%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:03:31 EST 2020

% Result     : Theorem 7.37s
% Output     : CNFRefutation 7.37s
% Verified   : 
% Statistics : Number of formulae       :  113 ( 552 expanded)
%              Number of leaves         :   32 ( 210 expanded)
%              Depth                    :   21
%              Number of atoms          :  178 ( 989 expanded)
%              Number of equality atoms :   70 ( 330 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > v1_funct_1 > k2_enumset1 > k1_enumset1 > k8_relat_1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1

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

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_83,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_69,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k7_relat_1(B,k3_xboole_0(k1_relat_1(B),A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t192_relat_1)).

tff(f_79,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k5_relat_1(k6_relat_1(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k8_relat_1(A,B) = k5_relat_1(B,k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_relat_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k8_relat_1(A,B) = k3_xboole_0(B,k2_zfmisc_1(k1_relat_1(B),A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t124_relat_1)).

tff(f_33,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_75,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k5_relat_1(k6_relat_1(A),B) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_43,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k3_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_relat_1)).

tff(f_65,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ! [C] :
              ( v1_relat_1(C)
             => k5_relat_1(k5_relat_1(A,B),C) = k5_relat_1(A,k5_relat_1(B,C)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_relat_1)).

tff(f_86,negated_conjecture,(
    ~ ! [A,B] : k5_relat_1(k6_relat_1(B),k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_funct_1)).

tff(c_34,plain,(
    ! [A_32] : v1_relat_1(k6_relat_1(A_32)) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_26,plain,(
    ! [A_27] : k1_relat_1(k6_relat_1(A_27)) = A_27 ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_283,plain,(
    ! [B_72,A_73] :
      ( k7_relat_1(B_72,k3_xboole_0(k1_relat_1(B_72),A_73)) = k7_relat_1(B_72,A_73)
      | ~ v1_relat_1(B_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_114,plain,(
    ! [A_53,B_54] :
      ( k5_relat_1(k6_relat_1(A_53),B_54) = k7_relat_1(B_54,A_53)
      | ~ v1_relat_1(B_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_18,plain,(
    ! [B_15,A_14] :
      ( k5_relat_1(B_15,k6_relat_1(A_14)) = k8_relat_1(A_14,B_15)
      | ~ v1_relat_1(B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_121,plain,(
    ! [A_14,A_53] :
      ( k8_relat_1(A_14,k6_relat_1(A_53)) = k7_relat_1(k6_relat_1(A_14),A_53)
      | ~ v1_relat_1(k6_relat_1(A_53))
      | ~ v1_relat_1(k6_relat_1(A_14)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_114,c_18])).

tff(c_134,plain,(
    ! [A_14,A_53] : k8_relat_1(A_14,k6_relat_1(A_53)) = k7_relat_1(k6_relat_1(A_14),A_53) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_34,c_121])).

tff(c_237,plain,(
    ! [B_64,A_65] :
      ( k3_xboole_0(B_64,k2_zfmisc_1(k1_relat_1(B_64),A_65)) = k8_relat_1(A_65,B_64)
      | ~ v1_relat_1(B_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_8,plain,(
    ! [A_3,B_4] : r1_tarski(k3_xboole_0(A_3,B_4),A_3) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_260,plain,(
    ! [A_66,B_67] :
      ( r1_tarski(k8_relat_1(A_66,B_67),B_67)
      | ~ v1_relat_1(B_67) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_237,c_8])).

tff(c_265,plain,(
    ! [A_14,A_53] :
      ( r1_tarski(k7_relat_1(k6_relat_1(A_14),A_53),k6_relat_1(A_53))
      | ~ v1_relat_1(k6_relat_1(A_53)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_134,c_260])).

tff(c_268,plain,(
    ! [A_14,A_53] : r1_tarski(k7_relat_1(k6_relat_1(A_14),A_53),k6_relat_1(A_53)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_265])).

tff(c_290,plain,(
    ! [A_14,A_73] :
      ( r1_tarski(k7_relat_1(k6_relat_1(A_14),A_73),k6_relat_1(k3_xboole_0(k1_relat_1(k6_relat_1(A_14)),A_73)))
      | ~ v1_relat_1(k6_relat_1(A_14)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_283,c_268])).

tff(c_303,plain,(
    ! [A_14,A_73] : r1_tarski(k7_relat_1(k6_relat_1(A_14),A_73),k6_relat_1(k3_xboole_0(A_14,A_73))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_26,c_290])).

tff(c_300,plain,(
    ! [A_27,A_73] :
      ( k7_relat_1(k6_relat_1(A_27),k3_xboole_0(A_27,A_73)) = k7_relat_1(k6_relat_1(A_27),A_73)
      | ~ v1_relat_1(k6_relat_1(A_27)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_283])).

tff(c_306,plain,(
    ! [A_27,A_73] : k7_relat_1(k6_relat_1(A_27),k3_xboole_0(A_27,A_73)) = k7_relat_1(k6_relat_1(A_27),A_73) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_300])).

tff(c_140,plain,(
    ! [A_55,B_56] :
      ( k5_relat_1(k6_relat_1(A_55),B_56) = B_56
      | ~ r1_tarski(k1_relat_1(B_56),A_55)
      | ~ v1_relat_1(B_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_143,plain,(
    ! [A_55,A_27] :
      ( k5_relat_1(k6_relat_1(A_55),k6_relat_1(A_27)) = k6_relat_1(A_27)
      | ~ r1_tarski(A_27,A_55)
      | ~ v1_relat_1(k6_relat_1(A_27)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_140])).

tff(c_417,plain,(
    ! [A_83,A_84] :
      ( k5_relat_1(k6_relat_1(A_83),k6_relat_1(A_84)) = k6_relat_1(A_84)
      | ~ r1_tarski(A_84,A_83) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_143])).

tff(c_32,plain,(
    ! [A_30,B_31] :
      ( k5_relat_1(k6_relat_1(A_30),B_31) = k7_relat_1(B_31,A_30)
      | ~ v1_relat_1(B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_434,plain,(
    ! [A_84,A_83] :
      ( k7_relat_1(k6_relat_1(A_84),A_83) = k6_relat_1(A_84)
      | ~ v1_relat_1(k6_relat_1(A_84))
      | ~ r1_tarski(A_84,A_83) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_417,c_32])).

tff(c_483,plain,(
    ! [A_85,A_86] :
      ( k7_relat_1(k6_relat_1(A_85),A_86) = k6_relat_1(A_85)
      | ~ r1_tarski(A_85,A_86) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_434])).

tff(c_489,plain,(
    ! [A_85,A_86] :
      ( r1_tarski(k6_relat_1(A_85),k6_relat_1(k3_xboole_0(A_85,A_86)))
      | ~ r1_tarski(A_85,A_86) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_483,c_303])).

tff(c_544,plain,(
    ! [A_87,A_88] :
      ( r1_tarski(k6_relat_1(A_87),k6_relat_1(A_88))
      | ~ r1_tarski(A_87,A_88) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_483,c_268])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_743,plain,(
    ! [A_106,A_105] :
      ( k6_relat_1(A_106) = k6_relat_1(A_105)
      | ~ r1_tarski(k6_relat_1(A_105),k6_relat_1(A_106))
      | ~ r1_tarski(A_106,A_105) ) ),
    inference(resolution,[status(thm)],[c_544,c_2])).

tff(c_749,plain,(
    ! [A_85,A_86] :
      ( k6_relat_1(k3_xboole_0(A_85,A_86)) = k6_relat_1(A_85)
      | ~ r1_tarski(k3_xboole_0(A_85,A_86),A_85)
      | ~ r1_tarski(A_85,A_86) ) ),
    inference(resolution,[status(thm)],[c_489,c_743])).

tff(c_1025,plain,(
    ! [A_112,A_113] :
      ( k6_relat_1(k3_xboole_0(A_112,A_113)) = k6_relat_1(A_112)
      | ~ r1_tarski(A_112,A_113) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_749])).

tff(c_1108,plain,(
    ! [A_112,A_113] :
      ( k3_xboole_0(A_112,A_113) = k1_relat_1(k6_relat_1(A_112))
      | ~ r1_tarski(A_112,A_113) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1025,c_26])).

tff(c_1142,plain,(
    ! [A_114,A_115] :
      ( k3_xboole_0(A_114,A_115) = A_114
      | ~ r1_tarski(A_114,A_115) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_1108])).

tff(c_1173,plain,(
    ! [A_3,B_4] : k3_xboole_0(k3_xboole_0(A_3,B_4),A_3) = k3_xboole_0(A_3,B_4) ),
    inference(resolution,[status(thm)],[c_8,c_1142])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_161,plain,(
    ! [B_59] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(B_59)),B_59) = B_59
      | ~ v1_relat_1(B_59) ) ),
    inference(resolution,[status(thm)],[c_6,c_140])).

tff(c_171,plain,(
    ! [A_14] :
      ( k8_relat_1(A_14,k6_relat_1(k1_relat_1(k6_relat_1(A_14)))) = k6_relat_1(A_14)
      | ~ v1_relat_1(k6_relat_1(k1_relat_1(k6_relat_1(A_14))))
      | ~ v1_relat_1(k6_relat_1(A_14)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_161,c_18])).

tff(c_188,plain,(
    ! [A_14] : k7_relat_1(k6_relat_1(A_14),A_14) = k6_relat_1(A_14) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_34,c_134,c_26,c_171])).

tff(c_1176,plain,(
    ! [A_116,B_117] : k3_xboole_0(k3_xboole_0(A_116,B_117),A_116) = k3_xboole_0(A_116,B_117) ),
    inference(resolution,[status(thm)],[c_8,c_1142])).

tff(c_1197,plain,(
    ! [A_116,B_117] : k7_relat_1(k6_relat_1(k3_xboole_0(A_116,B_117)),k3_xboole_0(A_116,B_117)) = k7_relat_1(k6_relat_1(k3_xboole_0(A_116,B_117)),A_116) ),
    inference(superposition,[status(thm),theory(equality)],[c_1176,c_306])).

tff(c_1235,plain,(
    ! [A_116,B_117] : k7_relat_1(k6_relat_1(k3_xboole_0(A_116,B_117)),A_116) = k6_relat_1(k3_xboole_0(A_116,B_117)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_188,c_1197])).

tff(c_22,plain,(
    ! [B_19,A_18] :
      ( k7_relat_1(B_19,k3_xboole_0(k1_relat_1(B_19),A_18)) = k7_relat_1(B_19,A_18)
      | ~ v1_relat_1(B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_16,plain,(
    ! [A_12,B_13] :
      ( v1_relat_1(k3_xboole_0(A_12,B_13))
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_277,plain,(
    ! [A_70,B_71] :
      ( v1_relat_1(k8_relat_1(A_70,B_71))
      | ~ v1_relat_1(B_71)
      | ~ v1_relat_1(B_71) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_237,c_16])).

tff(c_280,plain,(
    ! [A_14,A_53] :
      ( v1_relat_1(k7_relat_1(k6_relat_1(A_14),A_53))
      | ~ v1_relat_1(k6_relat_1(A_53))
      | ~ v1_relat_1(k6_relat_1(A_53)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_134,c_277])).

tff(c_282,plain,(
    ! [A_14,A_53] : v1_relat_1(k7_relat_1(k6_relat_1(A_14),A_53)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_34,c_280])).

tff(c_185,plain,(
    ! [A_27] :
      ( k5_relat_1(k6_relat_1(A_27),k6_relat_1(A_27)) = k6_relat_1(A_27)
      | ~ v1_relat_1(k6_relat_1(A_27)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_161])).

tff(c_193,plain,(
    ! [A_27] : k5_relat_1(k6_relat_1(A_27),k6_relat_1(A_27)) = k6_relat_1(A_27) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_185])).

tff(c_369,plain,(
    ! [A_80,B_81,C_82] :
      ( k5_relat_1(k5_relat_1(A_80,B_81),C_82) = k5_relat_1(A_80,k5_relat_1(B_81,C_82))
      | ~ v1_relat_1(C_82)
      | ~ v1_relat_1(B_81)
      | ~ v1_relat_1(A_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_394,plain,(
    ! [A_30,B_31,C_82] :
      ( k5_relat_1(k6_relat_1(A_30),k5_relat_1(B_31,C_82)) = k5_relat_1(k7_relat_1(B_31,A_30),C_82)
      | ~ v1_relat_1(C_82)
      | ~ v1_relat_1(B_31)
      | ~ v1_relat_1(k6_relat_1(A_30))
      | ~ v1_relat_1(B_31) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_369])).

tff(c_940,plain,(
    ! [A_109,B_110,C_111] :
      ( k5_relat_1(k6_relat_1(A_109),k5_relat_1(B_110,C_111)) = k5_relat_1(k7_relat_1(B_110,A_109),C_111)
      | ~ v1_relat_1(C_111)
      | ~ v1_relat_1(B_110) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_394])).

tff(c_985,plain,(
    ! [A_27,A_109] :
      ( k5_relat_1(k7_relat_1(k6_relat_1(A_27),A_109),k6_relat_1(A_27)) = k5_relat_1(k6_relat_1(A_109),k6_relat_1(A_27))
      | ~ v1_relat_1(k6_relat_1(A_27))
      | ~ v1_relat_1(k6_relat_1(A_27)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_193,c_940])).

tff(c_1018,plain,(
    ! [A_27,A_109] : k5_relat_1(k7_relat_1(k6_relat_1(A_27),A_109),k6_relat_1(A_27)) = k5_relat_1(k6_relat_1(A_109),k6_relat_1(A_27)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_34,c_985])).

tff(c_2739,plain,(
    ! [A_169,A_170] : k5_relat_1(k7_relat_1(k6_relat_1(A_169),A_170),k6_relat_1(A_169)) = k5_relat_1(k6_relat_1(A_170),k6_relat_1(A_169)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_34,c_985])).

tff(c_2790,plain,(
    ! [A_169,A_18] :
      ( k5_relat_1(k6_relat_1(k3_xboole_0(k1_relat_1(k6_relat_1(A_169)),A_18)),k6_relat_1(A_169)) = k5_relat_1(k7_relat_1(k6_relat_1(A_169),A_18),k6_relat_1(A_169))
      | ~ v1_relat_1(k6_relat_1(A_169)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_2739])).

tff(c_3246,plain,(
    ! [A_183,A_184] : k5_relat_1(k6_relat_1(k3_xboole_0(A_183,A_184)),k6_relat_1(A_183)) = k5_relat_1(k6_relat_1(A_184),k6_relat_1(A_183)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_1018,c_26,c_2790])).

tff(c_3278,plain,(
    ! [A_183,A_184] :
      ( k7_relat_1(k6_relat_1(A_183),k3_xboole_0(A_183,A_184)) = k5_relat_1(k6_relat_1(A_184),k6_relat_1(A_183))
      | ~ v1_relat_1(k6_relat_1(A_183)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3246,c_32])).

tff(c_3340,plain,(
    ! [A_184,A_183] : k5_relat_1(k6_relat_1(A_184),k6_relat_1(A_183)) = k7_relat_1(k6_relat_1(A_183),A_184) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_306,c_3278])).

tff(c_1002,plain,(
    ! [B_15,A_109,A_14] :
      ( k5_relat_1(k7_relat_1(B_15,A_109),k6_relat_1(A_14)) = k5_relat_1(k6_relat_1(A_109),k8_relat_1(A_14,B_15))
      | ~ v1_relat_1(k6_relat_1(A_14))
      | ~ v1_relat_1(B_15)
      | ~ v1_relat_1(B_15) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_940])).

tff(c_5592,plain,(
    ! [B_233,A_234,A_235] :
      ( k5_relat_1(k7_relat_1(B_233,A_234),k6_relat_1(A_235)) = k5_relat_1(k6_relat_1(A_234),k8_relat_1(A_235,B_233))
      | ~ v1_relat_1(B_233) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_1002])).

tff(c_5666,plain,(
    ! [A_14,A_235] :
      ( k5_relat_1(k6_relat_1(A_14),k8_relat_1(A_235,k6_relat_1(A_14))) = k5_relat_1(k6_relat_1(A_14),k6_relat_1(A_235))
      | ~ v1_relat_1(k6_relat_1(A_14)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_188,c_5592])).

tff(c_5701,plain,(
    ! [A_236,A_237] : k5_relat_1(k6_relat_1(A_236),k7_relat_1(k6_relat_1(A_237),A_236)) = k7_relat_1(k6_relat_1(A_237),A_236) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_3340,c_134,c_5666])).

tff(c_5722,plain,(
    ! [A_237,A_236] :
      ( k7_relat_1(k7_relat_1(k6_relat_1(A_237),A_236),A_236) = k7_relat_1(k6_relat_1(A_237),A_236)
      | ~ v1_relat_1(k7_relat_1(k6_relat_1(A_237),A_236)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5701,c_32])).

tff(c_5804,plain,(
    ! [A_238,A_239] : k7_relat_1(k7_relat_1(k6_relat_1(A_238),A_239),A_239) = k7_relat_1(k6_relat_1(A_238),A_239) ),
    inference(demodulation,[status(thm),theory(equality)],[c_282,c_5722])).

tff(c_5846,plain,(
    ! [A_238,A_18] :
      ( k7_relat_1(k7_relat_1(k6_relat_1(A_238),A_18),k3_xboole_0(k1_relat_1(k6_relat_1(A_238)),A_18)) = k7_relat_1(k6_relat_1(A_238),k3_xboole_0(k1_relat_1(k6_relat_1(A_238)),A_18))
      | ~ v1_relat_1(k6_relat_1(A_238)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_5804])).

tff(c_5866,plain,(
    ! [A_238,A_18] : k7_relat_1(k7_relat_1(k6_relat_1(A_238),A_18),k3_xboole_0(A_238,A_18)) = k7_relat_1(k6_relat_1(A_238),A_18) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_306,c_26,c_26,c_5846])).

tff(c_995,plain,(
    ! [A_30,A_109,B_31] :
      ( k5_relat_1(k7_relat_1(k6_relat_1(A_30),A_109),B_31) = k5_relat_1(k6_relat_1(A_109),k7_relat_1(B_31,A_30))
      | ~ v1_relat_1(B_31)
      | ~ v1_relat_1(k6_relat_1(A_30))
      | ~ v1_relat_1(B_31) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_940])).

tff(c_4608,plain,(
    ! [A_211,A_212,B_213] :
      ( k5_relat_1(k7_relat_1(k6_relat_1(A_211),A_212),B_213) = k5_relat_1(k6_relat_1(A_212),k7_relat_1(B_213,A_211))
      | ~ v1_relat_1(B_213) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_995])).

tff(c_4648,plain,(
    ! [A_212,A_14,A_211] :
      ( k5_relat_1(k6_relat_1(A_212),k7_relat_1(k6_relat_1(A_14),A_211)) = k8_relat_1(A_14,k7_relat_1(k6_relat_1(A_211),A_212))
      | ~ v1_relat_1(k7_relat_1(k6_relat_1(A_211),A_212))
      | ~ v1_relat_1(k6_relat_1(A_14)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4608,c_18])).

tff(c_9622,plain,(
    ! [A_298,A_299,A_300] : k5_relat_1(k6_relat_1(A_298),k7_relat_1(k6_relat_1(A_299),A_300)) = k8_relat_1(A_299,k7_relat_1(k6_relat_1(A_300),A_298)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_282,c_4648])).

tff(c_9655,plain,(
    ! [A_299,A_300,A_298] :
      ( k8_relat_1(A_299,k7_relat_1(k6_relat_1(A_300),A_298)) = k7_relat_1(k7_relat_1(k6_relat_1(A_299),A_300),A_298)
      | ~ v1_relat_1(k7_relat_1(k6_relat_1(A_299),A_300)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_9622,c_32])).

tff(c_9797,plain,(
    ! [A_301,A_302,A_303] : k8_relat_1(A_301,k7_relat_1(k6_relat_1(A_302),A_303)) = k7_relat_1(k7_relat_1(k6_relat_1(A_301),A_302),A_303) ),
    inference(demodulation,[status(thm),theory(equality)],[c_282,c_9655])).

tff(c_249,plain,(
    ! [A_65,B_64] :
      ( r1_tarski(k8_relat_1(A_65,B_64),B_64)
      | ~ v1_relat_1(B_64) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_237,c_8])).

tff(c_9863,plain,(
    ! [A_301,A_302,A_303] :
      ( r1_tarski(k7_relat_1(k7_relat_1(k6_relat_1(A_301),A_302),A_303),k7_relat_1(k6_relat_1(A_302),A_303))
      | ~ v1_relat_1(k7_relat_1(k6_relat_1(A_302),A_303)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_9797,c_249])).

tff(c_10088,plain,(
    ! [A_307,A_308,A_309] : r1_tarski(k7_relat_1(k7_relat_1(k6_relat_1(A_307),A_308),A_309),k7_relat_1(k6_relat_1(A_308),A_309)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_282,c_9863])).

tff(c_10772,plain,(
    ! [A_324,A_325] : r1_tarski(k7_relat_1(k6_relat_1(A_324),A_325),k7_relat_1(k6_relat_1(A_325),k3_xboole_0(A_324,A_325))) ),
    inference(superposition,[status(thm),theory(equality)],[c_5866,c_10088])).

tff(c_10854,plain,(
    ! [A_116,B_117] : r1_tarski(k6_relat_1(k3_xboole_0(A_116,B_117)),k7_relat_1(k6_relat_1(A_116),k3_xboole_0(k3_xboole_0(A_116,B_117),A_116))) ),
    inference(superposition,[status(thm),theory(equality)],[c_1235,c_10772])).

tff(c_10934,plain,(
    ! [A_326,B_327] : r1_tarski(k6_relat_1(k3_xboole_0(A_326,B_327)),k7_relat_1(k6_relat_1(A_326),B_327)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_306,c_1173,c_10854])).

tff(c_10941,plain,(
    ! [A_326,B_327] :
      ( k7_relat_1(k6_relat_1(A_326),B_327) = k6_relat_1(k3_xboole_0(A_326,B_327))
      | ~ r1_tarski(k7_relat_1(k6_relat_1(A_326),B_327),k6_relat_1(k3_xboole_0(A_326,B_327))) ) ),
    inference(resolution,[status(thm)],[c_10934,c_2])).

tff(c_11057,plain,(
    ! [A_326,B_327] : k7_relat_1(k6_relat_1(A_326),B_327) = k6_relat_1(k3_xboole_0(A_326,B_327)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_303,c_10941])).

tff(c_38,plain,(
    k5_relat_1(k6_relat_1('#skF_2'),k6_relat_1('#skF_1')) != k6_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_124,plain,
    ( k7_relat_1(k6_relat_1('#skF_1'),'#skF_2') != k6_relat_1(k3_xboole_0('#skF_1','#skF_2'))
    | ~ v1_relat_1(k6_relat_1('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_114,c_38])).

tff(c_136,plain,(
    k7_relat_1(k6_relat_1('#skF_1'),'#skF_2') != k6_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_124])).

tff(c_11132,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_11057,c_136])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n022.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 12:43:11 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.37/2.61  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.37/2.62  
% 7.37/2.62  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.37/2.63  %$ r1_tarski > v1_relat_1 > v1_funct_1 > k2_enumset1 > k1_enumset1 > k8_relat_1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1
% 7.37/2.63  
% 7.37/2.63  %Foreground sorts:
% 7.37/2.63  
% 7.37/2.63  
% 7.37/2.63  %Background operators:
% 7.37/2.63  
% 7.37/2.63  
% 7.37/2.63  %Foreground operators:
% 7.37/2.63  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 7.37/2.63  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 7.37/2.63  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.37/2.63  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 7.37/2.63  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 7.37/2.63  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.37/2.63  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 7.37/2.63  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 7.37/2.63  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 7.37/2.63  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 7.37/2.63  tff('#skF_2', type, '#skF_2': $i).
% 7.37/2.63  tff('#skF_1', type, '#skF_1': $i).
% 7.37/2.63  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.37/2.63  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 7.37/2.63  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 7.37/2.63  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 7.37/2.63  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.37/2.63  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 7.37/2.63  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 7.37/2.63  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 7.37/2.63  
% 7.37/2.65  tff(f_83, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc3_funct_1)).
% 7.37/2.65  tff(f_69, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 7.37/2.65  tff(f_55, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k7_relat_1(B, k3_xboole_0(k1_relat_1(B), A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t192_relat_1)).
% 7.37/2.65  tff(f_79, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_relat_1)).
% 7.37/2.65  tff(f_47, axiom, (![A, B]: (v1_relat_1(B) => (k8_relat_1(A, B) = k5_relat_1(B, k6_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t123_relat_1)).
% 7.37/2.65  tff(f_51, axiom, (![A, B]: (v1_relat_1(B) => (k8_relat_1(A, B) = k3_xboole_0(B, k2_zfmisc_1(k1_relat_1(B), A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t124_relat_1)).
% 7.37/2.65  tff(f_33, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 7.37/2.65  tff(f_75, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k5_relat_1(k6_relat_1(A), B) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t77_relat_1)).
% 7.37/2.65  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 7.37/2.65  tff(f_43, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_relat_1)).
% 7.37/2.65  tff(f_65, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (k5_relat_1(k5_relat_1(A, B), C) = k5_relat_1(A, k5_relat_1(B, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_relat_1)).
% 7.37/2.65  tff(f_86, negated_conjecture, ~(![A, B]: (k5_relat_1(k6_relat_1(B), k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_funct_1)).
% 7.37/2.65  tff(c_34, plain, (![A_32]: (v1_relat_1(k6_relat_1(A_32)))), inference(cnfTransformation, [status(thm)], [f_83])).
% 7.37/2.65  tff(c_26, plain, (![A_27]: (k1_relat_1(k6_relat_1(A_27))=A_27)), inference(cnfTransformation, [status(thm)], [f_69])).
% 7.37/2.65  tff(c_283, plain, (![B_72, A_73]: (k7_relat_1(B_72, k3_xboole_0(k1_relat_1(B_72), A_73))=k7_relat_1(B_72, A_73) | ~v1_relat_1(B_72))), inference(cnfTransformation, [status(thm)], [f_55])).
% 7.37/2.65  tff(c_114, plain, (![A_53, B_54]: (k5_relat_1(k6_relat_1(A_53), B_54)=k7_relat_1(B_54, A_53) | ~v1_relat_1(B_54))), inference(cnfTransformation, [status(thm)], [f_79])).
% 7.37/2.65  tff(c_18, plain, (![B_15, A_14]: (k5_relat_1(B_15, k6_relat_1(A_14))=k8_relat_1(A_14, B_15) | ~v1_relat_1(B_15))), inference(cnfTransformation, [status(thm)], [f_47])).
% 7.37/2.65  tff(c_121, plain, (![A_14, A_53]: (k8_relat_1(A_14, k6_relat_1(A_53))=k7_relat_1(k6_relat_1(A_14), A_53) | ~v1_relat_1(k6_relat_1(A_53)) | ~v1_relat_1(k6_relat_1(A_14)))), inference(superposition, [status(thm), theory('equality')], [c_114, c_18])).
% 7.37/2.65  tff(c_134, plain, (![A_14, A_53]: (k8_relat_1(A_14, k6_relat_1(A_53))=k7_relat_1(k6_relat_1(A_14), A_53))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_34, c_121])).
% 7.37/2.65  tff(c_237, plain, (![B_64, A_65]: (k3_xboole_0(B_64, k2_zfmisc_1(k1_relat_1(B_64), A_65))=k8_relat_1(A_65, B_64) | ~v1_relat_1(B_64))), inference(cnfTransformation, [status(thm)], [f_51])).
% 7.37/2.65  tff(c_8, plain, (![A_3, B_4]: (r1_tarski(k3_xboole_0(A_3, B_4), A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 7.37/2.65  tff(c_260, plain, (![A_66, B_67]: (r1_tarski(k8_relat_1(A_66, B_67), B_67) | ~v1_relat_1(B_67))), inference(superposition, [status(thm), theory('equality')], [c_237, c_8])).
% 7.37/2.65  tff(c_265, plain, (![A_14, A_53]: (r1_tarski(k7_relat_1(k6_relat_1(A_14), A_53), k6_relat_1(A_53)) | ~v1_relat_1(k6_relat_1(A_53)))), inference(superposition, [status(thm), theory('equality')], [c_134, c_260])).
% 7.37/2.65  tff(c_268, plain, (![A_14, A_53]: (r1_tarski(k7_relat_1(k6_relat_1(A_14), A_53), k6_relat_1(A_53)))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_265])).
% 7.37/2.65  tff(c_290, plain, (![A_14, A_73]: (r1_tarski(k7_relat_1(k6_relat_1(A_14), A_73), k6_relat_1(k3_xboole_0(k1_relat_1(k6_relat_1(A_14)), A_73))) | ~v1_relat_1(k6_relat_1(A_14)))), inference(superposition, [status(thm), theory('equality')], [c_283, c_268])).
% 7.37/2.65  tff(c_303, plain, (![A_14, A_73]: (r1_tarski(k7_relat_1(k6_relat_1(A_14), A_73), k6_relat_1(k3_xboole_0(A_14, A_73))))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_26, c_290])).
% 7.37/2.65  tff(c_300, plain, (![A_27, A_73]: (k7_relat_1(k6_relat_1(A_27), k3_xboole_0(A_27, A_73))=k7_relat_1(k6_relat_1(A_27), A_73) | ~v1_relat_1(k6_relat_1(A_27)))), inference(superposition, [status(thm), theory('equality')], [c_26, c_283])).
% 7.37/2.65  tff(c_306, plain, (![A_27, A_73]: (k7_relat_1(k6_relat_1(A_27), k3_xboole_0(A_27, A_73))=k7_relat_1(k6_relat_1(A_27), A_73))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_300])).
% 7.37/2.65  tff(c_140, plain, (![A_55, B_56]: (k5_relat_1(k6_relat_1(A_55), B_56)=B_56 | ~r1_tarski(k1_relat_1(B_56), A_55) | ~v1_relat_1(B_56))), inference(cnfTransformation, [status(thm)], [f_75])).
% 7.37/2.65  tff(c_143, plain, (![A_55, A_27]: (k5_relat_1(k6_relat_1(A_55), k6_relat_1(A_27))=k6_relat_1(A_27) | ~r1_tarski(A_27, A_55) | ~v1_relat_1(k6_relat_1(A_27)))), inference(superposition, [status(thm), theory('equality')], [c_26, c_140])).
% 7.37/2.65  tff(c_417, plain, (![A_83, A_84]: (k5_relat_1(k6_relat_1(A_83), k6_relat_1(A_84))=k6_relat_1(A_84) | ~r1_tarski(A_84, A_83))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_143])).
% 7.37/2.65  tff(c_32, plain, (![A_30, B_31]: (k5_relat_1(k6_relat_1(A_30), B_31)=k7_relat_1(B_31, A_30) | ~v1_relat_1(B_31))), inference(cnfTransformation, [status(thm)], [f_79])).
% 7.37/2.65  tff(c_434, plain, (![A_84, A_83]: (k7_relat_1(k6_relat_1(A_84), A_83)=k6_relat_1(A_84) | ~v1_relat_1(k6_relat_1(A_84)) | ~r1_tarski(A_84, A_83))), inference(superposition, [status(thm), theory('equality')], [c_417, c_32])).
% 7.37/2.65  tff(c_483, plain, (![A_85, A_86]: (k7_relat_1(k6_relat_1(A_85), A_86)=k6_relat_1(A_85) | ~r1_tarski(A_85, A_86))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_434])).
% 7.37/2.65  tff(c_489, plain, (![A_85, A_86]: (r1_tarski(k6_relat_1(A_85), k6_relat_1(k3_xboole_0(A_85, A_86))) | ~r1_tarski(A_85, A_86))), inference(superposition, [status(thm), theory('equality')], [c_483, c_303])).
% 7.37/2.65  tff(c_544, plain, (![A_87, A_88]: (r1_tarski(k6_relat_1(A_87), k6_relat_1(A_88)) | ~r1_tarski(A_87, A_88))), inference(superposition, [status(thm), theory('equality')], [c_483, c_268])).
% 7.37/2.65  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.37/2.65  tff(c_743, plain, (![A_106, A_105]: (k6_relat_1(A_106)=k6_relat_1(A_105) | ~r1_tarski(k6_relat_1(A_105), k6_relat_1(A_106)) | ~r1_tarski(A_106, A_105))), inference(resolution, [status(thm)], [c_544, c_2])).
% 7.37/2.65  tff(c_749, plain, (![A_85, A_86]: (k6_relat_1(k3_xboole_0(A_85, A_86))=k6_relat_1(A_85) | ~r1_tarski(k3_xboole_0(A_85, A_86), A_85) | ~r1_tarski(A_85, A_86))), inference(resolution, [status(thm)], [c_489, c_743])).
% 7.37/2.65  tff(c_1025, plain, (![A_112, A_113]: (k6_relat_1(k3_xboole_0(A_112, A_113))=k6_relat_1(A_112) | ~r1_tarski(A_112, A_113))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_749])).
% 7.37/2.65  tff(c_1108, plain, (![A_112, A_113]: (k3_xboole_0(A_112, A_113)=k1_relat_1(k6_relat_1(A_112)) | ~r1_tarski(A_112, A_113))), inference(superposition, [status(thm), theory('equality')], [c_1025, c_26])).
% 7.37/2.65  tff(c_1142, plain, (![A_114, A_115]: (k3_xboole_0(A_114, A_115)=A_114 | ~r1_tarski(A_114, A_115))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_1108])).
% 7.37/2.65  tff(c_1173, plain, (![A_3, B_4]: (k3_xboole_0(k3_xboole_0(A_3, B_4), A_3)=k3_xboole_0(A_3, B_4))), inference(resolution, [status(thm)], [c_8, c_1142])).
% 7.37/2.65  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.37/2.65  tff(c_161, plain, (![B_59]: (k5_relat_1(k6_relat_1(k1_relat_1(B_59)), B_59)=B_59 | ~v1_relat_1(B_59))), inference(resolution, [status(thm)], [c_6, c_140])).
% 7.37/2.65  tff(c_171, plain, (![A_14]: (k8_relat_1(A_14, k6_relat_1(k1_relat_1(k6_relat_1(A_14))))=k6_relat_1(A_14) | ~v1_relat_1(k6_relat_1(k1_relat_1(k6_relat_1(A_14)))) | ~v1_relat_1(k6_relat_1(A_14)))), inference(superposition, [status(thm), theory('equality')], [c_161, c_18])).
% 7.37/2.65  tff(c_188, plain, (![A_14]: (k7_relat_1(k6_relat_1(A_14), A_14)=k6_relat_1(A_14))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_34, c_134, c_26, c_171])).
% 7.37/2.65  tff(c_1176, plain, (![A_116, B_117]: (k3_xboole_0(k3_xboole_0(A_116, B_117), A_116)=k3_xboole_0(A_116, B_117))), inference(resolution, [status(thm)], [c_8, c_1142])).
% 7.37/2.65  tff(c_1197, plain, (![A_116, B_117]: (k7_relat_1(k6_relat_1(k3_xboole_0(A_116, B_117)), k3_xboole_0(A_116, B_117))=k7_relat_1(k6_relat_1(k3_xboole_0(A_116, B_117)), A_116))), inference(superposition, [status(thm), theory('equality')], [c_1176, c_306])).
% 7.37/2.65  tff(c_1235, plain, (![A_116, B_117]: (k7_relat_1(k6_relat_1(k3_xboole_0(A_116, B_117)), A_116)=k6_relat_1(k3_xboole_0(A_116, B_117)))), inference(demodulation, [status(thm), theory('equality')], [c_188, c_1197])).
% 7.37/2.65  tff(c_22, plain, (![B_19, A_18]: (k7_relat_1(B_19, k3_xboole_0(k1_relat_1(B_19), A_18))=k7_relat_1(B_19, A_18) | ~v1_relat_1(B_19))), inference(cnfTransformation, [status(thm)], [f_55])).
% 7.37/2.65  tff(c_16, plain, (![A_12, B_13]: (v1_relat_1(k3_xboole_0(A_12, B_13)) | ~v1_relat_1(A_12))), inference(cnfTransformation, [status(thm)], [f_43])).
% 7.37/2.65  tff(c_277, plain, (![A_70, B_71]: (v1_relat_1(k8_relat_1(A_70, B_71)) | ~v1_relat_1(B_71) | ~v1_relat_1(B_71))), inference(superposition, [status(thm), theory('equality')], [c_237, c_16])).
% 7.37/2.65  tff(c_280, plain, (![A_14, A_53]: (v1_relat_1(k7_relat_1(k6_relat_1(A_14), A_53)) | ~v1_relat_1(k6_relat_1(A_53)) | ~v1_relat_1(k6_relat_1(A_53)))), inference(superposition, [status(thm), theory('equality')], [c_134, c_277])).
% 7.37/2.65  tff(c_282, plain, (![A_14, A_53]: (v1_relat_1(k7_relat_1(k6_relat_1(A_14), A_53)))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_34, c_280])).
% 7.37/2.65  tff(c_185, plain, (![A_27]: (k5_relat_1(k6_relat_1(A_27), k6_relat_1(A_27))=k6_relat_1(A_27) | ~v1_relat_1(k6_relat_1(A_27)))), inference(superposition, [status(thm), theory('equality')], [c_26, c_161])).
% 7.37/2.65  tff(c_193, plain, (![A_27]: (k5_relat_1(k6_relat_1(A_27), k6_relat_1(A_27))=k6_relat_1(A_27))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_185])).
% 7.37/2.65  tff(c_369, plain, (![A_80, B_81, C_82]: (k5_relat_1(k5_relat_1(A_80, B_81), C_82)=k5_relat_1(A_80, k5_relat_1(B_81, C_82)) | ~v1_relat_1(C_82) | ~v1_relat_1(B_81) | ~v1_relat_1(A_80))), inference(cnfTransformation, [status(thm)], [f_65])).
% 7.37/2.65  tff(c_394, plain, (![A_30, B_31, C_82]: (k5_relat_1(k6_relat_1(A_30), k5_relat_1(B_31, C_82))=k5_relat_1(k7_relat_1(B_31, A_30), C_82) | ~v1_relat_1(C_82) | ~v1_relat_1(B_31) | ~v1_relat_1(k6_relat_1(A_30)) | ~v1_relat_1(B_31))), inference(superposition, [status(thm), theory('equality')], [c_32, c_369])).
% 7.37/2.65  tff(c_940, plain, (![A_109, B_110, C_111]: (k5_relat_1(k6_relat_1(A_109), k5_relat_1(B_110, C_111))=k5_relat_1(k7_relat_1(B_110, A_109), C_111) | ~v1_relat_1(C_111) | ~v1_relat_1(B_110))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_394])).
% 7.37/2.65  tff(c_985, plain, (![A_27, A_109]: (k5_relat_1(k7_relat_1(k6_relat_1(A_27), A_109), k6_relat_1(A_27))=k5_relat_1(k6_relat_1(A_109), k6_relat_1(A_27)) | ~v1_relat_1(k6_relat_1(A_27)) | ~v1_relat_1(k6_relat_1(A_27)))), inference(superposition, [status(thm), theory('equality')], [c_193, c_940])).
% 7.37/2.65  tff(c_1018, plain, (![A_27, A_109]: (k5_relat_1(k7_relat_1(k6_relat_1(A_27), A_109), k6_relat_1(A_27))=k5_relat_1(k6_relat_1(A_109), k6_relat_1(A_27)))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_34, c_985])).
% 7.37/2.65  tff(c_2739, plain, (![A_169, A_170]: (k5_relat_1(k7_relat_1(k6_relat_1(A_169), A_170), k6_relat_1(A_169))=k5_relat_1(k6_relat_1(A_170), k6_relat_1(A_169)))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_34, c_985])).
% 7.37/2.65  tff(c_2790, plain, (![A_169, A_18]: (k5_relat_1(k6_relat_1(k3_xboole_0(k1_relat_1(k6_relat_1(A_169)), A_18)), k6_relat_1(A_169))=k5_relat_1(k7_relat_1(k6_relat_1(A_169), A_18), k6_relat_1(A_169)) | ~v1_relat_1(k6_relat_1(A_169)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_2739])).
% 7.37/2.65  tff(c_3246, plain, (![A_183, A_184]: (k5_relat_1(k6_relat_1(k3_xboole_0(A_183, A_184)), k6_relat_1(A_183))=k5_relat_1(k6_relat_1(A_184), k6_relat_1(A_183)))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_1018, c_26, c_2790])).
% 7.37/2.65  tff(c_3278, plain, (![A_183, A_184]: (k7_relat_1(k6_relat_1(A_183), k3_xboole_0(A_183, A_184))=k5_relat_1(k6_relat_1(A_184), k6_relat_1(A_183)) | ~v1_relat_1(k6_relat_1(A_183)))), inference(superposition, [status(thm), theory('equality')], [c_3246, c_32])).
% 7.37/2.65  tff(c_3340, plain, (![A_184, A_183]: (k5_relat_1(k6_relat_1(A_184), k6_relat_1(A_183))=k7_relat_1(k6_relat_1(A_183), A_184))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_306, c_3278])).
% 7.37/2.65  tff(c_1002, plain, (![B_15, A_109, A_14]: (k5_relat_1(k7_relat_1(B_15, A_109), k6_relat_1(A_14))=k5_relat_1(k6_relat_1(A_109), k8_relat_1(A_14, B_15)) | ~v1_relat_1(k6_relat_1(A_14)) | ~v1_relat_1(B_15) | ~v1_relat_1(B_15))), inference(superposition, [status(thm), theory('equality')], [c_18, c_940])).
% 7.37/2.65  tff(c_5592, plain, (![B_233, A_234, A_235]: (k5_relat_1(k7_relat_1(B_233, A_234), k6_relat_1(A_235))=k5_relat_1(k6_relat_1(A_234), k8_relat_1(A_235, B_233)) | ~v1_relat_1(B_233))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_1002])).
% 7.37/2.65  tff(c_5666, plain, (![A_14, A_235]: (k5_relat_1(k6_relat_1(A_14), k8_relat_1(A_235, k6_relat_1(A_14)))=k5_relat_1(k6_relat_1(A_14), k6_relat_1(A_235)) | ~v1_relat_1(k6_relat_1(A_14)))), inference(superposition, [status(thm), theory('equality')], [c_188, c_5592])).
% 7.37/2.65  tff(c_5701, plain, (![A_236, A_237]: (k5_relat_1(k6_relat_1(A_236), k7_relat_1(k6_relat_1(A_237), A_236))=k7_relat_1(k6_relat_1(A_237), A_236))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_3340, c_134, c_5666])).
% 7.37/2.65  tff(c_5722, plain, (![A_237, A_236]: (k7_relat_1(k7_relat_1(k6_relat_1(A_237), A_236), A_236)=k7_relat_1(k6_relat_1(A_237), A_236) | ~v1_relat_1(k7_relat_1(k6_relat_1(A_237), A_236)))), inference(superposition, [status(thm), theory('equality')], [c_5701, c_32])).
% 7.37/2.65  tff(c_5804, plain, (![A_238, A_239]: (k7_relat_1(k7_relat_1(k6_relat_1(A_238), A_239), A_239)=k7_relat_1(k6_relat_1(A_238), A_239))), inference(demodulation, [status(thm), theory('equality')], [c_282, c_5722])).
% 7.37/2.65  tff(c_5846, plain, (![A_238, A_18]: (k7_relat_1(k7_relat_1(k6_relat_1(A_238), A_18), k3_xboole_0(k1_relat_1(k6_relat_1(A_238)), A_18))=k7_relat_1(k6_relat_1(A_238), k3_xboole_0(k1_relat_1(k6_relat_1(A_238)), A_18)) | ~v1_relat_1(k6_relat_1(A_238)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_5804])).
% 7.37/2.65  tff(c_5866, plain, (![A_238, A_18]: (k7_relat_1(k7_relat_1(k6_relat_1(A_238), A_18), k3_xboole_0(A_238, A_18))=k7_relat_1(k6_relat_1(A_238), A_18))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_306, c_26, c_26, c_5846])).
% 7.37/2.65  tff(c_995, plain, (![A_30, A_109, B_31]: (k5_relat_1(k7_relat_1(k6_relat_1(A_30), A_109), B_31)=k5_relat_1(k6_relat_1(A_109), k7_relat_1(B_31, A_30)) | ~v1_relat_1(B_31) | ~v1_relat_1(k6_relat_1(A_30)) | ~v1_relat_1(B_31))), inference(superposition, [status(thm), theory('equality')], [c_32, c_940])).
% 7.37/2.65  tff(c_4608, plain, (![A_211, A_212, B_213]: (k5_relat_1(k7_relat_1(k6_relat_1(A_211), A_212), B_213)=k5_relat_1(k6_relat_1(A_212), k7_relat_1(B_213, A_211)) | ~v1_relat_1(B_213))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_995])).
% 7.37/2.65  tff(c_4648, plain, (![A_212, A_14, A_211]: (k5_relat_1(k6_relat_1(A_212), k7_relat_1(k6_relat_1(A_14), A_211))=k8_relat_1(A_14, k7_relat_1(k6_relat_1(A_211), A_212)) | ~v1_relat_1(k7_relat_1(k6_relat_1(A_211), A_212)) | ~v1_relat_1(k6_relat_1(A_14)))), inference(superposition, [status(thm), theory('equality')], [c_4608, c_18])).
% 7.37/2.65  tff(c_9622, plain, (![A_298, A_299, A_300]: (k5_relat_1(k6_relat_1(A_298), k7_relat_1(k6_relat_1(A_299), A_300))=k8_relat_1(A_299, k7_relat_1(k6_relat_1(A_300), A_298)))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_282, c_4648])).
% 7.37/2.65  tff(c_9655, plain, (![A_299, A_300, A_298]: (k8_relat_1(A_299, k7_relat_1(k6_relat_1(A_300), A_298))=k7_relat_1(k7_relat_1(k6_relat_1(A_299), A_300), A_298) | ~v1_relat_1(k7_relat_1(k6_relat_1(A_299), A_300)))), inference(superposition, [status(thm), theory('equality')], [c_9622, c_32])).
% 7.37/2.65  tff(c_9797, plain, (![A_301, A_302, A_303]: (k8_relat_1(A_301, k7_relat_1(k6_relat_1(A_302), A_303))=k7_relat_1(k7_relat_1(k6_relat_1(A_301), A_302), A_303))), inference(demodulation, [status(thm), theory('equality')], [c_282, c_9655])).
% 7.37/2.65  tff(c_249, plain, (![A_65, B_64]: (r1_tarski(k8_relat_1(A_65, B_64), B_64) | ~v1_relat_1(B_64))), inference(superposition, [status(thm), theory('equality')], [c_237, c_8])).
% 7.37/2.65  tff(c_9863, plain, (![A_301, A_302, A_303]: (r1_tarski(k7_relat_1(k7_relat_1(k6_relat_1(A_301), A_302), A_303), k7_relat_1(k6_relat_1(A_302), A_303)) | ~v1_relat_1(k7_relat_1(k6_relat_1(A_302), A_303)))), inference(superposition, [status(thm), theory('equality')], [c_9797, c_249])).
% 7.37/2.65  tff(c_10088, plain, (![A_307, A_308, A_309]: (r1_tarski(k7_relat_1(k7_relat_1(k6_relat_1(A_307), A_308), A_309), k7_relat_1(k6_relat_1(A_308), A_309)))), inference(demodulation, [status(thm), theory('equality')], [c_282, c_9863])).
% 7.37/2.65  tff(c_10772, plain, (![A_324, A_325]: (r1_tarski(k7_relat_1(k6_relat_1(A_324), A_325), k7_relat_1(k6_relat_1(A_325), k3_xboole_0(A_324, A_325))))), inference(superposition, [status(thm), theory('equality')], [c_5866, c_10088])).
% 7.37/2.65  tff(c_10854, plain, (![A_116, B_117]: (r1_tarski(k6_relat_1(k3_xboole_0(A_116, B_117)), k7_relat_1(k6_relat_1(A_116), k3_xboole_0(k3_xboole_0(A_116, B_117), A_116))))), inference(superposition, [status(thm), theory('equality')], [c_1235, c_10772])).
% 7.37/2.65  tff(c_10934, plain, (![A_326, B_327]: (r1_tarski(k6_relat_1(k3_xboole_0(A_326, B_327)), k7_relat_1(k6_relat_1(A_326), B_327)))), inference(demodulation, [status(thm), theory('equality')], [c_306, c_1173, c_10854])).
% 7.37/2.65  tff(c_10941, plain, (![A_326, B_327]: (k7_relat_1(k6_relat_1(A_326), B_327)=k6_relat_1(k3_xboole_0(A_326, B_327)) | ~r1_tarski(k7_relat_1(k6_relat_1(A_326), B_327), k6_relat_1(k3_xboole_0(A_326, B_327))))), inference(resolution, [status(thm)], [c_10934, c_2])).
% 7.37/2.65  tff(c_11057, plain, (![A_326, B_327]: (k7_relat_1(k6_relat_1(A_326), B_327)=k6_relat_1(k3_xboole_0(A_326, B_327)))), inference(demodulation, [status(thm), theory('equality')], [c_303, c_10941])).
% 7.37/2.65  tff(c_38, plain, (k5_relat_1(k6_relat_1('#skF_2'), k6_relat_1('#skF_1'))!=k6_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_86])).
% 7.37/2.65  tff(c_124, plain, (k7_relat_1(k6_relat_1('#skF_1'), '#skF_2')!=k6_relat_1(k3_xboole_0('#skF_1', '#skF_2')) | ~v1_relat_1(k6_relat_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_114, c_38])).
% 7.37/2.65  tff(c_136, plain, (k7_relat_1(k6_relat_1('#skF_1'), '#skF_2')!=k6_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_124])).
% 7.37/2.65  tff(c_11132, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_11057, c_136])).
% 7.37/2.65  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.37/2.65  
% 7.37/2.65  Inference rules
% 7.37/2.65  ----------------------
% 7.37/2.65  #Ref     : 0
% 7.37/2.65  #Sup     : 2714
% 7.37/2.65  #Fact    : 0
% 7.37/2.65  #Define  : 0
% 7.37/2.65  #Split   : 1
% 7.37/2.65  #Chain   : 0
% 7.37/2.65  #Close   : 0
% 7.37/2.65  
% 7.37/2.65  Ordering : KBO
% 7.37/2.65  
% 7.37/2.65  Simplification rules
% 7.37/2.65  ----------------------
% 7.37/2.65  #Subsume      : 256
% 7.37/2.65  #Demod        : 2599
% 7.37/2.65  #Tautology    : 927
% 7.37/2.65  #SimpNegUnit  : 0
% 7.37/2.65  #BackRed      : 57
% 7.37/2.65  
% 7.37/2.65  #Partial instantiations: 0
% 7.37/2.65  #Strategies tried      : 1
% 7.37/2.65  
% 7.37/2.65  Timing (in seconds)
% 7.37/2.65  ----------------------
% 7.37/2.65  Preprocessing        : 0.32
% 7.37/2.65  Parsing              : 0.17
% 7.37/2.65  CNF conversion       : 0.02
% 7.37/2.65  Main loop            : 1.56
% 7.37/2.65  Inferencing          : 0.47
% 7.37/2.65  Reduction            : 0.57
% 7.37/2.65  Demodulation         : 0.44
% 7.37/2.65  BG Simplification    : 0.07
% 7.37/2.65  Subsumption          : 0.34
% 7.37/2.65  Abstraction          : 0.11
% 7.37/2.65  MUC search           : 0.00
% 7.37/2.65  Cooper               : 0.00
% 7.37/2.65  Total                : 1.92
% 7.37/2.65  Index Insertion      : 0.00
% 7.37/2.65  Index Deletion       : 0.00
% 7.37/2.65  Index Matching       : 0.00
% 7.37/2.65  BG Taut test         : 0.00
%------------------------------------------------------------------------------

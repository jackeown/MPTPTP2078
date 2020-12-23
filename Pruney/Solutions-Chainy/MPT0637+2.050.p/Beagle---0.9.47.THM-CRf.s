%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:03:30 EST 2020

% Result     : Theorem 7.28s
% Output     : CNFRefutation 7.28s
% Verified   : 
% Statistics : Number of formulae       :   99 ( 770 expanded)
%              Number of leaves         :   32 ( 283 expanded)
%              Depth                    :   22
%              Number of atoms          :  168 (1469 expanded)
%              Number of equality atoms :   50 ( 444 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > v1_funct_1 > k2_enumset1 > k1_enumset1 > k7_relat_1 > k5_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

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

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_95,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_67,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k7_relat_1(B,k3_xboole_0(k1_relat_1(B),A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t192_relat_1)).

tff(f_91,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k5_relat_1(k6_relat_1(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).

tff(f_73,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k5_relat_1(B,k6_relat_1(A)),B)
        & r1_tarski(k5_relat_1(k6_relat_1(A),B),B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_83,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k5_relat_1(k6_relat_1(k1_relat_1(A)),A) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t78_relat_1)).

tff(f_33,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_79,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k5_relat_1(k6_relat_1(A),B) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_relat_1)).

tff(f_87,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k5_relat_1(A,k6_relat_1(k2_relat_1(A))) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_relat_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_relat_1(B) )
     => v1_relat_1(k5_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).

tff(f_63,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ! [C] :
              ( v1_relat_1(C)
             => k5_relat_1(k5_relat_1(A,B),C) = k5_relat_1(A,k5_relat_1(B,C)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_relat_1)).

tff(f_98,negated_conjecture,(
    ~ ! [A,B] : k5_relat_1(k6_relat_1(B),k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_funct_1)).

tff(c_42,plain,(
    ! [A_36] : v1_relat_1(k6_relat_1(A_36)) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_26,plain,(
    ! [A_27] : k1_relat_1(k6_relat_1(A_27)) = A_27 ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_444,plain,(
    ! [B_88,A_89] :
      ( k7_relat_1(B_88,k3_xboole_0(k1_relat_1(B_88),A_89)) = k7_relat_1(B_88,A_89)
      | ~ v1_relat_1(B_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_243,plain,(
    ! [A_65,B_66] :
      ( k5_relat_1(k6_relat_1(A_65),B_66) = k7_relat_1(B_66,A_65)
      | ~ v1_relat_1(B_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_32,plain,(
    ! [B_29,A_28] :
      ( r1_tarski(k5_relat_1(B_29,k6_relat_1(A_28)),B_29)
      | ~ v1_relat_1(B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_250,plain,(
    ! [A_28,A_65] :
      ( r1_tarski(k7_relat_1(k6_relat_1(A_28),A_65),k6_relat_1(A_65))
      | ~ v1_relat_1(k6_relat_1(A_65))
      | ~ v1_relat_1(k6_relat_1(A_28)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_243,c_32])).

tff(c_287,plain,(
    ! [A_28,A_65] : r1_tarski(k7_relat_1(k6_relat_1(A_28),A_65),k6_relat_1(A_65)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_42,c_250])).

tff(c_454,plain,(
    ! [A_28,A_89] :
      ( r1_tarski(k7_relat_1(k6_relat_1(A_28),A_89),k6_relat_1(k3_xboole_0(k1_relat_1(k6_relat_1(A_28)),A_89)))
      | ~ v1_relat_1(k6_relat_1(A_28)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_444,c_287])).

tff(c_474,plain,(
    ! [A_28,A_89] : r1_tarski(k7_relat_1(k6_relat_1(A_28),A_89),k6_relat_1(k3_xboole_0(A_28,A_89))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_26,c_454])).

tff(c_471,plain,(
    ! [A_27,A_89] :
      ( k7_relat_1(k6_relat_1(A_27),k3_xboole_0(A_27,A_89)) = k7_relat_1(k6_relat_1(A_27),A_89)
      | ~ v1_relat_1(k6_relat_1(A_27)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_444])).

tff(c_479,plain,(
    ! [A_27,A_89] : k7_relat_1(k6_relat_1(A_27),k3_xboole_0(A_27,A_89)) = k7_relat_1(k6_relat_1(A_27),A_89) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_471])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_36,plain,(
    ! [A_32] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(A_32)),A_32) = A_32
      | ~ v1_relat_1(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_284,plain,(
    ! [A_32] :
      ( k7_relat_1(A_32,k1_relat_1(A_32)) = A_32
      | ~ v1_relat_1(A_32)
      | ~ v1_relat_1(A_32) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_243])).

tff(c_30,plain,(
    ! [A_28,B_29] :
      ( r1_tarski(k5_relat_1(k6_relat_1(A_28),B_29),B_29)
      | ~ v1_relat_1(B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_402,plain,(
    ! [B_80,A_81] :
      ( r1_tarski(k7_relat_1(B_80,A_81),B_80)
      | ~ v1_relat_1(B_80)
      | ~ v1_relat_1(B_80) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_243,c_30])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_824,plain,(
    ! [B_110,A_111] :
      ( k7_relat_1(B_110,A_111) = B_110
      | ~ r1_tarski(B_110,k7_relat_1(B_110,A_111))
      | ~ v1_relat_1(B_110) ) ),
    inference(resolution,[status(thm)],[c_402,c_2])).

tff(c_836,plain,(
    ! [A_32] :
      ( k7_relat_1(A_32,k1_relat_1(A_32)) = A_32
      | ~ r1_tarski(A_32,A_32)
      | ~ v1_relat_1(A_32)
      | ~ v1_relat_1(A_32)
      | ~ v1_relat_1(A_32) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_284,c_824])).

tff(c_845,plain,(
    ! [A_32] :
      ( k7_relat_1(A_32,k1_relat_1(A_32)) = A_32
      | ~ v1_relat_1(A_32) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_836])).

tff(c_8,plain,(
    ! [A_3,B_4] : r1_tarski(k3_xboole_0(A_3,B_4),A_3) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_40,plain,(
    ! [A_34,B_35] :
      ( k5_relat_1(k6_relat_1(A_34),B_35) = k7_relat_1(B_35,A_34)
      | ~ v1_relat_1(B_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_424,plain,(
    ! [A_84,B_85] :
      ( k5_relat_1(k6_relat_1(A_84),B_85) = B_85
      | ~ r1_tarski(k1_relat_1(B_85),A_84)
      | ~ v1_relat_1(B_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_427,plain,(
    ! [A_84,A_27] :
      ( k5_relat_1(k6_relat_1(A_84),k6_relat_1(A_27)) = k6_relat_1(A_27)
      | ~ r1_tarski(A_27,A_84)
      | ~ v1_relat_1(k6_relat_1(A_27)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_424])).

tff(c_646,plain,(
    ! [A_102,A_103] :
      ( k5_relat_1(k6_relat_1(A_102),k6_relat_1(A_103)) = k6_relat_1(A_103)
      | ~ r1_tarski(A_103,A_102) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_427])).

tff(c_686,plain,(
    ! [A_103,A_34] :
      ( k7_relat_1(k6_relat_1(A_103),A_34) = k6_relat_1(A_103)
      | ~ r1_tarski(A_103,A_34)
      | ~ v1_relat_1(k6_relat_1(A_103)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_646])).

tff(c_733,plain,(
    ! [A_106,A_107] :
      ( k7_relat_1(k6_relat_1(A_106),A_107) = k6_relat_1(A_106)
      | ~ r1_tarski(A_106,A_107) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_686])).

tff(c_748,plain,(
    ! [A_106,A_107] :
      ( r1_tarski(k6_relat_1(A_106),k6_relat_1(k3_xboole_0(A_106,A_107)))
      | ~ r1_tarski(A_106,A_107) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_733,c_474])).

tff(c_658,plain,(
    ! [A_103,A_102] :
      ( r1_tarski(k6_relat_1(A_103),k6_relat_1(A_102))
      | ~ v1_relat_1(k6_relat_1(A_102))
      | ~ r1_tarski(A_103,A_102) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_646,c_32])).

tff(c_728,plain,(
    ! [A_104,A_105] :
      ( r1_tarski(k6_relat_1(A_104),k6_relat_1(A_105))
      | ~ r1_tarski(A_104,A_105) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_658])).

tff(c_954,plain,(
    ! [A_118,A_117] :
      ( k6_relat_1(A_118) = k6_relat_1(A_117)
      | ~ r1_tarski(k6_relat_1(A_117),k6_relat_1(A_118))
      | ~ r1_tarski(A_118,A_117) ) ),
    inference(resolution,[status(thm)],[c_728,c_2])).

tff(c_957,plain,(
    ! [A_106,A_107] :
      ( k6_relat_1(k3_xboole_0(A_106,A_107)) = k6_relat_1(A_106)
      | ~ r1_tarski(k3_xboole_0(A_106,A_107),A_106)
      | ~ r1_tarski(A_106,A_107) ) ),
    inference(resolution,[status(thm)],[c_748,c_954])).

tff(c_1140,plain,(
    ! [A_121,A_122] :
      ( k6_relat_1(k3_xboole_0(A_121,A_122)) = k6_relat_1(A_121)
      | ~ r1_tarski(A_121,A_122) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_957])).

tff(c_1214,plain,(
    ! [A_121,A_122] :
      ( k3_xboole_0(A_121,A_122) = k1_relat_1(k6_relat_1(A_121))
      | ~ r1_tarski(A_121,A_122) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1140,c_26])).

tff(c_1276,plain,(
    ! [A_125,A_126] :
      ( k3_xboole_0(A_125,A_126) = A_125
      | ~ r1_tarski(A_125,A_126) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_1214])).

tff(c_1315,plain,(
    ! [A_28,A_65] : k3_xboole_0(k7_relat_1(k6_relat_1(A_28),A_65),k6_relat_1(A_65)) = k7_relat_1(k6_relat_1(A_28),A_65) ),
    inference(resolution,[status(thm)],[c_287,c_1276])).

tff(c_3024,plain,(
    ! [B_179,A_180] :
      ( k3_xboole_0(k5_relat_1(B_179,k6_relat_1(A_180)),B_179) = k5_relat_1(B_179,k6_relat_1(A_180))
      | ~ v1_relat_1(B_179) ) ),
    inference(resolution,[status(thm)],[c_32,c_1276])).

tff(c_3097,plain,(
    ! [A_180,A_34] :
      ( k3_xboole_0(k7_relat_1(k6_relat_1(A_180),A_34),k6_relat_1(A_34)) = k5_relat_1(k6_relat_1(A_34),k6_relat_1(A_180))
      | ~ v1_relat_1(k6_relat_1(A_34))
      | ~ v1_relat_1(k6_relat_1(A_180)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_3024])).

tff(c_3135,plain,(
    ! [A_34,A_180] : k5_relat_1(k6_relat_1(A_34),k6_relat_1(A_180)) = k7_relat_1(k6_relat_1(A_180),A_34) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_42,c_1315,c_3097])).

tff(c_28,plain,(
    ! [A_27] : k2_relat_1(k6_relat_1(A_27)) = A_27 ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_38,plain,(
    ! [A_33] :
      ( k5_relat_1(A_33,k6_relat_1(k2_relat_1(A_33))) = A_33
      | ~ v1_relat_1(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_278,plain,(
    ! [A_65] :
      ( k7_relat_1(k6_relat_1(k2_relat_1(k6_relat_1(A_65))),A_65) = k6_relat_1(A_65)
      | ~ v1_relat_1(k6_relat_1(k2_relat_1(k6_relat_1(A_65))))
      | ~ v1_relat_1(k6_relat_1(A_65)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_243])).

tff(c_298,plain,(
    ! [A_65] : k7_relat_1(k6_relat_1(A_65),A_65) = k6_relat_1(A_65) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_42,c_28,c_278])).

tff(c_1379,plain,(
    ! [A_129,B_130] : k3_xboole_0(k3_xboole_0(A_129,B_130),A_129) = k3_xboole_0(A_129,B_130) ),
    inference(resolution,[status(thm)],[c_8,c_1276])).

tff(c_1397,plain,(
    ! [A_129,B_130] : k7_relat_1(k6_relat_1(k3_xboole_0(A_129,B_130)),k3_xboole_0(A_129,B_130)) = k7_relat_1(k6_relat_1(k3_xboole_0(A_129,B_130)),A_129) ),
    inference(superposition,[status(thm),theory(equality)],[c_1379,c_479])).

tff(c_1440,plain,(
    ! [A_129,B_130] : k7_relat_1(k6_relat_1(k3_xboole_0(A_129,B_130)),A_129) = k6_relat_1(k3_xboole_0(A_129,B_130)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_298,c_1397])).

tff(c_512,plain,(
    ! [A_93,A_94] : k7_relat_1(k6_relat_1(A_93),k3_xboole_0(A_93,A_94)) = k7_relat_1(k6_relat_1(A_93),A_94) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_471])).

tff(c_20,plain,(
    ! [A_16,B_17] :
      ( v1_relat_1(k5_relat_1(A_16,B_17))
      | ~ v1_relat_1(B_17)
      | ~ v1_relat_1(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_271,plain,(
    ! [B_66,A_65] :
      ( v1_relat_1(k7_relat_1(B_66,A_65))
      | ~ v1_relat_1(B_66)
      | ~ v1_relat_1(k6_relat_1(A_65))
      | ~ v1_relat_1(B_66) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_243,c_20])).

tff(c_295,plain,(
    ! [B_66,A_65] :
      ( v1_relat_1(k7_relat_1(B_66,A_65))
      | ~ v1_relat_1(B_66) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_271])).

tff(c_527,plain,(
    ! [A_93,A_94] :
      ( v1_relat_1(k7_relat_1(k6_relat_1(A_93),A_94))
      | ~ v1_relat_1(k6_relat_1(A_93)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_512,c_295])).

tff(c_543,plain,(
    ! [A_93,A_94] : v1_relat_1(k7_relat_1(k6_relat_1(A_93),A_94)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_527])).

tff(c_566,plain,(
    ! [A_97,B_98,C_99] :
      ( k5_relat_1(k5_relat_1(A_97,B_98),C_99) = k5_relat_1(A_97,k5_relat_1(B_98,C_99))
      | ~ v1_relat_1(C_99)
      | ~ v1_relat_1(B_98)
      | ~ v1_relat_1(A_97) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_576,plain,(
    ! [A_97,B_98,A_28] :
      ( r1_tarski(k5_relat_1(A_97,k5_relat_1(B_98,k6_relat_1(A_28))),k5_relat_1(A_97,B_98))
      | ~ v1_relat_1(k5_relat_1(A_97,B_98))
      | ~ v1_relat_1(k6_relat_1(A_28))
      | ~ v1_relat_1(B_98)
      | ~ v1_relat_1(A_97) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_566,c_32])).

tff(c_3627,plain,(
    ! [A_189,B_190,A_191] :
      ( r1_tarski(k5_relat_1(A_189,k5_relat_1(B_190,k6_relat_1(A_191))),k5_relat_1(A_189,B_190))
      | ~ v1_relat_1(k5_relat_1(A_189,B_190))
      | ~ v1_relat_1(B_190)
      | ~ v1_relat_1(A_189) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_576])).

tff(c_3640,plain,(
    ! [A_34,A_180,A_191] :
      ( r1_tarski(k5_relat_1(k6_relat_1(A_34),k5_relat_1(k6_relat_1(A_180),k6_relat_1(A_191))),k7_relat_1(k6_relat_1(A_180),A_34))
      | ~ v1_relat_1(k5_relat_1(k6_relat_1(A_34),k6_relat_1(A_180)))
      | ~ v1_relat_1(k6_relat_1(A_180))
      | ~ v1_relat_1(k6_relat_1(A_34)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3135,c_3627])).

tff(c_9165,plain,(
    ! [A_277,A_278,A_279] : r1_tarski(k5_relat_1(k6_relat_1(A_277),k7_relat_1(k6_relat_1(A_278),A_279)),k7_relat_1(k6_relat_1(A_279),A_277)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_42,c_543,c_3135,c_3135,c_3640])).

tff(c_9236,plain,(
    ! [A_277,A_129,B_130] : r1_tarski(k5_relat_1(k6_relat_1(A_277),k6_relat_1(k3_xboole_0(A_129,B_130))),k7_relat_1(k6_relat_1(A_129),A_277)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1440,c_9165])).

tff(c_9460,plain,(
    ! [A_283,B_284,A_285] : r1_tarski(k7_relat_1(k6_relat_1(k3_xboole_0(A_283,B_284)),A_285),k7_relat_1(k6_relat_1(A_283),A_285)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3135,c_9236])).

tff(c_9556,plain,(
    ! [A_283,B_284] :
      ( r1_tarski(k6_relat_1(k3_xboole_0(A_283,B_284)),k7_relat_1(k6_relat_1(A_283),k1_relat_1(k6_relat_1(k3_xboole_0(A_283,B_284)))))
      | ~ v1_relat_1(k6_relat_1(k3_xboole_0(A_283,B_284))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_845,c_9460])).

tff(c_9626,plain,(
    ! [A_286,B_287] : r1_tarski(k6_relat_1(k3_xboole_0(A_286,B_287)),k7_relat_1(k6_relat_1(A_286),B_287)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_479,c_26,c_9556])).

tff(c_9633,plain,(
    ! [A_286,B_287] :
      ( k7_relat_1(k6_relat_1(A_286),B_287) = k6_relat_1(k3_xboole_0(A_286,B_287))
      | ~ r1_tarski(k7_relat_1(k6_relat_1(A_286),B_287),k6_relat_1(k3_xboole_0(A_286,B_287))) ) ),
    inference(resolution,[status(thm)],[c_9626,c_2])).

tff(c_9741,plain,(
    ! [A_286,B_287] : k7_relat_1(k6_relat_1(A_286),B_287) = k6_relat_1(k3_xboole_0(A_286,B_287)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_474,c_9633])).

tff(c_46,plain,(
    k5_relat_1(k6_relat_1('#skF_2'),k6_relat_1('#skF_1')) != k6_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_268,plain,
    ( k7_relat_1(k6_relat_1('#skF_1'),'#skF_2') != k6_relat_1(k3_xboole_0('#skF_1','#skF_2'))
    | ~ v1_relat_1(k6_relat_1('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_243,c_46])).

tff(c_293,plain,(
    k7_relat_1(k6_relat_1('#skF_1'),'#skF_2') != k6_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_268])).

tff(c_9800,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_9741,c_293])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n008.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 13:35:30 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.28/2.62  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.28/2.63  
% 7.28/2.63  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.28/2.63  %$ r1_tarski > v1_relat_1 > v1_funct_1 > k2_enumset1 > k1_enumset1 > k7_relat_1 > k5_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1
% 7.28/2.63  
% 7.28/2.63  %Foreground sorts:
% 7.28/2.63  
% 7.28/2.63  
% 7.28/2.63  %Background operators:
% 7.28/2.63  
% 7.28/2.63  
% 7.28/2.63  %Foreground operators:
% 7.28/2.63  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 7.28/2.63  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.28/2.63  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 7.28/2.63  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 7.28/2.63  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 7.28/2.63  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.28/2.63  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 7.28/2.63  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 7.28/2.63  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 7.28/2.63  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 7.28/2.63  tff('#skF_2', type, '#skF_2': $i).
% 7.28/2.63  tff('#skF_1', type, '#skF_1': $i).
% 7.28/2.63  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.28/2.63  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 7.28/2.63  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 7.28/2.63  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.28/2.63  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 7.28/2.63  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 7.28/2.63  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 7.28/2.63  
% 7.28/2.65  tff(f_95, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc3_funct_1)).
% 7.28/2.65  tff(f_67, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 7.28/2.65  tff(f_53, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k7_relat_1(B, k3_xboole_0(k1_relat_1(B), A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t192_relat_1)).
% 7.28/2.65  tff(f_91, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_relat_1)).
% 7.28/2.65  tff(f_73, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k5_relat_1(B, k6_relat_1(A)), B) & r1_tarski(k5_relat_1(k6_relat_1(A), B), B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t76_relat_1)).
% 7.28/2.65  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 7.28/2.65  tff(f_83, axiom, (![A]: (v1_relat_1(A) => (k5_relat_1(k6_relat_1(k1_relat_1(A)), A) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t78_relat_1)).
% 7.28/2.65  tff(f_33, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 7.28/2.65  tff(f_79, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k5_relat_1(k6_relat_1(A), B) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t77_relat_1)).
% 7.28/2.65  tff(f_87, axiom, (![A]: (v1_relat_1(A) => (k5_relat_1(A, k6_relat_1(k2_relat_1(A))) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t80_relat_1)).
% 7.28/2.65  tff(f_49, axiom, (![A, B]: ((v1_relat_1(A) & v1_relat_1(B)) => v1_relat_1(k5_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k5_relat_1)).
% 7.28/2.65  tff(f_63, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (k5_relat_1(k5_relat_1(A, B), C) = k5_relat_1(A, k5_relat_1(B, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_relat_1)).
% 7.28/2.65  tff(f_98, negated_conjecture, ~(![A, B]: (k5_relat_1(k6_relat_1(B), k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_funct_1)).
% 7.28/2.65  tff(c_42, plain, (![A_36]: (v1_relat_1(k6_relat_1(A_36)))), inference(cnfTransformation, [status(thm)], [f_95])).
% 7.28/2.65  tff(c_26, plain, (![A_27]: (k1_relat_1(k6_relat_1(A_27))=A_27)), inference(cnfTransformation, [status(thm)], [f_67])).
% 7.28/2.65  tff(c_444, plain, (![B_88, A_89]: (k7_relat_1(B_88, k3_xboole_0(k1_relat_1(B_88), A_89))=k7_relat_1(B_88, A_89) | ~v1_relat_1(B_88))), inference(cnfTransformation, [status(thm)], [f_53])).
% 7.28/2.65  tff(c_243, plain, (![A_65, B_66]: (k5_relat_1(k6_relat_1(A_65), B_66)=k7_relat_1(B_66, A_65) | ~v1_relat_1(B_66))), inference(cnfTransformation, [status(thm)], [f_91])).
% 7.28/2.65  tff(c_32, plain, (![B_29, A_28]: (r1_tarski(k5_relat_1(B_29, k6_relat_1(A_28)), B_29) | ~v1_relat_1(B_29))), inference(cnfTransformation, [status(thm)], [f_73])).
% 7.28/2.65  tff(c_250, plain, (![A_28, A_65]: (r1_tarski(k7_relat_1(k6_relat_1(A_28), A_65), k6_relat_1(A_65)) | ~v1_relat_1(k6_relat_1(A_65)) | ~v1_relat_1(k6_relat_1(A_28)))), inference(superposition, [status(thm), theory('equality')], [c_243, c_32])).
% 7.28/2.65  tff(c_287, plain, (![A_28, A_65]: (r1_tarski(k7_relat_1(k6_relat_1(A_28), A_65), k6_relat_1(A_65)))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_42, c_250])).
% 7.28/2.65  tff(c_454, plain, (![A_28, A_89]: (r1_tarski(k7_relat_1(k6_relat_1(A_28), A_89), k6_relat_1(k3_xboole_0(k1_relat_1(k6_relat_1(A_28)), A_89))) | ~v1_relat_1(k6_relat_1(A_28)))), inference(superposition, [status(thm), theory('equality')], [c_444, c_287])).
% 7.28/2.65  tff(c_474, plain, (![A_28, A_89]: (r1_tarski(k7_relat_1(k6_relat_1(A_28), A_89), k6_relat_1(k3_xboole_0(A_28, A_89))))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_26, c_454])).
% 7.28/2.65  tff(c_471, plain, (![A_27, A_89]: (k7_relat_1(k6_relat_1(A_27), k3_xboole_0(A_27, A_89))=k7_relat_1(k6_relat_1(A_27), A_89) | ~v1_relat_1(k6_relat_1(A_27)))), inference(superposition, [status(thm), theory('equality')], [c_26, c_444])).
% 7.28/2.65  tff(c_479, plain, (![A_27, A_89]: (k7_relat_1(k6_relat_1(A_27), k3_xboole_0(A_27, A_89))=k7_relat_1(k6_relat_1(A_27), A_89))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_471])).
% 7.28/2.65  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.28/2.65  tff(c_36, plain, (![A_32]: (k5_relat_1(k6_relat_1(k1_relat_1(A_32)), A_32)=A_32 | ~v1_relat_1(A_32))), inference(cnfTransformation, [status(thm)], [f_83])).
% 7.28/2.65  tff(c_284, plain, (![A_32]: (k7_relat_1(A_32, k1_relat_1(A_32))=A_32 | ~v1_relat_1(A_32) | ~v1_relat_1(A_32))), inference(superposition, [status(thm), theory('equality')], [c_36, c_243])).
% 7.28/2.65  tff(c_30, plain, (![A_28, B_29]: (r1_tarski(k5_relat_1(k6_relat_1(A_28), B_29), B_29) | ~v1_relat_1(B_29))), inference(cnfTransformation, [status(thm)], [f_73])).
% 7.28/2.65  tff(c_402, plain, (![B_80, A_81]: (r1_tarski(k7_relat_1(B_80, A_81), B_80) | ~v1_relat_1(B_80) | ~v1_relat_1(B_80))), inference(superposition, [status(thm), theory('equality')], [c_243, c_30])).
% 7.28/2.65  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.28/2.65  tff(c_824, plain, (![B_110, A_111]: (k7_relat_1(B_110, A_111)=B_110 | ~r1_tarski(B_110, k7_relat_1(B_110, A_111)) | ~v1_relat_1(B_110))), inference(resolution, [status(thm)], [c_402, c_2])).
% 7.28/2.65  tff(c_836, plain, (![A_32]: (k7_relat_1(A_32, k1_relat_1(A_32))=A_32 | ~r1_tarski(A_32, A_32) | ~v1_relat_1(A_32) | ~v1_relat_1(A_32) | ~v1_relat_1(A_32))), inference(superposition, [status(thm), theory('equality')], [c_284, c_824])).
% 7.28/2.65  tff(c_845, plain, (![A_32]: (k7_relat_1(A_32, k1_relat_1(A_32))=A_32 | ~v1_relat_1(A_32))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_836])).
% 7.28/2.65  tff(c_8, plain, (![A_3, B_4]: (r1_tarski(k3_xboole_0(A_3, B_4), A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 7.28/2.65  tff(c_40, plain, (![A_34, B_35]: (k5_relat_1(k6_relat_1(A_34), B_35)=k7_relat_1(B_35, A_34) | ~v1_relat_1(B_35))), inference(cnfTransformation, [status(thm)], [f_91])).
% 7.28/2.65  tff(c_424, plain, (![A_84, B_85]: (k5_relat_1(k6_relat_1(A_84), B_85)=B_85 | ~r1_tarski(k1_relat_1(B_85), A_84) | ~v1_relat_1(B_85))), inference(cnfTransformation, [status(thm)], [f_79])).
% 7.28/2.65  tff(c_427, plain, (![A_84, A_27]: (k5_relat_1(k6_relat_1(A_84), k6_relat_1(A_27))=k6_relat_1(A_27) | ~r1_tarski(A_27, A_84) | ~v1_relat_1(k6_relat_1(A_27)))), inference(superposition, [status(thm), theory('equality')], [c_26, c_424])).
% 7.28/2.65  tff(c_646, plain, (![A_102, A_103]: (k5_relat_1(k6_relat_1(A_102), k6_relat_1(A_103))=k6_relat_1(A_103) | ~r1_tarski(A_103, A_102))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_427])).
% 7.28/2.65  tff(c_686, plain, (![A_103, A_34]: (k7_relat_1(k6_relat_1(A_103), A_34)=k6_relat_1(A_103) | ~r1_tarski(A_103, A_34) | ~v1_relat_1(k6_relat_1(A_103)))), inference(superposition, [status(thm), theory('equality')], [c_40, c_646])).
% 7.28/2.65  tff(c_733, plain, (![A_106, A_107]: (k7_relat_1(k6_relat_1(A_106), A_107)=k6_relat_1(A_106) | ~r1_tarski(A_106, A_107))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_686])).
% 7.28/2.65  tff(c_748, plain, (![A_106, A_107]: (r1_tarski(k6_relat_1(A_106), k6_relat_1(k3_xboole_0(A_106, A_107))) | ~r1_tarski(A_106, A_107))), inference(superposition, [status(thm), theory('equality')], [c_733, c_474])).
% 7.28/2.65  tff(c_658, plain, (![A_103, A_102]: (r1_tarski(k6_relat_1(A_103), k6_relat_1(A_102)) | ~v1_relat_1(k6_relat_1(A_102)) | ~r1_tarski(A_103, A_102))), inference(superposition, [status(thm), theory('equality')], [c_646, c_32])).
% 7.28/2.65  tff(c_728, plain, (![A_104, A_105]: (r1_tarski(k6_relat_1(A_104), k6_relat_1(A_105)) | ~r1_tarski(A_104, A_105))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_658])).
% 7.28/2.65  tff(c_954, plain, (![A_118, A_117]: (k6_relat_1(A_118)=k6_relat_1(A_117) | ~r1_tarski(k6_relat_1(A_117), k6_relat_1(A_118)) | ~r1_tarski(A_118, A_117))), inference(resolution, [status(thm)], [c_728, c_2])).
% 7.28/2.65  tff(c_957, plain, (![A_106, A_107]: (k6_relat_1(k3_xboole_0(A_106, A_107))=k6_relat_1(A_106) | ~r1_tarski(k3_xboole_0(A_106, A_107), A_106) | ~r1_tarski(A_106, A_107))), inference(resolution, [status(thm)], [c_748, c_954])).
% 7.28/2.65  tff(c_1140, plain, (![A_121, A_122]: (k6_relat_1(k3_xboole_0(A_121, A_122))=k6_relat_1(A_121) | ~r1_tarski(A_121, A_122))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_957])).
% 7.28/2.65  tff(c_1214, plain, (![A_121, A_122]: (k3_xboole_0(A_121, A_122)=k1_relat_1(k6_relat_1(A_121)) | ~r1_tarski(A_121, A_122))), inference(superposition, [status(thm), theory('equality')], [c_1140, c_26])).
% 7.28/2.65  tff(c_1276, plain, (![A_125, A_126]: (k3_xboole_0(A_125, A_126)=A_125 | ~r1_tarski(A_125, A_126))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_1214])).
% 7.28/2.65  tff(c_1315, plain, (![A_28, A_65]: (k3_xboole_0(k7_relat_1(k6_relat_1(A_28), A_65), k6_relat_1(A_65))=k7_relat_1(k6_relat_1(A_28), A_65))), inference(resolution, [status(thm)], [c_287, c_1276])).
% 7.28/2.65  tff(c_3024, plain, (![B_179, A_180]: (k3_xboole_0(k5_relat_1(B_179, k6_relat_1(A_180)), B_179)=k5_relat_1(B_179, k6_relat_1(A_180)) | ~v1_relat_1(B_179))), inference(resolution, [status(thm)], [c_32, c_1276])).
% 7.28/2.65  tff(c_3097, plain, (![A_180, A_34]: (k3_xboole_0(k7_relat_1(k6_relat_1(A_180), A_34), k6_relat_1(A_34))=k5_relat_1(k6_relat_1(A_34), k6_relat_1(A_180)) | ~v1_relat_1(k6_relat_1(A_34)) | ~v1_relat_1(k6_relat_1(A_180)))), inference(superposition, [status(thm), theory('equality')], [c_40, c_3024])).
% 7.28/2.65  tff(c_3135, plain, (![A_34, A_180]: (k5_relat_1(k6_relat_1(A_34), k6_relat_1(A_180))=k7_relat_1(k6_relat_1(A_180), A_34))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_42, c_1315, c_3097])).
% 7.28/2.65  tff(c_28, plain, (![A_27]: (k2_relat_1(k6_relat_1(A_27))=A_27)), inference(cnfTransformation, [status(thm)], [f_67])).
% 7.28/2.65  tff(c_38, plain, (![A_33]: (k5_relat_1(A_33, k6_relat_1(k2_relat_1(A_33)))=A_33 | ~v1_relat_1(A_33))), inference(cnfTransformation, [status(thm)], [f_87])).
% 7.28/2.65  tff(c_278, plain, (![A_65]: (k7_relat_1(k6_relat_1(k2_relat_1(k6_relat_1(A_65))), A_65)=k6_relat_1(A_65) | ~v1_relat_1(k6_relat_1(k2_relat_1(k6_relat_1(A_65)))) | ~v1_relat_1(k6_relat_1(A_65)))), inference(superposition, [status(thm), theory('equality')], [c_38, c_243])).
% 7.28/2.65  tff(c_298, plain, (![A_65]: (k7_relat_1(k6_relat_1(A_65), A_65)=k6_relat_1(A_65))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_42, c_28, c_278])).
% 7.28/2.65  tff(c_1379, plain, (![A_129, B_130]: (k3_xboole_0(k3_xboole_0(A_129, B_130), A_129)=k3_xboole_0(A_129, B_130))), inference(resolution, [status(thm)], [c_8, c_1276])).
% 7.28/2.65  tff(c_1397, plain, (![A_129, B_130]: (k7_relat_1(k6_relat_1(k3_xboole_0(A_129, B_130)), k3_xboole_0(A_129, B_130))=k7_relat_1(k6_relat_1(k3_xboole_0(A_129, B_130)), A_129))), inference(superposition, [status(thm), theory('equality')], [c_1379, c_479])).
% 7.28/2.65  tff(c_1440, plain, (![A_129, B_130]: (k7_relat_1(k6_relat_1(k3_xboole_0(A_129, B_130)), A_129)=k6_relat_1(k3_xboole_0(A_129, B_130)))), inference(demodulation, [status(thm), theory('equality')], [c_298, c_1397])).
% 7.28/2.65  tff(c_512, plain, (![A_93, A_94]: (k7_relat_1(k6_relat_1(A_93), k3_xboole_0(A_93, A_94))=k7_relat_1(k6_relat_1(A_93), A_94))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_471])).
% 7.28/2.65  tff(c_20, plain, (![A_16, B_17]: (v1_relat_1(k5_relat_1(A_16, B_17)) | ~v1_relat_1(B_17) | ~v1_relat_1(A_16))), inference(cnfTransformation, [status(thm)], [f_49])).
% 7.28/2.65  tff(c_271, plain, (![B_66, A_65]: (v1_relat_1(k7_relat_1(B_66, A_65)) | ~v1_relat_1(B_66) | ~v1_relat_1(k6_relat_1(A_65)) | ~v1_relat_1(B_66))), inference(superposition, [status(thm), theory('equality')], [c_243, c_20])).
% 7.28/2.65  tff(c_295, plain, (![B_66, A_65]: (v1_relat_1(k7_relat_1(B_66, A_65)) | ~v1_relat_1(B_66))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_271])).
% 7.28/2.65  tff(c_527, plain, (![A_93, A_94]: (v1_relat_1(k7_relat_1(k6_relat_1(A_93), A_94)) | ~v1_relat_1(k6_relat_1(A_93)))), inference(superposition, [status(thm), theory('equality')], [c_512, c_295])).
% 7.28/2.65  tff(c_543, plain, (![A_93, A_94]: (v1_relat_1(k7_relat_1(k6_relat_1(A_93), A_94)))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_527])).
% 7.28/2.65  tff(c_566, plain, (![A_97, B_98, C_99]: (k5_relat_1(k5_relat_1(A_97, B_98), C_99)=k5_relat_1(A_97, k5_relat_1(B_98, C_99)) | ~v1_relat_1(C_99) | ~v1_relat_1(B_98) | ~v1_relat_1(A_97))), inference(cnfTransformation, [status(thm)], [f_63])).
% 7.28/2.65  tff(c_576, plain, (![A_97, B_98, A_28]: (r1_tarski(k5_relat_1(A_97, k5_relat_1(B_98, k6_relat_1(A_28))), k5_relat_1(A_97, B_98)) | ~v1_relat_1(k5_relat_1(A_97, B_98)) | ~v1_relat_1(k6_relat_1(A_28)) | ~v1_relat_1(B_98) | ~v1_relat_1(A_97))), inference(superposition, [status(thm), theory('equality')], [c_566, c_32])).
% 7.28/2.65  tff(c_3627, plain, (![A_189, B_190, A_191]: (r1_tarski(k5_relat_1(A_189, k5_relat_1(B_190, k6_relat_1(A_191))), k5_relat_1(A_189, B_190)) | ~v1_relat_1(k5_relat_1(A_189, B_190)) | ~v1_relat_1(B_190) | ~v1_relat_1(A_189))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_576])).
% 7.28/2.65  tff(c_3640, plain, (![A_34, A_180, A_191]: (r1_tarski(k5_relat_1(k6_relat_1(A_34), k5_relat_1(k6_relat_1(A_180), k6_relat_1(A_191))), k7_relat_1(k6_relat_1(A_180), A_34)) | ~v1_relat_1(k5_relat_1(k6_relat_1(A_34), k6_relat_1(A_180))) | ~v1_relat_1(k6_relat_1(A_180)) | ~v1_relat_1(k6_relat_1(A_34)))), inference(superposition, [status(thm), theory('equality')], [c_3135, c_3627])).
% 7.28/2.65  tff(c_9165, plain, (![A_277, A_278, A_279]: (r1_tarski(k5_relat_1(k6_relat_1(A_277), k7_relat_1(k6_relat_1(A_278), A_279)), k7_relat_1(k6_relat_1(A_279), A_277)))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_42, c_543, c_3135, c_3135, c_3640])).
% 7.28/2.65  tff(c_9236, plain, (![A_277, A_129, B_130]: (r1_tarski(k5_relat_1(k6_relat_1(A_277), k6_relat_1(k3_xboole_0(A_129, B_130))), k7_relat_1(k6_relat_1(A_129), A_277)))), inference(superposition, [status(thm), theory('equality')], [c_1440, c_9165])).
% 7.28/2.65  tff(c_9460, plain, (![A_283, B_284, A_285]: (r1_tarski(k7_relat_1(k6_relat_1(k3_xboole_0(A_283, B_284)), A_285), k7_relat_1(k6_relat_1(A_283), A_285)))), inference(demodulation, [status(thm), theory('equality')], [c_3135, c_9236])).
% 7.28/2.65  tff(c_9556, plain, (![A_283, B_284]: (r1_tarski(k6_relat_1(k3_xboole_0(A_283, B_284)), k7_relat_1(k6_relat_1(A_283), k1_relat_1(k6_relat_1(k3_xboole_0(A_283, B_284))))) | ~v1_relat_1(k6_relat_1(k3_xboole_0(A_283, B_284))))), inference(superposition, [status(thm), theory('equality')], [c_845, c_9460])).
% 7.28/2.65  tff(c_9626, plain, (![A_286, B_287]: (r1_tarski(k6_relat_1(k3_xboole_0(A_286, B_287)), k7_relat_1(k6_relat_1(A_286), B_287)))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_479, c_26, c_9556])).
% 7.28/2.65  tff(c_9633, plain, (![A_286, B_287]: (k7_relat_1(k6_relat_1(A_286), B_287)=k6_relat_1(k3_xboole_0(A_286, B_287)) | ~r1_tarski(k7_relat_1(k6_relat_1(A_286), B_287), k6_relat_1(k3_xboole_0(A_286, B_287))))), inference(resolution, [status(thm)], [c_9626, c_2])).
% 7.28/2.65  tff(c_9741, plain, (![A_286, B_287]: (k7_relat_1(k6_relat_1(A_286), B_287)=k6_relat_1(k3_xboole_0(A_286, B_287)))), inference(demodulation, [status(thm), theory('equality')], [c_474, c_9633])).
% 7.28/2.65  tff(c_46, plain, (k5_relat_1(k6_relat_1('#skF_2'), k6_relat_1('#skF_1'))!=k6_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_98])).
% 7.28/2.65  tff(c_268, plain, (k7_relat_1(k6_relat_1('#skF_1'), '#skF_2')!=k6_relat_1(k3_xboole_0('#skF_1', '#skF_2')) | ~v1_relat_1(k6_relat_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_243, c_46])).
% 7.28/2.65  tff(c_293, plain, (k7_relat_1(k6_relat_1('#skF_1'), '#skF_2')!=k6_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_268])).
% 7.28/2.65  tff(c_9800, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_9741, c_293])).
% 7.28/2.65  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.28/2.65  
% 7.28/2.65  Inference rules
% 7.28/2.65  ----------------------
% 7.28/2.65  #Ref     : 0
% 7.28/2.66  #Sup     : 2350
% 7.28/2.66  #Fact    : 0
% 7.28/2.66  #Define  : 0
% 7.28/2.66  #Split   : 1
% 7.28/2.66  #Chain   : 0
% 7.28/2.66  #Close   : 0
% 7.28/2.66  
% 7.28/2.66  Ordering : KBO
% 7.28/2.66  
% 7.28/2.66  Simplification rules
% 7.28/2.66  ----------------------
% 7.28/2.66  #Subsume      : 240
% 7.28/2.66  #Demod        : 2480
% 7.28/2.66  #Tautology    : 1046
% 7.28/2.66  #SimpNegUnit  : 0
% 7.28/2.66  #BackRed      : 37
% 7.28/2.66  
% 7.28/2.66  #Partial instantiations: 0
% 7.28/2.66  #Strategies tried      : 1
% 7.28/2.66  
% 7.28/2.66  Timing (in seconds)
% 7.28/2.66  ----------------------
% 7.28/2.66  Preprocessing        : 0.33
% 7.28/2.66  Parsing              : 0.18
% 7.28/2.66  CNF conversion       : 0.02
% 7.28/2.66  Main loop            : 1.53
% 7.28/2.66  Inferencing          : 0.46
% 7.28/2.66  Reduction            : 0.59
% 7.28/2.66  Demodulation         : 0.46
% 7.28/2.66  BG Simplification    : 0.06
% 7.28/2.66  Subsumption          : 0.32
% 7.28/2.66  Abstraction          : 0.10
% 7.28/2.66  MUC search           : 0.00
% 7.28/2.66  Cooper               : 0.00
% 7.28/2.66  Total                : 1.90
% 7.28/2.66  Index Insertion      : 0.00
% 7.28/2.66  Index Deletion       : 0.00
% 7.28/2.66  Index Matching       : 0.00
% 7.28/2.66  BG Taut test         : 0.00
%------------------------------------------------------------------------------

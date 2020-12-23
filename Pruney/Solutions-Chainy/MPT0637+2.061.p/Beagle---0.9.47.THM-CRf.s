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
% DateTime   : Thu Dec  3 10:03:32 EST 2020

% Result     : Theorem 8.00s
% Output     : CNFRefutation 8.12s
% Verified   : 
% Statistics : Number of formulae       :  108 ( 377 expanded)
%              Number of leaves         :   36 ( 148 expanded)
%              Depth                    :   13
%              Number of atoms          :  172 ( 616 expanded)
%              Number of equality atoms :   70 ( 222 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k8_relat_1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1

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

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

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

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_49,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_88,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_106,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k1_relat_1(k7_relat_1(B,A)) = k3_xboole_0(k1_relat_1(B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_relat_1)).

tff(f_110,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k5_relat_1(k6_relat_1(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).

tff(f_74,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => r1_tarski(k1_relat_1(k5_relat_1(A,B)),k1_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_relat_1)).

tff(f_27,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_102,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k5_relat_1(A,k6_relat_1(k2_relat_1(A))) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_relat_1)).

tff(f_98,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k2_relat_1(B),A)
       => k5_relat_1(B,k6_relat_1(A)) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_relat_1)).

tff(f_60,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k8_relat_1(A,B) = k5_relat_1(B,k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_relat_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_relat_1(B) )
     => v1_relat_1(k5_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).

tff(f_92,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k5_relat_1(k6_relat_1(k1_relat_1(A)),A) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_relat_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ! [C] :
          ( v1_relat_1(C)
         => k7_relat_1(k5_relat_1(B,C),A) = k5_relat_1(k7_relat_1(B,A),C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t112_relat_1)).

tff(f_67,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ! [C] :
          ( v1_relat_1(C)
         => k8_relat_1(A,k5_relat_1(B,C)) = k5_relat_1(B,k8_relat_1(A,C)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t139_relat_1)).

tff(f_113,negated_conjecture,(
    ~ ! [A,B] : k5_relat_1(k6_relat_1(B),k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_funct_1)).

tff(c_20,plain,(
    ! [A_34] : v1_relat_1(k6_relat_1(A_34)) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_32,plain,(
    ! [A_55] : k1_relat_1(k6_relat_1(A_55)) = A_55 ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_293,plain,(
    ! [B_91,A_92] :
      ( k3_xboole_0(k1_relat_1(B_91),A_92) = k1_relat_1(k7_relat_1(B_91,A_92))
      | ~ v1_relat_1(B_91) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_305,plain,(
    ! [A_55,A_92] :
      ( k1_relat_1(k7_relat_1(k6_relat_1(A_55),A_92)) = k3_xboole_0(A_55,A_92)
      | ~ v1_relat_1(k6_relat_1(A_55)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_293])).

tff(c_309,plain,(
    ! [A_55,A_92] : k1_relat_1(k7_relat_1(k6_relat_1(A_55),A_92)) = k3_xboole_0(A_55,A_92) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_305])).

tff(c_44,plain,(
    ! [A_62,B_63] :
      ( k5_relat_1(k6_relat_1(A_62),B_63) = k7_relat_1(B_63,A_62)
      | ~ v1_relat_1(B_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_491,plain,(
    ! [A_111,B_112] :
      ( r1_tarski(k1_relat_1(k5_relat_1(A_111,B_112)),k1_relat_1(A_111))
      | ~ v1_relat_1(B_112)
      | ~ v1_relat_1(A_111) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_497,plain,(
    ! [B_63,A_62] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_63,A_62)),k1_relat_1(k6_relat_1(A_62)))
      | ~ v1_relat_1(B_63)
      | ~ v1_relat_1(k6_relat_1(A_62))
      | ~ v1_relat_1(B_63) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_491])).

tff(c_527,plain,(
    ! [B_113,A_114] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_113,A_114)),A_114)
      | ~ v1_relat_1(B_113) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_32,c_497])).

tff(c_533,plain,(
    ! [A_55,A_92] :
      ( r1_tarski(k3_xboole_0(A_55,A_92),A_92)
      | ~ v1_relat_1(k6_relat_1(A_55)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_309,c_527])).

tff(c_539,plain,(
    ! [A_55,A_92] : r1_tarski(k3_xboole_0(A_55,A_92),A_92) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_533])).

tff(c_2,plain,(
    ! [A_1,B_2] : r1_tarski(k3_xboole_0(A_1,B_2),A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_34,plain,(
    ! [A_55] : k2_relat_1(k6_relat_1(A_55)) = A_55 ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_211,plain,(
    ! [A_86,B_87] :
      ( k5_relat_1(k6_relat_1(A_86),B_87) = k7_relat_1(B_87,A_86)
      | ~ v1_relat_1(B_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_40,plain,(
    ! [A_59] :
      ( k5_relat_1(A_59,k6_relat_1(k2_relat_1(A_59))) = A_59
      | ~ v1_relat_1(A_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_222,plain,(
    ! [A_86] :
      ( k7_relat_1(k6_relat_1(k2_relat_1(k6_relat_1(A_86))),A_86) = k6_relat_1(A_86)
      | ~ v1_relat_1(k6_relat_1(A_86))
      | ~ v1_relat_1(k6_relat_1(k2_relat_1(k6_relat_1(A_86)))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_211,c_40])).

tff(c_258,plain,(
    ! [A_86] : k7_relat_1(k6_relat_1(A_86),A_86) = k6_relat_1(A_86) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_20,c_34,c_222])).

tff(c_426,plain,(
    ! [B_106,A_107] :
      ( k5_relat_1(B_106,k6_relat_1(A_107)) = B_106
      | ~ r1_tarski(k2_relat_1(B_106),A_107)
      | ~ v1_relat_1(B_106) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_433,plain,(
    ! [A_55,A_107] :
      ( k5_relat_1(k6_relat_1(A_55),k6_relat_1(A_107)) = k6_relat_1(A_55)
      | ~ r1_tarski(A_55,A_107)
      | ~ v1_relat_1(k6_relat_1(A_55)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_426])).

tff(c_676,plain,(
    ! [A_127,A_128] :
      ( k5_relat_1(k6_relat_1(A_127),k6_relat_1(A_128)) = k6_relat_1(A_127)
      | ~ r1_tarski(A_127,A_128) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_433])).

tff(c_716,plain,(
    ! [A_128,A_62] :
      ( k7_relat_1(k6_relat_1(A_128),A_62) = k6_relat_1(A_62)
      | ~ r1_tarski(A_62,A_128)
      | ~ v1_relat_1(k6_relat_1(A_128)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_676])).

tff(c_765,plain,(
    ! [A_129,A_130] :
      ( k7_relat_1(k6_relat_1(A_129),A_130) = k6_relat_1(A_130)
      | ~ r1_tarski(A_130,A_129) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_716])).

tff(c_785,plain,(
    ! [A_129,A_130] :
      ( k3_xboole_0(A_129,A_130) = k1_relat_1(k6_relat_1(A_130))
      | ~ r1_tarski(A_130,A_129) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_765,c_309])).

tff(c_830,plain,(
    ! [A_131,A_132] :
      ( k3_xboole_0(A_131,A_132) = A_132
      | ~ r1_tarski(A_132,A_131) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_785])).

tff(c_863,plain,(
    ! [A_1,B_2] : k3_xboole_0(A_1,k3_xboole_0(A_1,B_2)) = k3_xboole_0(A_1,B_2) ),
    inference(resolution,[status(thm)],[c_2,c_830])).

tff(c_24,plain,(
    ! [B_40,A_39] :
      ( k5_relat_1(B_40,k6_relat_1(A_39)) = k8_relat_1(A_39,B_40)
      | ~ v1_relat_1(B_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_218,plain,(
    ! [A_39,A_86] :
      ( k8_relat_1(A_39,k6_relat_1(A_86)) = k7_relat_1(k6_relat_1(A_39),A_86)
      | ~ v1_relat_1(k6_relat_1(A_86))
      | ~ v1_relat_1(k6_relat_1(A_39)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_211,c_24])).

tff(c_310,plain,(
    ! [A_93,A_94] : k8_relat_1(A_93,k6_relat_1(A_94)) = k7_relat_1(k6_relat_1(A_93),A_94) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_20,c_218])).

tff(c_147,plain,(
    ! [B_81,A_82] :
      ( k5_relat_1(B_81,k6_relat_1(A_82)) = k8_relat_1(A_82,B_81)
      | ~ v1_relat_1(B_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_18,plain,(
    ! [A_32,B_33] :
      ( v1_relat_1(k5_relat_1(A_32,B_33))
      | ~ v1_relat_1(B_33)
      | ~ v1_relat_1(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_168,plain,(
    ! [A_82,B_81] :
      ( v1_relat_1(k8_relat_1(A_82,B_81))
      | ~ v1_relat_1(k6_relat_1(A_82))
      | ~ v1_relat_1(B_81)
      | ~ v1_relat_1(B_81) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_147,c_18])).

tff(c_190,plain,(
    ! [A_82,B_81] :
      ( v1_relat_1(k8_relat_1(A_82,B_81))
      | ~ v1_relat_1(B_81) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_168])).

tff(c_316,plain,(
    ! [A_93,A_94] :
      ( v1_relat_1(k7_relat_1(k6_relat_1(A_93),A_94))
      | ~ v1_relat_1(k6_relat_1(A_94)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_310,c_190])).

tff(c_329,plain,(
    ! [A_93,A_94] : v1_relat_1(k7_relat_1(k6_relat_1(A_93),A_94)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_316])).

tff(c_86,plain,(
    ! [A_75] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(A_75)),A_75) = A_75
      | ~ v1_relat_1(A_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_98,plain,(
    ! [A_55] :
      ( k5_relat_1(k6_relat_1(A_55),k6_relat_1(A_55)) = k6_relat_1(A_55)
      | ~ v1_relat_1(k6_relat_1(A_55)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_86])).

tff(c_104,plain,(
    ! [A_55] : k5_relat_1(k6_relat_1(A_55),k6_relat_1(A_55)) = k6_relat_1(A_55) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_98])).

tff(c_962,plain,(
    ! [B_137,C_138,A_139] :
      ( k7_relat_1(k5_relat_1(B_137,C_138),A_139) = k5_relat_1(k7_relat_1(B_137,A_139),C_138)
      | ~ v1_relat_1(C_138)
      | ~ v1_relat_1(B_137) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_1004,plain,(
    ! [A_55,A_139] :
      ( k5_relat_1(k7_relat_1(k6_relat_1(A_55),A_139),k6_relat_1(A_55)) = k7_relat_1(k6_relat_1(A_55),A_139)
      | ~ v1_relat_1(k6_relat_1(A_55))
      | ~ v1_relat_1(k6_relat_1(A_55)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_104,c_962])).

tff(c_1075,plain,(
    ! [A_143,A_144] : k5_relat_1(k7_relat_1(k6_relat_1(A_143),A_144),k6_relat_1(A_143)) = k7_relat_1(k6_relat_1(A_143),A_144) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_20,c_1004])).

tff(c_1090,plain,(
    ! [A_143,A_144] :
      ( k8_relat_1(A_143,k7_relat_1(k6_relat_1(A_143),A_144)) = k7_relat_1(k6_relat_1(A_143),A_144)
      | ~ v1_relat_1(k7_relat_1(k6_relat_1(A_143),A_144)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1075,c_24])).

tff(c_1119,plain,(
    ! [A_143,A_144] : k8_relat_1(A_143,k7_relat_1(k6_relat_1(A_143),A_144)) = k7_relat_1(k6_relat_1(A_143),A_144) ),
    inference(demodulation,[status(thm),theory(equality)],[c_329,c_1090])).

tff(c_36,plain,(
    ! [A_56] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(A_56)),A_56) = A_56
      | ~ v1_relat_1(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_165,plain,(
    ! [A_82] :
      ( k8_relat_1(A_82,k6_relat_1(k1_relat_1(k6_relat_1(A_82)))) = k6_relat_1(A_82)
      | ~ v1_relat_1(k6_relat_1(A_82))
      | ~ v1_relat_1(k6_relat_1(k1_relat_1(k6_relat_1(A_82)))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_147,c_36])).

tff(c_188,plain,(
    ! [A_82] : k8_relat_1(A_82,k6_relat_1(A_82)) = k6_relat_1(A_82) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_20,c_32,c_165])).

tff(c_1022,plain,(
    ! [A_140,B_141,C_142] :
      ( k8_relat_1(A_140,k5_relat_1(B_141,C_142)) = k5_relat_1(B_141,k8_relat_1(A_140,C_142))
      | ~ v1_relat_1(C_142)
      | ~ v1_relat_1(B_141) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_1048,plain,(
    ! [A_62,A_140,B_63] :
      ( k5_relat_1(k6_relat_1(A_62),k8_relat_1(A_140,B_63)) = k8_relat_1(A_140,k7_relat_1(B_63,A_62))
      | ~ v1_relat_1(B_63)
      | ~ v1_relat_1(k6_relat_1(A_62))
      | ~ v1_relat_1(B_63) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_1022])).

tff(c_2327,plain,(
    ! [A_204,A_205,B_206] :
      ( k5_relat_1(k6_relat_1(A_204),k8_relat_1(A_205,B_206)) = k8_relat_1(A_205,k7_relat_1(B_206,A_204))
      | ~ v1_relat_1(B_206) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_1048])).

tff(c_2384,plain,(
    ! [A_82,A_204] :
      ( k8_relat_1(A_82,k7_relat_1(k6_relat_1(A_82),A_204)) = k5_relat_1(k6_relat_1(A_204),k6_relat_1(A_82))
      | ~ v1_relat_1(k6_relat_1(A_82)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_188,c_2327])).

tff(c_2406,plain,(
    ! [A_204,A_82] : k5_relat_1(k6_relat_1(A_204),k6_relat_1(A_82)) = k7_relat_1(k6_relat_1(A_82),A_204) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_1119,c_2384])).

tff(c_753,plain,(
    ! [A_128,A_62] :
      ( k7_relat_1(k6_relat_1(A_128),A_62) = k6_relat_1(A_62)
      | ~ r1_tarski(A_62,A_128) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_716])).

tff(c_347,plain,(
    ! [A_101,A_102] : k1_relat_1(k7_relat_1(k6_relat_1(A_101),A_102)) = k3_xboole_0(A_101,A_102) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_305])).

tff(c_356,plain,(
    ! [A_101,A_102] :
      ( k5_relat_1(k6_relat_1(k3_xboole_0(A_101,A_102)),k7_relat_1(k6_relat_1(A_101),A_102)) = k7_relat_1(k6_relat_1(A_101),A_102)
      | ~ v1_relat_1(k7_relat_1(k6_relat_1(A_101),A_102)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_347,c_36])).

tff(c_9451,plain,(
    ! [A_367,A_368] : k5_relat_1(k6_relat_1(k3_xboole_0(A_367,A_368)),k7_relat_1(k6_relat_1(A_367),A_368)) = k7_relat_1(k6_relat_1(A_367),A_368) ),
    inference(demodulation,[status(thm),theory(equality)],[c_329,c_356])).

tff(c_9540,plain,(
    ! [A_128,A_62] :
      ( k5_relat_1(k6_relat_1(k3_xboole_0(A_128,A_62)),k6_relat_1(A_62)) = k7_relat_1(k6_relat_1(A_128),A_62)
      | ~ r1_tarski(A_62,A_128) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_753,c_9451])).

tff(c_9906,plain,(
    ! [A_372,A_373] :
      ( k7_relat_1(k6_relat_1(A_372),k3_xboole_0(A_373,A_372)) = k7_relat_1(k6_relat_1(A_373),A_372)
      | ~ r1_tarski(A_372,A_373) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2406,c_9540])).

tff(c_10070,plain,(
    ! [A_1,B_2] :
      ( k7_relat_1(k6_relat_1(k3_xboole_0(A_1,B_2)),k3_xboole_0(A_1,B_2)) = k7_relat_1(k6_relat_1(A_1),k3_xboole_0(A_1,B_2))
      | ~ r1_tarski(k3_xboole_0(A_1,B_2),A_1) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_863,c_9906])).

tff(c_10152,plain,(
    ! [A_1,B_2] : k7_relat_1(k6_relat_1(A_1),k3_xboole_0(A_1,B_2)) = k6_relat_1(k3_xboole_0(A_1,B_2)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_258,c_10070])).

tff(c_256,plain,(
    ! [A_39,A_86] : k8_relat_1(A_39,k6_relat_1(A_86)) = k7_relat_1(k6_relat_1(A_39),A_86) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_20,c_218])).

tff(c_998,plain,(
    ! [B_40,A_139,A_39] :
      ( k5_relat_1(k7_relat_1(B_40,A_139),k6_relat_1(A_39)) = k7_relat_1(k8_relat_1(A_39,B_40),A_139)
      | ~ v1_relat_1(k6_relat_1(A_39))
      | ~ v1_relat_1(B_40)
      | ~ v1_relat_1(B_40) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_962])).

tff(c_4037,plain,(
    ! [B_263,A_264,A_265] :
      ( k5_relat_1(k7_relat_1(B_263,A_264),k6_relat_1(A_265)) = k7_relat_1(k8_relat_1(A_265,B_263),A_264)
      | ~ v1_relat_1(B_263) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_998])).

tff(c_4113,plain,(
    ! [A_265,A_128,A_62] :
      ( k7_relat_1(k8_relat_1(A_265,k6_relat_1(A_128)),A_62) = k5_relat_1(k6_relat_1(A_62),k6_relat_1(A_265))
      | ~ v1_relat_1(k6_relat_1(A_128))
      | ~ r1_tarski(A_62,A_128) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_753,c_4037])).

tff(c_11882,plain,(
    ! [A_389,A_390,A_391] :
      ( k7_relat_1(k7_relat_1(k6_relat_1(A_389),A_390),A_391) = k7_relat_1(k6_relat_1(A_389),A_391)
      | ~ r1_tarski(A_391,A_390) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_2406,c_256,c_4113])).

tff(c_392,plain,(
    ! [B_105] :
      ( k7_relat_1(B_105,k1_relat_1(B_105)) = B_105
      | ~ v1_relat_1(B_105)
      | ~ v1_relat_1(B_105) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_211,c_36])).

tff(c_412,plain,(
    ! [A_55,A_92] :
      ( k7_relat_1(k7_relat_1(k6_relat_1(A_55),A_92),k3_xboole_0(A_55,A_92)) = k7_relat_1(k6_relat_1(A_55),A_92)
      | ~ v1_relat_1(k7_relat_1(k6_relat_1(A_55),A_92))
      | ~ v1_relat_1(k7_relat_1(k6_relat_1(A_55),A_92)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_309,c_392])).

tff(c_423,plain,(
    ! [A_55,A_92] : k7_relat_1(k7_relat_1(k6_relat_1(A_55),A_92),k3_xboole_0(A_55,A_92)) = k7_relat_1(k6_relat_1(A_55),A_92) ),
    inference(demodulation,[status(thm),theory(equality)],[c_329,c_329,c_412])).

tff(c_11992,plain,(
    ! [A_389,A_390] :
      ( k7_relat_1(k6_relat_1(A_389),k3_xboole_0(A_389,A_390)) = k7_relat_1(k6_relat_1(A_389),A_390)
      | ~ r1_tarski(k3_xboole_0(A_389,A_390),A_390) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_11882,c_423])).

tff(c_12129,plain,(
    ! [A_389,A_390] : k7_relat_1(k6_relat_1(A_389),A_390) = k6_relat_1(k3_xboole_0(A_389,A_390)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_539,c_10152,c_11992])).

tff(c_46,plain,(
    k5_relat_1(k6_relat_1('#skF_2'),k6_relat_1('#skF_1')) != k6_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_225,plain,
    ( k7_relat_1(k6_relat_1('#skF_1'),'#skF_2') != k6_relat_1(k3_xboole_0('#skF_1','#skF_2'))
    | ~ v1_relat_1(k6_relat_1('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_211,c_46])).

tff(c_260,plain,(
    k7_relat_1(k6_relat_1('#skF_1'),'#skF_2') != k6_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_225])).

tff(c_12206,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12129,c_260])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:26:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.00/2.71  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.00/2.72  
% 8.00/2.72  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.00/2.72  %$ r1_tarski > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k8_relat_1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1
% 8.00/2.72  
% 8.00/2.72  %Foreground sorts:
% 8.00/2.72  
% 8.00/2.72  
% 8.00/2.72  %Background operators:
% 8.00/2.72  
% 8.00/2.72  
% 8.00/2.72  %Foreground operators:
% 8.00/2.72  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 8.00/2.72  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.00/2.72  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 8.00/2.72  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 8.00/2.72  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 8.00/2.72  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.00/2.72  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 8.00/2.72  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 8.00/2.72  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 8.00/2.72  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 8.00/2.72  tff('#skF_2', type, '#skF_2': $i).
% 8.00/2.72  tff('#skF_1', type, '#skF_1': $i).
% 8.00/2.72  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 8.00/2.72  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 8.00/2.72  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.00/2.72  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 8.00/2.72  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 8.00/2.72  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.00/2.72  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 8.00/2.72  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 8.00/2.72  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 8.00/2.72  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 8.00/2.72  
% 8.12/2.74  tff(f_49, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 8.12/2.74  tff(f_88, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 8.12/2.74  tff(f_106, axiom, (![A, B]: (v1_relat_1(B) => (k1_relat_1(k7_relat_1(B, A)) = k3_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t90_relat_1)).
% 8.12/2.74  tff(f_110, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_relat_1)).
% 8.12/2.74  tff(f_74, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k5_relat_1(A, B)), k1_relat_1(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_relat_1)).
% 8.12/2.74  tff(f_27, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 8.12/2.74  tff(f_102, axiom, (![A]: (v1_relat_1(A) => (k5_relat_1(A, k6_relat_1(k2_relat_1(A))) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t80_relat_1)).
% 8.12/2.74  tff(f_98, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k5_relat_1(B, k6_relat_1(A)) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_relat_1)).
% 8.12/2.74  tff(f_60, axiom, (![A, B]: (v1_relat_1(B) => (k8_relat_1(A, B) = k5_relat_1(B, k6_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t123_relat_1)).
% 8.12/2.74  tff(f_47, axiom, (![A, B]: ((v1_relat_1(A) & v1_relat_1(B)) => v1_relat_1(k5_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k5_relat_1)).
% 8.12/2.74  tff(f_92, axiom, (![A]: (v1_relat_1(A) => (k5_relat_1(k6_relat_1(k1_relat_1(A)), A) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t78_relat_1)).
% 8.12/2.74  tff(f_56, axiom, (![A, B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (k7_relat_1(k5_relat_1(B, C), A) = k5_relat_1(k7_relat_1(B, A), C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t112_relat_1)).
% 8.12/2.74  tff(f_67, axiom, (![A, B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (k8_relat_1(A, k5_relat_1(B, C)) = k5_relat_1(B, k8_relat_1(A, C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t139_relat_1)).
% 8.12/2.74  tff(f_113, negated_conjecture, ~(![A, B]: (k5_relat_1(k6_relat_1(B), k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_funct_1)).
% 8.12/2.74  tff(c_20, plain, (![A_34]: (v1_relat_1(k6_relat_1(A_34)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 8.12/2.74  tff(c_32, plain, (![A_55]: (k1_relat_1(k6_relat_1(A_55))=A_55)), inference(cnfTransformation, [status(thm)], [f_88])).
% 8.12/2.74  tff(c_293, plain, (![B_91, A_92]: (k3_xboole_0(k1_relat_1(B_91), A_92)=k1_relat_1(k7_relat_1(B_91, A_92)) | ~v1_relat_1(B_91))), inference(cnfTransformation, [status(thm)], [f_106])).
% 8.12/2.74  tff(c_305, plain, (![A_55, A_92]: (k1_relat_1(k7_relat_1(k6_relat_1(A_55), A_92))=k3_xboole_0(A_55, A_92) | ~v1_relat_1(k6_relat_1(A_55)))), inference(superposition, [status(thm), theory('equality')], [c_32, c_293])).
% 8.12/2.74  tff(c_309, plain, (![A_55, A_92]: (k1_relat_1(k7_relat_1(k6_relat_1(A_55), A_92))=k3_xboole_0(A_55, A_92))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_305])).
% 8.12/2.74  tff(c_44, plain, (![A_62, B_63]: (k5_relat_1(k6_relat_1(A_62), B_63)=k7_relat_1(B_63, A_62) | ~v1_relat_1(B_63))), inference(cnfTransformation, [status(thm)], [f_110])).
% 8.12/2.74  tff(c_491, plain, (![A_111, B_112]: (r1_tarski(k1_relat_1(k5_relat_1(A_111, B_112)), k1_relat_1(A_111)) | ~v1_relat_1(B_112) | ~v1_relat_1(A_111))), inference(cnfTransformation, [status(thm)], [f_74])).
% 8.12/2.74  tff(c_497, plain, (![B_63, A_62]: (r1_tarski(k1_relat_1(k7_relat_1(B_63, A_62)), k1_relat_1(k6_relat_1(A_62))) | ~v1_relat_1(B_63) | ~v1_relat_1(k6_relat_1(A_62)) | ~v1_relat_1(B_63))), inference(superposition, [status(thm), theory('equality')], [c_44, c_491])).
% 8.12/2.74  tff(c_527, plain, (![B_113, A_114]: (r1_tarski(k1_relat_1(k7_relat_1(B_113, A_114)), A_114) | ~v1_relat_1(B_113))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_32, c_497])).
% 8.12/2.74  tff(c_533, plain, (![A_55, A_92]: (r1_tarski(k3_xboole_0(A_55, A_92), A_92) | ~v1_relat_1(k6_relat_1(A_55)))), inference(superposition, [status(thm), theory('equality')], [c_309, c_527])).
% 8.12/2.74  tff(c_539, plain, (![A_55, A_92]: (r1_tarski(k3_xboole_0(A_55, A_92), A_92))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_533])).
% 8.12/2.74  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(k3_xboole_0(A_1, B_2), A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 8.12/2.74  tff(c_34, plain, (![A_55]: (k2_relat_1(k6_relat_1(A_55))=A_55)), inference(cnfTransformation, [status(thm)], [f_88])).
% 8.12/2.74  tff(c_211, plain, (![A_86, B_87]: (k5_relat_1(k6_relat_1(A_86), B_87)=k7_relat_1(B_87, A_86) | ~v1_relat_1(B_87))), inference(cnfTransformation, [status(thm)], [f_110])).
% 8.12/2.74  tff(c_40, plain, (![A_59]: (k5_relat_1(A_59, k6_relat_1(k2_relat_1(A_59)))=A_59 | ~v1_relat_1(A_59))), inference(cnfTransformation, [status(thm)], [f_102])).
% 8.12/2.74  tff(c_222, plain, (![A_86]: (k7_relat_1(k6_relat_1(k2_relat_1(k6_relat_1(A_86))), A_86)=k6_relat_1(A_86) | ~v1_relat_1(k6_relat_1(A_86)) | ~v1_relat_1(k6_relat_1(k2_relat_1(k6_relat_1(A_86)))))), inference(superposition, [status(thm), theory('equality')], [c_211, c_40])).
% 8.12/2.74  tff(c_258, plain, (![A_86]: (k7_relat_1(k6_relat_1(A_86), A_86)=k6_relat_1(A_86))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_20, c_34, c_222])).
% 8.12/2.74  tff(c_426, plain, (![B_106, A_107]: (k5_relat_1(B_106, k6_relat_1(A_107))=B_106 | ~r1_tarski(k2_relat_1(B_106), A_107) | ~v1_relat_1(B_106))), inference(cnfTransformation, [status(thm)], [f_98])).
% 8.12/2.74  tff(c_433, plain, (![A_55, A_107]: (k5_relat_1(k6_relat_1(A_55), k6_relat_1(A_107))=k6_relat_1(A_55) | ~r1_tarski(A_55, A_107) | ~v1_relat_1(k6_relat_1(A_55)))), inference(superposition, [status(thm), theory('equality')], [c_34, c_426])).
% 8.12/2.74  tff(c_676, plain, (![A_127, A_128]: (k5_relat_1(k6_relat_1(A_127), k6_relat_1(A_128))=k6_relat_1(A_127) | ~r1_tarski(A_127, A_128))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_433])).
% 8.12/2.74  tff(c_716, plain, (![A_128, A_62]: (k7_relat_1(k6_relat_1(A_128), A_62)=k6_relat_1(A_62) | ~r1_tarski(A_62, A_128) | ~v1_relat_1(k6_relat_1(A_128)))), inference(superposition, [status(thm), theory('equality')], [c_44, c_676])).
% 8.12/2.74  tff(c_765, plain, (![A_129, A_130]: (k7_relat_1(k6_relat_1(A_129), A_130)=k6_relat_1(A_130) | ~r1_tarski(A_130, A_129))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_716])).
% 8.12/2.74  tff(c_785, plain, (![A_129, A_130]: (k3_xboole_0(A_129, A_130)=k1_relat_1(k6_relat_1(A_130)) | ~r1_tarski(A_130, A_129))), inference(superposition, [status(thm), theory('equality')], [c_765, c_309])).
% 8.12/2.74  tff(c_830, plain, (![A_131, A_132]: (k3_xboole_0(A_131, A_132)=A_132 | ~r1_tarski(A_132, A_131))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_785])).
% 8.12/2.74  tff(c_863, plain, (![A_1, B_2]: (k3_xboole_0(A_1, k3_xboole_0(A_1, B_2))=k3_xboole_0(A_1, B_2))), inference(resolution, [status(thm)], [c_2, c_830])).
% 8.12/2.74  tff(c_24, plain, (![B_40, A_39]: (k5_relat_1(B_40, k6_relat_1(A_39))=k8_relat_1(A_39, B_40) | ~v1_relat_1(B_40))), inference(cnfTransformation, [status(thm)], [f_60])).
% 8.12/2.74  tff(c_218, plain, (![A_39, A_86]: (k8_relat_1(A_39, k6_relat_1(A_86))=k7_relat_1(k6_relat_1(A_39), A_86) | ~v1_relat_1(k6_relat_1(A_86)) | ~v1_relat_1(k6_relat_1(A_39)))), inference(superposition, [status(thm), theory('equality')], [c_211, c_24])).
% 8.12/2.74  tff(c_310, plain, (![A_93, A_94]: (k8_relat_1(A_93, k6_relat_1(A_94))=k7_relat_1(k6_relat_1(A_93), A_94))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_20, c_218])).
% 8.12/2.74  tff(c_147, plain, (![B_81, A_82]: (k5_relat_1(B_81, k6_relat_1(A_82))=k8_relat_1(A_82, B_81) | ~v1_relat_1(B_81))), inference(cnfTransformation, [status(thm)], [f_60])).
% 8.12/2.74  tff(c_18, plain, (![A_32, B_33]: (v1_relat_1(k5_relat_1(A_32, B_33)) | ~v1_relat_1(B_33) | ~v1_relat_1(A_32))), inference(cnfTransformation, [status(thm)], [f_47])).
% 8.12/2.74  tff(c_168, plain, (![A_82, B_81]: (v1_relat_1(k8_relat_1(A_82, B_81)) | ~v1_relat_1(k6_relat_1(A_82)) | ~v1_relat_1(B_81) | ~v1_relat_1(B_81))), inference(superposition, [status(thm), theory('equality')], [c_147, c_18])).
% 8.12/2.74  tff(c_190, plain, (![A_82, B_81]: (v1_relat_1(k8_relat_1(A_82, B_81)) | ~v1_relat_1(B_81))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_168])).
% 8.12/2.74  tff(c_316, plain, (![A_93, A_94]: (v1_relat_1(k7_relat_1(k6_relat_1(A_93), A_94)) | ~v1_relat_1(k6_relat_1(A_94)))), inference(superposition, [status(thm), theory('equality')], [c_310, c_190])).
% 8.12/2.74  tff(c_329, plain, (![A_93, A_94]: (v1_relat_1(k7_relat_1(k6_relat_1(A_93), A_94)))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_316])).
% 8.12/2.74  tff(c_86, plain, (![A_75]: (k5_relat_1(k6_relat_1(k1_relat_1(A_75)), A_75)=A_75 | ~v1_relat_1(A_75))), inference(cnfTransformation, [status(thm)], [f_92])).
% 8.12/2.74  tff(c_98, plain, (![A_55]: (k5_relat_1(k6_relat_1(A_55), k6_relat_1(A_55))=k6_relat_1(A_55) | ~v1_relat_1(k6_relat_1(A_55)))), inference(superposition, [status(thm), theory('equality')], [c_32, c_86])).
% 8.12/2.74  tff(c_104, plain, (![A_55]: (k5_relat_1(k6_relat_1(A_55), k6_relat_1(A_55))=k6_relat_1(A_55))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_98])).
% 8.12/2.74  tff(c_962, plain, (![B_137, C_138, A_139]: (k7_relat_1(k5_relat_1(B_137, C_138), A_139)=k5_relat_1(k7_relat_1(B_137, A_139), C_138) | ~v1_relat_1(C_138) | ~v1_relat_1(B_137))), inference(cnfTransformation, [status(thm)], [f_56])).
% 8.12/2.74  tff(c_1004, plain, (![A_55, A_139]: (k5_relat_1(k7_relat_1(k6_relat_1(A_55), A_139), k6_relat_1(A_55))=k7_relat_1(k6_relat_1(A_55), A_139) | ~v1_relat_1(k6_relat_1(A_55)) | ~v1_relat_1(k6_relat_1(A_55)))), inference(superposition, [status(thm), theory('equality')], [c_104, c_962])).
% 8.12/2.74  tff(c_1075, plain, (![A_143, A_144]: (k5_relat_1(k7_relat_1(k6_relat_1(A_143), A_144), k6_relat_1(A_143))=k7_relat_1(k6_relat_1(A_143), A_144))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_20, c_1004])).
% 8.12/2.74  tff(c_1090, plain, (![A_143, A_144]: (k8_relat_1(A_143, k7_relat_1(k6_relat_1(A_143), A_144))=k7_relat_1(k6_relat_1(A_143), A_144) | ~v1_relat_1(k7_relat_1(k6_relat_1(A_143), A_144)))), inference(superposition, [status(thm), theory('equality')], [c_1075, c_24])).
% 8.12/2.74  tff(c_1119, plain, (![A_143, A_144]: (k8_relat_1(A_143, k7_relat_1(k6_relat_1(A_143), A_144))=k7_relat_1(k6_relat_1(A_143), A_144))), inference(demodulation, [status(thm), theory('equality')], [c_329, c_1090])).
% 8.12/2.74  tff(c_36, plain, (![A_56]: (k5_relat_1(k6_relat_1(k1_relat_1(A_56)), A_56)=A_56 | ~v1_relat_1(A_56))), inference(cnfTransformation, [status(thm)], [f_92])).
% 8.12/2.74  tff(c_165, plain, (![A_82]: (k8_relat_1(A_82, k6_relat_1(k1_relat_1(k6_relat_1(A_82))))=k6_relat_1(A_82) | ~v1_relat_1(k6_relat_1(A_82)) | ~v1_relat_1(k6_relat_1(k1_relat_1(k6_relat_1(A_82)))))), inference(superposition, [status(thm), theory('equality')], [c_147, c_36])).
% 8.12/2.74  tff(c_188, plain, (![A_82]: (k8_relat_1(A_82, k6_relat_1(A_82))=k6_relat_1(A_82))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_20, c_32, c_165])).
% 8.12/2.74  tff(c_1022, plain, (![A_140, B_141, C_142]: (k8_relat_1(A_140, k5_relat_1(B_141, C_142))=k5_relat_1(B_141, k8_relat_1(A_140, C_142)) | ~v1_relat_1(C_142) | ~v1_relat_1(B_141))), inference(cnfTransformation, [status(thm)], [f_67])).
% 8.12/2.74  tff(c_1048, plain, (![A_62, A_140, B_63]: (k5_relat_1(k6_relat_1(A_62), k8_relat_1(A_140, B_63))=k8_relat_1(A_140, k7_relat_1(B_63, A_62)) | ~v1_relat_1(B_63) | ~v1_relat_1(k6_relat_1(A_62)) | ~v1_relat_1(B_63))), inference(superposition, [status(thm), theory('equality')], [c_44, c_1022])).
% 8.12/2.74  tff(c_2327, plain, (![A_204, A_205, B_206]: (k5_relat_1(k6_relat_1(A_204), k8_relat_1(A_205, B_206))=k8_relat_1(A_205, k7_relat_1(B_206, A_204)) | ~v1_relat_1(B_206))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_1048])).
% 8.12/2.74  tff(c_2384, plain, (![A_82, A_204]: (k8_relat_1(A_82, k7_relat_1(k6_relat_1(A_82), A_204))=k5_relat_1(k6_relat_1(A_204), k6_relat_1(A_82)) | ~v1_relat_1(k6_relat_1(A_82)))), inference(superposition, [status(thm), theory('equality')], [c_188, c_2327])).
% 8.12/2.74  tff(c_2406, plain, (![A_204, A_82]: (k5_relat_1(k6_relat_1(A_204), k6_relat_1(A_82))=k7_relat_1(k6_relat_1(A_82), A_204))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_1119, c_2384])).
% 8.12/2.74  tff(c_753, plain, (![A_128, A_62]: (k7_relat_1(k6_relat_1(A_128), A_62)=k6_relat_1(A_62) | ~r1_tarski(A_62, A_128))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_716])).
% 8.12/2.74  tff(c_347, plain, (![A_101, A_102]: (k1_relat_1(k7_relat_1(k6_relat_1(A_101), A_102))=k3_xboole_0(A_101, A_102))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_305])).
% 8.12/2.74  tff(c_356, plain, (![A_101, A_102]: (k5_relat_1(k6_relat_1(k3_xboole_0(A_101, A_102)), k7_relat_1(k6_relat_1(A_101), A_102))=k7_relat_1(k6_relat_1(A_101), A_102) | ~v1_relat_1(k7_relat_1(k6_relat_1(A_101), A_102)))), inference(superposition, [status(thm), theory('equality')], [c_347, c_36])).
% 8.12/2.74  tff(c_9451, plain, (![A_367, A_368]: (k5_relat_1(k6_relat_1(k3_xboole_0(A_367, A_368)), k7_relat_1(k6_relat_1(A_367), A_368))=k7_relat_1(k6_relat_1(A_367), A_368))), inference(demodulation, [status(thm), theory('equality')], [c_329, c_356])).
% 8.12/2.74  tff(c_9540, plain, (![A_128, A_62]: (k5_relat_1(k6_relat_1(k3_xboole_0(A_128, A_62)), k6_relat_1(A_62))=k7_relat_1(k6_relat_1(A_128), A_62) | ~r1_tarski(A_62, A_128))), inference(superposition, [status(thm), theory('equality')], [c_753, c_9451])).
% 8.12/2.74  tff(c_9906, plain, (![A_372, A_373]: (k7_relat_1(k6_relat_1(A_372), k3_xboole_0(A_373, A_372))=k7_relat_1(k6_relat_1(A_373), A_372) | ~r1_tarski(A_372, A_373))), inference(demodulation, [status(thm), theory('equality')], [c_2406, c_9540])).
% 8.12/2.74  tff(c_10070, plain, (![A_1, B_2]: (k7_relat_1(k6_relat_1(k3_xboole_0(A_1, B_2)), k3_xboole_0(A_1, B_2))=k7_relat_1(k6_relat_1(A_1), k3_xboole_0(A_1, B_2)) | ~r1_tarski(k3_xboole_0(A_1, B_2), A_1))), inference(superposition, [status(thm), theory('equality')], [c_863, c_9906])).
% 8.12/2.74  tff(c_10152, plain, (![A_1, B_2]: (k7_relat_1(k6_relat_1(A_1), k3_xboole_0(A_1, B_2))=k6_relat_1(k3_xboole_0(A_1, B_2)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_258, c_10070])).
% 8.12/2.74  tff(c_256, plain, (![A_39, A_86]: (k8_relat_1(A_39, k6_relat_1(A_86))=k7_relat_1(k6_relat_1(A_39), A_86))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_20, c_218])).
% 8.12/2.74  tff(c_998, plain, (![B_40, A_139, A_39]: (k5_relat_1(k7_relat_1(B_40, A_139), k6_relat_1(A_39))=k7_relat_1(k8_relat_1(A_39, B_40), A_139) | ~v1_relat_1(k6_relat_1(A_39)) | ~v1_relat_1(B_40) | ~v1_relat_1(B_40))), inference(superposition, [status(thm), theory('equality')], [c_24, c_962])).
% 8.12/2.74  tff(c_4037, plain, (![B_263, A_264, A_265]: (k5_relat_1(k7_relat_1(B_263, A_264), k6_relat_1(A_265))=k7_relat_1(k8_relat_1(A_265, B_263), A_264) | ~v1_relat_1(B_263))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_998])).
% 8.12/2.74  tff(c_4113, plain, (![A_265, A_128, A_62]: (k7_relat_1(k8_relat_1(A_265, k6_relat_1(A_128)), A_62)=k5_relat_1(k6_relat_1(A_62), k6_relat_1(A_265)) | ~v1_relat_1(k6_relat_1(A_128)) | ~r1_tarski(A_62, A_128))), inference(superposition, [status(thm), theory('equality')], [c_753, c_4037])).
% 8.12/2.74  tff(c_11882, plain, (![A_389, A_390, A_391]: (k7_relat_1(k7_relat_1(k6_relat_1(A_389), A_390), A_391)=k7_relat_1(k6_relat_1(A_389), A_391) | ~r1_tarski(A_391, A_390))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_2406, c_256, c_4113])).
% 8.12/2.74  tff(c_392, plain, (![B_105]: (k7_relat_1(B_105, k1_relat_1(B_105))=B_105 | ~v1_relat_1(B_105) | ~v1_relat_1(B_105))), inference(superposition, [status(thm), theory('equality')], [c_211, c_36])).
% 8.12/2.74  tff(c_412, plain, (![A_55, A_92]: (k7_relat_1(k7_relat_1(k6_relat_1(A_55), A_92), k3_xboole_0(A_55, A_92))=k7_relat_1(k6_relat_1(A_55), A_92) | ~v1_relat_1(k7_relat_1(k6_relat_1(A_55), A_92)) | ~v1_relat_1(k7_relat_1(k6_relat_1(A_55), A_92)))), inference(superposition, [status(thm), theory('equality')], [c_309, c_392])).
% 8.12/2.74  tff(c_423, plain, (![A_55, A_92]: (k7_relat_1(k7_relat_1(k6_relat_1(A_55), A_92), k3_xboole_0(A_55, A_92))=k7_relat_1(k6_relat_1(A_55), A_92))), inference(demodulation, [status(thm), theory('equality')], [c_329, c_329, c_412])).
% 8.12/2.74  tff(c_11992, plain, (![A_389, A_390]: (k7_relat_1(k6_relat_1(A_389), k3_xboole_0(A_389, A_390))=k7_relat_1(k6_relat_1(A_389), A_390) | ~r1_tarski(k3_xboole_0(A_389, A_390), A_390))), inference(superposition, [status(thm), theory('equality')], [c_11882, c_423])).
% 8.12/2.74  tff(c_12129, plain, (![A_389, A_390]: (k7_relat_1(k6_relat_1(A_389), A_390)=k6_relat_1(k3_xboole_0(A_389, A_390)))), inference(demodulation, [status(thm), theory('equality')], [c_539, c_10152, c_11992])).
% 8.12/2.74  tff(c_46, plain, (k5_relat_1(k6_relat_1('#skF_2'), k6_relat_1('#skF_1'))!=k6_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_113])).
% 8.12/2.74  tff(c_225, plain, (k7_relat_1(k6_relat_1('#skF_1'), '#skF_2')!=k6_relat_1(k3_xboole_0('#skF_1', '#skF_2')) | ~v1_relat_1(k6_relat_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_211, c_46])).
% 8.12/2.74  tff(c_260, plain, (k7_relat_1(k6_relat_1('#skF_1'), '#skF_2')!=k6_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_225])).
% 8.12/2.74  tff(c_12206, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12129, c_260])).
% 8.12/2.74  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.12/2.74  
% 8.12/2.74  Inference rules
% 8.12/2.74  ----------------------
% 8.12/2.74  #Ref     : 0
% 8.12/2.74  #Sup     : 2754
% 8.12/2.74  #Fact    : 0
% 8.12/2.74  #Define  : 0
% 8.12/2.74  #Split   : 1
% 8.12/2.74  #Chain   : 0
% 8.12/2.74  #Close   : 0
% 8.12/2.74  
% 8.12/2.74  Ordering : KBO
% 8.12/2.74  
% 8.12/2.74  Simplification rules
% 8.12/2.74  ----------------------
% 8.12/2.74  #Subsume      : 359
% 8.12/2.74  #Demod        : 4260
% 8.12/2.74  #Tautology    : 1214
% 8.12/2.74  #SimpNegUnit  : 0
% 8.12/2.74  #BackRed      : 37
% 8.12/2.74  
% 8.12/2.74  #Partial instantiations: 0
% 8.12/2.74  #Strategies tried      : 1
% 8.12/2.74  
% 8.12/2.74  Timing (in seconds)
% 8.12/2.74  ----------------------
% 8.12/2.75  Preprocessing        : 0.34
% 8.12/2.75  Parsing              : 0.18
% 8.12/2.75  CNF conversion       : 0.02
% 8.12/2.75  Main loop            : 1.61
% 8.12/2.75  Inferencing          : 0.51
% 8.12/2.75  Reduction            : 0.64
% 8.12/2.75  Demodulation         : 0.51
% 8.12/2.75  BG Simplification    : 0.08
% 8.12/2.75  Subsumption          : 0.29
% 8.12/2.75  Abstraction          : 0.10
% 8.12/2.75  MUC search           : 0.00
% 8.12/2.75  Cooper               : 0.00
% 8.12/2.75  Total                : 1.98
% 8.12/2.75  Index Insertion      : 0.00
% 8.12/2.75  Index Deletion       : 0.00
% 8.12/2.75  Index Matching       : 0.00
% 8.12/2.75  BG Taut test         : 0.00
%------------------------------------------------------------------------------

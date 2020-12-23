%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:03:26 EST 2020

% Result     : Theorem 6.97s
% Output     : CNFRefutation 6.97s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 211 expanded)
%              Number of leaves         :   36 (  91 expanded)
%              Depth                    :   11
%              Number of atoms          :  117 ( 316 expanded)
%              Number of equality atoms :   46 ( 119 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k8_relat_1 > k7_relat_1 > k5_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k8_relat_1,type,(
    k8_relat_1: ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

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

tff(f_29,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_43,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_51,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_73,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_91,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k1_relat_1(k7_relat_1(B,A)) = k3_xboole_0(k1_relat_1(B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_relat_1)).

tff(f_95,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k5_relat_1(k6_relat_1(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).

tff(f_69,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => r1_tarski(k1_relat_1(k5_relat_1(A,B)),k1_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_relat_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k8_relat_1(A,B) = k5_relat_1(B,k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_relat_1)).

tff(f_83,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k2_relat_1(B),A)
       => k5_relat_1(B,k6_relat_1(A)) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_relat_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_relat_1(B) )
     => v1_relat_1(k5_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).

tff(f_62,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ! [C] :
          ( v1_relat_1(C)
         => k8_relat_1(A,k5_relat_1(B,C)) = k5_relat_1(B,k8_relat_1(A,C)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t139_relat_1)).

tff(f_77,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k5_relat_1(k6_relat_1(k1_relat_1(A)),A) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_relat_1)).

tff(f_98,negated_conjecture,(
    ~ ! [A,B] : k5_relat_1(k6_relat_1(B),k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_funct_1)).

tff(c_4,plain,(
    ! [B_4,A_3] : k2_tarski(B_4,A_3) = k2_tarski(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_106,plain,(
    ! [A_62,B_63] : k1_setfam_1(k2_tarski(A_62,B_63)) = k3_xboole_0(A_62,B_63) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_121,plain,(
    ! [B_64,A_65] : k1_setfam_1(k2_tarski(B_64,A_65)) = k3_xboole_0(A_65,B_64) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_106])).

tff(c_18,plain,(
    ! [A_32,B_33] : k1_setfam_1(k2_tarski(A_32,B_33)) = k3_xboole_0(A_32,B_33) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_127,plain,(
    ! [B_64,A_65] : k3_xboole_0(B_64,A_65) = k3_xboole_0(A_65,B_64) ),
    inference(superposition,[status(thm),theory(equality)],[c_121,c_18])).

tff(c_22,plain,(
    ! [A_36] : v1_relat_1(k6_relat_1(A_36)) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_30,plain,(
    ! [A_46] : k1_relat_1(k6_relat_1(A_46)) = A_46 ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_383,plain,(
    ! [B_85,A_86] :
      ( k3_xboole_0(k1_relat_1(B_85),A_86) = k1_relat_1(k7_relat_1(B_85,A_86))
      | ~ v1_relat_1(B_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_406,plain,(
    ! [A_46,A_86] :
      ( k1_relat_1(k7_relat_1(k6_relat_1(A_46),A_86)) = k3_xboole_0(A_46,A_86)
      | ~ v1_relat_1(k6_relat_1(A_46)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_383])).

tff(c_410,plain,(
    ! [A_46,A_86] : k1_relat_1(k7_relat_1(k6_relat_1(A_46),A_86)) = k3_xboole_0(A_46,A_86) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_406])).

tff(c_42,plain,(
    ! [A_53,B_54] :
      ( k5_relat_1(k6_relat_1(A_53),B_54) = k7_relat_1(B_54,A_53)
      | ~ v1_relat_1(B_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_529,plain,(
    ! [A_100,B_101] :
      ( r1_tarski(k1_relat_1(k5_relat_1(A_100,B_101)),k1_relat_1(A_100))
      | ~ v1_relat_1(B_101)
      | ~ v1_relat_1(A_100) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_538,plain,(
    ! [B_54,A_53] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_54,A_53)),k1_relat_1(k6_relat_1(A_53)))
      | ~ v1_relat_1(B_54)
      | ~ v1_relat_1(k6_relat_1(A_53))
      | ~ v1_relat_1(B_54) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_529])).

tff(c_573,plain,(
    ! [B_103,A_104] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_103,A_104)),A_104)
      | ~ v1_relat_1(B_103) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_30,c_538])).

tff(c_576,plain,(
    ! [A_46,A_86] :
      ( r1_tarski(k3_xboole_0(A_46,A_86),A_86)
      | ~ v1_relat_1(k6_relat_1(A_46)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_410,c_573])).

tff(c_584,plain,(
    ! [A_105,A_106] : r1_tarski(k3_xboole_0(A_105,A_106),A_106) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_576])).

tff(c_593,plain,(
    ! [B_64,A_65] : r1_tarski(k3_xboole_0(B_64,A_65),B_64) ),
    inference(superposition,[status(thm),theory(equality)],[c_127,c_584])).

tff(c_581,plain,(
    ! [A_46,A_86] : r1_tarski(k3_xboole_0(A_46,A_86),A_86) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_576])).

tff(c_322,plain,(
    ! [B_83,A_84] :
      ( k5_relat_1(B_83,k6_relat_1(A_84)) = k8_relat_1(A_84,B_83)
      | ~ v1_relat_1(B_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_354,plain,(
    ! [A_84,A_53] :
      ( k8_relat_1(A_84,k6_relat_1(A_53)) = k7_relat_1(k6_relat_1(A_84),A_53)
      | ~ v1_relat_1(k6_relat_1(A_53))
      | ~ v1_relat_1(k6_relat_1(A_84)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_322])).

tff(c_378,plain,(
    ! [A_84,A_53] : k8_relat_1(A_84,k6_relat_1(A_53)) = k7_relat_1(k6_relat_1(A_84),A_53) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_22,c_354])).

tff(c_32,plain,(
    ! [A_46] : k2_relat_1(k6_relat_1(A_46)) = A_46 ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_489,plain,(
    ! [B_95,A_96] :
      ( k5_relat_1(B_95,k6_relat_1(A_96)) = B_95
      | ~ r1_tarski(k2_relat_1(B_95),A_96)
      | ~ v1_relat_1(B_95) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_492,plain,(
    ! [A_46,A_96] :
      ( k5_relat_1(k6_relat_1(A_46),k6_relat_1(A_96)) = k6_relat_1(A_46)
      | ~ r1_tarski(A_46,A_96)
      | ~ v1_relat_1(k6_relat_1(A_46)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_489])).

tff(c_924,plain,(
    ! [A_139,A_140] :
      ( k5_relat_1(k6_relat_1(A_139),k6_relat_1(A_140)) = k6_relat_1(A_139)
      | ~ r1_tarski(A_139,A_140) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_492])).

tff(c_24,plain,(
    ! [B_38,A_37] :
      ( k5_relat_1(B_38,k6_relat_1(A_37)) = k8_relat_1(A_37,B_38)
      | ~ v1_relat_1(B_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_939,plain,(
    ! [A_140,A_139] :
      ( k8_relat_1(A_140,k6_relat_1(A_139)) = k6_relat_1(A_139)
      | ~ v1_relat_1(k6_relat_1(A_139))
      | ~ r1_tarski(A_139,A_140) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_924,c_24])).

tff(c_991,plain,(
    ! [A_140,A_139] :
      ( k7_relat_1(k6_relat_1(A_140),A_139) = k6_relat_1(A_139)
      | ~ r1_tarski(A_139,A_140) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_378,c_939])).

tff(c_466,plain,(
    ! [A_93,A_94] : k8_relat_1(A_93,k6_relat_1(A_94)) = k7_relat_1(k6_relat_1(A_93),A_94) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_22,c_354])).

tff(c_20,plain,(
    ! [A_34,B_35] :
      ( v1_relat_1(k5_relat_1(A_34,B_35))
      | ~ v1_relat_1(B_35)
      | ~ v1_relat_1(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_332,plain,(
    ! [A_84,B_83] :
      ( v1_relat_1(k8_relat_1(A_84,B_83))
      | ~ v1_relat_1(k6_relat_1(A_84))
      | ~ v1_relat_1(B_83)
      | ~ v1_relat_1(B_83) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_322,c_20])).

tff(c_369,plain,(
    ! [A_84,B_83] :
      ( v1_relat_1(k8_relat_1(A_84,B_83))
      | ~ v1_relat_1(B_83) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_332])).

tff(c_476,plain,(
    ! [A_93,A_94] :
      ( v1_relat_1(k7_relat_1(k6_relat_1(A_93),A_94))
      | ~ v1_relat_1(k6_relat_1(A_94)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_466,c_369])).

tff(c_486,plain,(
    ! [A_93,A_94] : v1_relat_1(k7_relat_1(k6_relat_1(A_93),A_94)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_476])).

tff(c_781,plain,(
    ! [A_124,B_125,C_126] :
      ( k8_relat_1(A_124,k5_relat_1(B_125,C_126)) = k5_relat_1(B_125,k8_relat_1(A_124,C_126))
      | ~ v1_relat_1(C_126)
      | ~ v1_relat_1(B_125) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_804,plain,(
    ! [B_38,A_124,A_37] :
      ( k5_relat_1(B_38,k8_relat_1(A_124,k6_relat_1(A_37))) = k8_relat_1(A_124,k8_relat_1(A_37,B_38))
      | ~ v1_relat_1(k6_relat_1(A_37))
      | ~ v1_relat_1(B_38)
      | ~ v1_relat_1(B_38) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_781])).

tff(c_2406,plain,(
    ! [B_180,A_181,A_182] :
      ( k5_relat_1(B_180,k7_relat_1(k6_relat_1(A_181),A_182)) = k8_relat_1(A_181,k8_relat_1(A_182,B_180))
      | ~ v1_relat_1(B_180) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_378,c_804])).

tff(c_34,plain,(
    ! [A_47] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(A_47)),A_47) = A_47
      | ~ v1_relat_1(A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_2434,plain,(
    ! [A_181,A_182] :
      ( k8_relat_1(A_181,k8_relat_1(A_182,k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(A_181),A_182))))) = k7_relat_1(k6_relat_1(A_181),A_182)
      | ~ v1_relat_1(k7_relat_1(k6_relat_1(A_181),A_182))
      | ~ v1_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(A_181),A_182)))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2406,c_34])).

tff(c_9729,plain,(
    ! [A_338,A_339] : k8_relat_1(A_338,k7_relat_1(k6_relat_1(A_339),k3_xboole_0(A_338,A_339))) = k7_relat_1(k6_relat_1(A_338),A_339) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_486,c_378,c_410,c_2434])).

tff(c_9823,plain,(
    ! [A_338,A_140] :
      ( k8_relat_1(A_338,k6_relat_1(k3_xboole_0(A_338,A_140))) = k7_relat_1(k6_relat_1(A_338),A_140)
      | ~ r1_tarski(k3_xboole_0(A_338,A_140),A_140) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_991,c_9729])).

tff(c_9872,plain,(
    ! [A_340,A_341] : k7_relat_1(k6_relat_1(A_340),k3_xboole_0(A_340,A_341)) = k7_relat_1(k6_relat_1(A_340),A_341) ),
    inference(demodulation,[status(thm),theory(equality)],[c_581,c_378,c_9823])).

tff(c_9960,plain,(
    ! [A_340,A_341] :
      ( k7_relat_1(k6_relat_1(A_340),A_341) = k6_relat_1(k3_xboole_0(A_340,A_341))
      | ~ r1_tarski(k3_xboole_0(A_340,A_341),A_340) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_9872,c_991])).

tff(c_10084,plain,(
    ! [A_340,A_341] : k7_relat_1(k6_relat_1(A_340),A_341) = k6_relat_1(k3_xboole_0(A_340,A_341)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_593,c_9960])).

tff(c_255,plain,(
    ! [A_78,B_79] :
      ( k5_relat_1(k6_relat_1(A_78),B_79) = k7_relat_1(B_79,A_78)
      | ~ v1_relat_1(B_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_44,plain,(
    k5_relat_1(k6_relat_1('#skF_2'),k6_relat_1('#skF_1')) != k6_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_276,plain,
    ( k7_relat_1(k6_relat_1('#skF_1'),'#skF_2') != k6_relat_1(k3_xboole_0('#skF_1','#skF_2'))
    | ~ v1_relat_1(k6_relat_1('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_255,c_44])).

tff(c_298,plain,(
    k7_relat_1(k6_relat_1('#skF_1'),'#skF_2') != k6_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_276])).

tff(c_10146,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_10084,c_298])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n016.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:08:49 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.97/2.51  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.97/2.51  
% 6.97/2.51  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.97/2.51  %$ r1_tarski > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k8_relat_1 > k7_relat_1 > k5_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1
% 6.97/2.51  
% 6.97/2.51  %Foreground sorts:
% 6.97/2.51  
% 6.97/2.51  
% 6.97/2.51  %Background operators:
% 6.97/2.51  
% 6.97/2.51  
% 6.97/2.51  %Foreground operators:
% 6.97/2.51  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 6.97/2.51  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.97/2.51  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 6.97/2.51  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 6.97/2.51  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 6.97/2.51  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 6.97/2.51  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.97/2.51  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 6.97/2.51  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 6.97/2.51  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 6.97/2.51  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 6.97/2.51  tff('#skF_2', type, '#skF_2': $i).
% 6.97/2.51  tff('#skF_1', type, '#skF_1': $i).
% 6.97/2.51  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 6.97/2.51  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 6.97/2.51  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.97/2.51  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 6.97/2.51  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 6.97/2.51  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.97/2.51  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 6.97/2.51  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 6.97/2.51  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 6.97/2.51  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 6.97/2.51  
% 6.97/2.53  tff(f_29, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 6.97/2.53  tff(f_43, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 6.97/2.53  tff(f_51, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 6.97/2.53  tff(f_73, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 6.97/2.53  tff(f_91, axiom, (![A, B]: (v1_relat_1(B) => (k1_relat_1(k7_relat_1(B, A)) = k3_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t90_relat_1)).
% 6.97/2.53  tff(f_95, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_relat_1)).
% 6.97/2.53  tff(f_69, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k5_relat_1(A, B)), k1_relat_1(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_relat_1)).
% 6.97/2.53  tff(f_55, axiom, (![A, B]: (v1_relat_1(B) => (k8_relat_1(A, B) = k5_relat_1(B, k6_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t123_relat_1)).
% 6.97/2.53  tff(f_83, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k5_relat_1(B, k6_relat_1(A)) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_relat_1)).
% 6.97/2.53  tff(f_49, axiom, (![A, B]: ((v1_relat_1(A) & v1_relat_1(B)) => v1_relat_1(k5_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k5_relat_1)).
% 6.97/2.53  tff(f_62, axiom, (![A, B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (k8_relat_1(A, k5_relat_1(B, C)) = k5_relat_1(B, k8_relat_1(A, C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t139_relat_1)).
% 6.97/2.53  tff(f_77, axiom, (![A]: (v1_relat_1(A) => (k5_relat_1(k6_relat_1(k1_relat_1(A)), A) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t78_relat_1)).
% 6.97/2.53  tff(f_98, negated_conjecture, ~(![A, B]: (k5_relat_1(k6_relat_1(B), k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_funct_1)).
% 6.97/2.53  tff(c_4, plain, (![B_4, A_3]: (k2_tarski(B_4, A_3)=k2_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 6.97/2.53  tff(c_106, plain, (![A_62, B_63]: (k1_setfam_1(k2_tarski(A_62, B_63))=k3_xboole_0(A_62, B_63))), inference(cnfTransformation, [status(thm)], [f_43])).
% 6.97/2.53  tff(c_121, plain, (![B_64, A_65]: (k1_setfam_1(k2_tarski(B_64, A_65))=k3_xboole_0(A_65, B_64))), inference(superposition, [status(thm), theory('equality')], [c_4, c_106])).
% 6.97/2.53  tff(c_18, plain, (![A_32, B_33]: (k1_setfam_1(k2_tarski(A_32, B_33))=k3_xboole_0(A_32, B_33))), inference(cnfTransformation, [status(thm)], [f_43])).
% 6.97/2.53  tff(c_127, plain, (![B_64, A_65]: (k3_xboole_0(B_64, A_65)=k3_xboole_0(A_65, B_64))), inference(superposition, [status(thm), theory('equality')], [c_121, c_18])).
% 6.97/2.53  tff(c_22, plain, (![A_36]: (v1_relat_1(k6_relat_1(A_36)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 6.97/2.53  tff(c_30, plain, (![A_46]: (k1_relat_1(k6_relat_1(A_46))=A_46)), inference(cnfTransformation, [status(thm)], [f_73])).
% 6.97/2.53  tff(c_383, plain, (![B_85, A_86]: (k3_xboole_0(k1_relat_1(B_85), A_86)=k1_relat_1(k7_relat_1(B_85, A_86)) | ~v1_relat_1(B_85))), inference(cnfTransformation, [status(thm)], [f_91])).
% 6.97/2.53  tff(c_406, plain, (![A_46, A_86]: (k1_relat_1(k7_relat_1(k6_relat_1(A_46), A_86))=k3_xboole_0(A_46, A_86) | ~v1_relat_1(k6_relat_1(A_46)))), inference(superposition, [status(thm), theory('equality')], [c_30, c_383])).
% 6.97/2.53  tff(c_410, plain, (![A_46, A_86]: (k1_relat_1(k7_relat_1(k6_relat_1(A_46), A_86))=k3_xboole_0(A_46, A_86))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_406])).
% 6.97/2.53  tff(c_42, plain, (![A_53, B_54]: (k5_relat_1(k6_relat_1(A_53), B_54)=k7_relat_1(B_54, A_53) | ~v1_relat_1(B_54))), inference(cnfTransformation, [status(thm)], [f_95])).
% 6.97/2.53  tff(c_529, plain, (![A_100, B_101]: (r1_tarski(k1_relat_1(k5_relat_1(A_100, B_101)), k1_relat_1(A_100)) | ~v1_relat_1(B_101) | ~v1_relat_1(A_100))), inference(cnfTransformation, [status(thm)], [f_69])).
% 6.97/2.53  tff(c_538, plain, (![B_54, A_53]: (r1_tarski(k1_relat_1(k7_relat_1(B_54, A_53)), k1_relat_1(k6_relat_1(A_53))) | ~v1_relat_1(B_54) | ~v1_relat_1(k6_relat_1(A_53)) | ~v1_relat_1(B_54))), inference(superposition, [status(thm), theory('equality')], [c_42, c_529])).
% 6.97/2.53  tff(c_573, plain, (![B_103, A_104]: (r1_tarski(k1_relat_1(k7_relat_1(B_103, A_104)), A_104) | ~v1_relat_1(B_103))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_30, c_538])).
% 6.97/2.53  tff(c_576, plain, (![A_46, A_86]: (r1_tarski(k3_xboole_0(A_46, A_86), A_86) | ~v1_relat_1(k6_relat_1(A_46)))), inference(superposition, [status(thm), theory('equality')], [c_410, c_573])).
% 6.97/2.53  tff(c_584, plain, (![A_105, A_106]: (r1_tarski(k3_xboole_0(A_105, A_106), A_106))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_576])).
% 6.97/2.53  tff(c_593, plain, (![B_64, A_65]: (r1_tarski(k3_xboole_0(B_64, A_65), B_64))), inference(superposition, [status(thm), theory('equality')], [c_127, c_584])).
% 6.97/2.53  tff(c_581, plain, (![A_46, A_86]: (r1_tarski(k3_xboole_0(A_46, A_86), A_86))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_576])).
% 6.97/2.53  tff(c_322, plain, (![B_83, A_84]: (k5_relat_1(B_83, k6_relat_1(A_84))=k8_relat_1(A_84, B_83) | ~v1_relat_1(B_83))), inference(cnfTransformation, [status(thm)], [f_55])).
% 6.97/2.53  tff(c_354, plain, (![A_84, A_53]: (k8_relat_1(A_84, k6_relat_1(A_53))=k7_relat_1(k6_relat_1(A_84), A_53) | ~v1_relat_1(k6_relat_1(A_53)) | ~v1_relat_1(k6_relat_1(A_84)))), inference(superposition, [status(thm), theory('equality')], [c_42, c_322])).
% 6.97/2.53  tff(c_378, plain, (![A_84, A_53]: (k8_relat_1(A_84, k6_relat_1(A_53))=k7_relat_1(k6_relat_1(A_84), A_53))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_22, c_354])).
% 6.97/2.53  tff(c_32, plain, (![A_46]: (k2_relat_1(k6_relat_1(A_46))=A_46)), inference(cnfTransformation, [status(thm)], [f_73])).
% 6.97/2.53  tff(c_489, plain, (![B_95, A_96]: (k5_relat_1(B_95, k6_relat_1(A_96))=B_95 | ~r1_tarski(k2_relat_1(B_95), A_96) | ~v1_relat_1(B_95))), inference(cnfTransformation, [status(thm)], [f_83])).
% 6.97/2.53  tff(c_492, plain, (![A_46, A_96]: (k5_relat_1(k6_relat_1(A_46), k6_relat_1(A_96))=k6_relat_1(A_46) | ~r1_tarski(A_46, A_96) | ~v1_relat_1(k6_relat_1(A_46)))), inference(superposition, [status(thm), theory('equality')], [c_32, c_489])).
% 6.97/2.53  tff(c_924, plain, (![A_139, A_140]: (k5_relat_1(k6_relat_1(A_139), k6_relat_1(A_140))=k6_relat_1(A_139) | ~r1_tarski(A_139, A_140))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_492])).
% 6.97/2.53  tff(c_24, plain, (![B_38, A_37]: (k5_relat_1(B_38, k6_relat_1(A_37))=k8_relat_1(A_37, B_38) | ~v1_relat_1(B_38))), inference(cnfTransformation, [status(thm)], [f_55])).
% 6.97/2.53  tff(c_939, plain, (![A_140, A_139]: (k8_relat_1(A_140, k6_relat_1(A_139))=k6_relat_1(A_139) | ~v1_relat_1(k6_relat_1(A_139)) | ~r1_tarski(A_139, A_140))), inference(superposition, [status(thm), theory('equality')], [c_924, c_24])).
% 6.97/2.53  tff(c_991, plain, (![A_140, A_139]: (k7_relat_1(k6_relat_1(A_140), A_139)=k6_relat_1(A_139) | ~r1_tarski(A_139, A_140))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_378, c_939])).
% 6.97/2.53  tff(c_466, plain, (![A_93, A_94]: (k8_relat_1(A_93, k6_relat_1(A_94))=k7_relat_1(k6_relat_1(A_93), A_94))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_22, c_354])).
% 6.97/2.53  tff(c_20, plain, (![A_34, B_35]: (v1_relat_1(k5_relat_1(A_34, B_35)) | ~v1_relat_1(B_35) | ~v1_relat_1(A_34))), inference(cnfTransformation, [status(thm)], [f_49])).
% 6.97/2.53  tff(c_332, plain, (![A_84, B_83]: (v1_relat_1(k8_relat_1(A_84, B_83)) | ~v1_relat_1(k6_relat_1(A_84)) | ~v1_relat_1(B_83) | ~v1_relat_1(B_83))), inference(superposition, [status(thm), theory('equality')], [c_322, c_20])).
% 6.97/2.53  tff(c_369, plain, (![A_84, B_83]: (v1_relat_1(k8_relat_1(A_84, B_83)) | ~v1_relat_1(B_83))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_332])).
% 6.97/2.53  tff(c_476, plain, (![A_93, A_94]: (v1_relat_1(k7_relat_1(k6_relat_1(A_93), A_94)) | ~v1_relat_1(k6_relat_1(A_94)))), inference(superposition, [status(thm), theory('equality')], [c_466, c_369])).
% 6.97/2.53  tff(c_486, plain, (![A_93, A_94]: (v1_relat_1(k7_relat_1(k6_relat_1(A_93), A_94)))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_476])).
% 6.97/2.53  tff(c_781, plain, (![A_124, B_125, C_126]: (k8_relat_1(A_124, k5_relat_1(B_125, C_126))=k5_relat_1(B_125, k8_relat_1(A_124, C_126)) | ~v1_relat_1(C_126) | ~v1_relat_1(B_125))), inference(cnfTransformation, [status(thm)], [f_62])).
% 6.97/2.53  tff(c_804, plain, (![B_38, A_124, A_37]: (k5_relat_1(B_38, k8_relat_1(A_124, k6_relat_1(A_37)))=k8_relat_1(A_124, k8_relat_1(A_37, B_38)) | ~v1_relat_1(k6_relat_1(A_37)) | ~v1_relat_1(B_38) | ~v1_relat_1(B_38))), inference(superposition, [status(thm), theory('equality')], [c_24, c_781])).
% 6.97/2.53  tff(c_2406, plain, (![B_180, A_181, A_182]: (k5_relat_1(B_180, k7_relat_1(k6_relat_1(A_181), A_182))=k8_relat_1(A_181, k8_relat_1(A_182, B_180)) | ~v1_relat_1(B_180))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_378, c_804])).
% 6.97/2.53  tff(c_34, plain, (![A_47]: (k5_relat_1(k6_relat_1(k1_relat_1(A_47)), A_47)=A_47 | ~v1_relat_1(A_47))), inference(cnfTransformation, [status(thm)], [f_77])).
% 6.97/2.53  tff(c_2434, plain, (![A_181, A_182]: (k8_relat_1(A_181, k8_relat_1(A_182, k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(A_181), A_182)))))=k7_relat_1(k6_relat_1(A_181), A_182) | ~v1_relat_1(k7_relat_1(k6_relat_1(A_181), A_182)) | ~v1_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(A_181), A_182)))))), inference(superposition, [status(thm), theory('equality')], [c_2406, c_34])).
% 6.97/2.53  tff(c_9729, plain, (![A_338, A_339]: (k8_relat_1(A_338, k7_relat_1(k6_relat_1(A_339), k3_xboole_0(A_338, A_339)))=k7_relat_1(k6_relat_1(A_338), A_339))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_486, c_378, c_410, c_2434])).
% 6.97/2.53  tff(c_9823, plain, (![A_338, A_140]: (k8_relat_1(A_338, k6_relat_1(k3_xboole_0(A_338, A_140)))=k7_relat_1(k6_relat_1(A_338), A_140) | ~r1_tarski(k3_xboole_0(A_338, A_140), A_140))), inference(superposition, [status(thm), theory('equality')], [c_991, c_9729])).
% 6.97/2.53  tff(c_9872, plain, (![A_340, A_341]: (k7_relat_1(k6_relat_1(A_340), k3_xboole_0(A_340, A_341))=k7_relat_1(k6_relat_1(A_340), A_341))), inference(demodulation, [status(thm), theory('equality')], [c_581, c_378, c_9823])).
% 6.97/2.53  tff(c_9960, plain, (![A_340, A_341]: (k7_relat_1(k6_relat_1(A_340), A_341)=k6_relat_1(k3_xboole_0(A_340, A_341)) | ~r1_tarski(k3_xboole_0(A_340, A_341), A_340))), inference(superposition, [status(thm), theory('equality')], [c_9872, c_991])).
% 6.97/2.53  tff(c_10084, plain, (![A_340, A_341]: (k7_relat_1(k6_relat_1(A_340), A_341)=k6_relat_1(k3_xboole_0(A_340, A_341)))), inference(demodulation, [status(thm), theory('equality')], [c_593, c_9960])).
% 6.97/2.53  tff(c_255, plain, (![A_78, B_79]: (k5_relat_1(k6_relat_1(A_78), B_79)=k7_relat_1(B_79, A_78) | ~v1_relat_1(B_79))), inference(cnfTransformation, [status(thm)], [f_95])).
% 6.97/2.53  tff(c_44, plain, (k5_relat_1(k6_relat_1('#skF_2'), k6_relat_1('#skF_1'))!=k6_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_98])).
% 6.97/2.53  tff(c_276, plain, (k7_relat_1(k6_relat_1('#skF_1'), '#skF_2')!=k6_relat_1(k3_xboole_0('#skF_1', '#skF_2')) | ~v1_relat_1(k6_relat_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_255, c_44])).
% 6.97/2.53  tff(c_298, plain, (k7_relat_1(k6_relat_1('#skF_1'), '#skF_2')!=k6_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_276])).
% 6.97/2.53  tff(c_10146, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_10084, c_298])).
% 6.97/2.53  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.97/2.53  
% 6.97/2.53  Inference rules
% 6.97/2.53  ----------------------
% 6.97/2.53  #Ref     : 0
% 6.97/2.53  #Sup     : 2455
% 6.97/2.53  #Fact    : 0
% 6.97/2.53  #Define  : 0
% 6.97/2.53  #Split   : 1
% 6.97/2.53  #Chain   : 0
% 6.97/2.53  #Close   : 0
% 6.97/2.53  
% 6.97/2.53  Ordering : KBO
% 6.97/2.53  
% 6.97/2.53  Simplification rules
% 6.97/2.53  ----------------------
% 6.97/2.53  #Subsume      : 297
% 6.97/2.53  #Demod        : 3561
% 6.97/2.53  #Tautology    : 1282
% 6.97/2.53  #SimpNegUnit  : 0
% 6.97/2.53  #BackRed      : 37
% 6.97/2.53  
% 6.97/2.53  #Partial instantiations: 0
% 6.97/2.53  #Strategies tried      : 1
% 6.97/2.53  
% 6.97/2.53  Timing (in seconds)
% 6.97/2.53  ----------------------
% 6.97/2.53  Preprocessing        : 0.32
% 6.97/2.53  Parsing              : 0.17
% 6.97/2.53  CNF conversion       : 0.02
% 6.97/2.53  Main loop            : 1.45
% 6.97/2.53  Inferencing          : 0.39
% 6.97/2.53  Reduction            : 0.71
% 6.97/2.53  Demodulation         : 0.60
% 6.97/2.53  BG Simplification    : 0.05
% 6.97/2.53  Subsumption          : 0.23
% 6.97/2.53  Abstraction          : 0.07
% 6.97/2.53  MUC search           : 0.00
% 6.97/2.53  Cooper               : 0.00
% 6.97/2.53  Total                : 1.80
% 6.97/2.53  Index Insertion      : 0.00
% 6.97/2.53  Index Deletion       : 0.00
% 6.97/2.53  Index Matching       : 0.00
% 6.97/2.53  BG Taut test         : 0.00
%------------------------------------------------------------------------------

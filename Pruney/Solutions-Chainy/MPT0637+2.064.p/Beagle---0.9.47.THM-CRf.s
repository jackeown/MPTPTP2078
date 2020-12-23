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
% DateTime   : Thu Dec  3 10:03:32 EST 2020

% Result     : Theorem 9.01s
% Output     : CNFRefutation 9.01s
% Verified   : 
% Statistics : Number of formulae       :  107 (1677 expanded)
%              Number of leaves         :   35 ( 600 expanded)
%              Depth                    :   21
%              Number of atoms          :  160 (2739 expanded)
%              Number of equality atoms :   73 (1033 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k6_relat_1 > k4_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
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

tff(k4_relat_1,type,(
    k4_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_27,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_83,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_49,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_91,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k5_relat_1(k6_relat_1(A),B) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_relat_1)).

tff(f_103,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k5_relat_1(k6_relat_1(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).

tff(f_99,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k1_relat_1(k7_relat_1(B,A)) = k3_xboole_0(k1_relat_1(B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_relat_1)).

tff(f_85,axiom,(
    ! [A] : k4_relat_1(k6_relat_1(A)) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_relat_1)).

tff(f_69,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k4_relat_1(k5_relat_1(A,B)) = k5_relat_1(k4_relat_1(B),k4_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_relat_1)).

tff(f_95,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k5_relat_1(A,k6_relat_1(k2_relat_1(A))) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_relat_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ! [C] :
          ( v1_relat_1(C)
         => k7_relat_1(k5_relat_1(B,C),A) = k5_relat_1(k7_relat_1(B,A),C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t112_relat_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_relat_1(B) )
     => v1_relat_1(k5_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).

tff(f_62,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k2_relat_1(A) = k1_relat_1(k4_relat_1(A))
        & k1_relat_1(A) = k2_relat_1(k4_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_relat_1)).

tff(f_106,negated_conjecture,(
    ~ ! [A,B] : k5_relat_1(k6_relat_1(B),k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_funct_1)).

tff(c_2,plain,(
    ! [A_1,B_2] : r1_tarski(k3_xboole_0(A_1,B_2),A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_32,plain,(
    ! [A_50] : k1_relat_1(k6_relat_1(A_50)) = A_50 ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_20,plain,(
    ! [A_34] : v1_relat_1(k6_relat_1(A_34)) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_285,plain,(
    ! [A_89,B_90] :
      ( k5_relat_1(k6_relat_1(A_89),B_90) = B_90
      | ~ r1_tarski(k1_relat_1(B_90),A_89)
      | ~ v1_relat_1(B_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_298,plain,(
    ! [A_89,A_50] :
      ( k5_relat_1(k6_relat_1(A_89),k6_relat_1(A_50)) = k6_relat_1(A_50)
      | ~ r1_tarski(A_50,A_89)
      | ~ v1_relat_1(k6_relat_1(A_50)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_285])).

tff(c_464,plain,(
    ! [A_100,A_101] :
      ( k5_relat_1(k6_relat_1(A_100),k6_relat_1(A_101)) = k6_relat_1(A_101)
      | ~ r1_tarski(A_101,A_100) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_298])).

tff(c_44,plain,(
    ! [A_57,B_58] :
      ( k5_relat_1(k6_relat_1(A_57),B_58) = k7_relat_1(B_58,A_57)
      | ~ v1_relat_1(B_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_474,plain,(
    ! [A_101,A_100] :
      ( k7_relat_1(k6_relat_1(A_101),A_100) = k6_relat_1(A_101)
      | ~ v1_relat_1(k6_relat_1(A_101))
      | ~ r1_tarski(A_101,A_100) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_464,c_44])).

tff(c_531,plain,(
    ! [A_102,A_103] :
      ( k7_relat_1(k6_relat_1(A_102),A_103) = k6_relat_1(A_102)
      | ~ r1_tarski(A_102,A_103) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_474])).

tff(c_210,plain,(
    ! [B_80,A_81] :
      ( k3_xboole_0(k1_relat_1(B_80),A_81) = k1_relat_1(k7_relat_1(B_80,A_81))
      | ~ v1_relat_1(B_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_225,plain,(
    ! [A_50,A_81] :
      ( k1_relat_1(k7_relat_1(k6_relat_1(A_50),A_81)) = k3_xboole_0(A_50,A_81)
      | ~ v1_relat_1(k6_relat_1(A_50)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_210])).

tff(c_229,plain,(
    ! [A_50,A_81] : k1_relat_1(k7_relat_1(k6_relat_1(A_50),A_81)) = k3_xboole_0(A_50,A_81) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_225])).

tff(c_548,plain,(
    ! [A_102,A_103] :
      ( k3_xboole_0(A_102,A_103) = k1_relat_1(k6_relat_1(A_102))
      | ~ r1_tarski(A_102,A_103) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_531,c_229])).

tff(c_599,plain,(
    ! [A_109,A_110] :
      ( k3_xboole_0(A_109,A_110) = A_109
      | ~ r1_tarski(A_109,A_110) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_548])).

tff(c_612,plain,(
    ! [A_1,B_2] : k3_xboole_0(k3_xboole_0(A_1,B_2),A_1) = k3_xboole_0(A_1,B_2) ),
    inference(resolution,[status(thm)],[c_2,c_599])).

tff(c_36,plain,(
    ! [A_51] : k4_relat_1(k6_relat_1(A_51)) = k6_relat_1(A_51) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_642,plain,(
    ! [B_113,A_114] :
      ( k5_relat_1(k4_relat_1(B_113),k4_relat_1(A_114)) = k4_relat_1(k5_relat_1(A_114,B_113))
      | ~ v1_relat_1(B_113)
      | ~ v1_relat_1(A_114) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_654,plain,(
    ! [A_51,A_114] :
      ( k5_relat_1(k6_relat_1(A_51),k4_relat_1(A_114)) = k4_relat_1(k5_relat_1(A_114,k6_relat_1(A_51)))
      | ~ v1_relat_1(k6_relat_1(A_51))
      | ~ v1_relat_1(A_114) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_642])).

tff(c_664,plain,(
    ! [A_115,A_116] :
      ( k5_relat_1(k6_relat_1(A_115),k4_relat_1(A_116)) = k4_relat_1(k5_relat_1(A_116,k6_relat_1(A_115)))
      | ~ v1_relat_1(A_116) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_654])).

tff(c_691,plain,(
    ! [A_51,A_115] :
      ( k4_relat_1(k5_relat_1(k6_relat_1(A_51),k6_relat_1(A_115))) = k5_relat_1(k6_relat_1(A_115),k6_relat_1(A_51))
      | ~ v1_relat_1(k6_relat_1(A_51)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_664])).

tff(c_797,plain,(
    ! [A_124,A_125] : k4_relat_1(k5_relat_1(k6_relat_1(A_124),k6_relat_1(A_125))) = k5_relat_1(k6_relat_1(A_125),k6_relat_1(A_124)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_691])).

tff(c_832,plain,(
    ! [A_125,A_57] :
      ( k5_relat_1(k6_relat_1(A_125),k6_relat_1(A_57)) = k4_relat_1(k7_relat_1(k6_relat_1(A_125),A_57))
      | ~ v1_relat_1(k6_relat_1(A_125)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_797])).

tff(c_904,plain,(
    ! [A_136,A_137] : k5_relat_1(k6_relat_1(A_136),k6_relat_1(A_137)) = k4_relat_1(k7_relat_1(k6_relat_1(A_136),A_137)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_832])).

tff(c_920,plain,(
    ! [A_136,A_137] :
      ( k4_relat_1(k7_relat_1(k6_relat_1(A_136),A_137)) = k7_relat_1(k6_relat_1(A_137),A_136)
      | ~ v1_relat_1(k6_relat_1(A_137)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_904,c_44])).

tff(c_958,plain,(
    ! [A_136,A_137] : k4_relat_1(k7_relat_1(k6_relat_1(A_136),A_137)) = k7_relat_1(k6_relat_1(A_137),A_136) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_920])).

tff(c_848,plain,(
    ! [A_125,A_57] : k5_relat_1(k6_relat_1(A_125),k6_relat_1(A_57)) = k4_relat_1(k7_relat_1(k6_relat_1(A_125),A_57)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_832])).

tff(c_991,plain,(
    ! [A_125,A_57] : k5_relat_1(k6_relat_1(A_125),k6_relat_1(A_57)) = k7_relat_1(k6_relat_1(A_57),A_125) ),
    inference(demodulation,[status(thm),theory(equality)],[c_958,c_848])).

tff(c_34,plain,(
    ! [A_50] : k2_relat_1(k6_relat_1(A_50)) = A_50 ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_168,plain,(
    ! [A_78,B_79] :
      ( k5_relat_1(k6_relat_1(A_78),B_79) = k7_relat_1(B_79,A_78)
      | ~ v1_relat_1(B_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_40,plain,(
    ! [A_54] :
      ( k5_relat_1(A_54,k6_relat_1(k2_relat_1(A_54))) = A_54
      | ~ v1_relat_1(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_179,plain,(
    ! [A_78] :
      ( k7_relat_1(k6_relat_1(k2_relat_1(k6_relat_1(A_78))),A_78) = k6_relat_1(A_78)
      | ~ v1_relat_1(k6_relat_1(A_78))
      | ~ v1_relat_1(k6_relat_1(k2_relat_1(k6_relat_1(A_78)))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_168,c_40])).

tff(c_200,plain,(
    ! [A_78] : k7_relat_1(k6_relat_1(A_78),A_78) = k6_relat_1(A_78) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_20,c_34,c_179])).

tff(c_724,plain,(
    ! [B_119,C_120,A_121] :
      ( k7_relat_1(k5_relat_1(B_119,C_120),A_121) = k5_relat_1(k7_relat_1(B_119,A_121),C_120)
      | ~ v1_relat_1(C_120)
      | ~ v1_relat_1(B_119) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_763,plain,(
    ! [A_57,A_121,B_58] :
      ( k5_relat_1(k7_relat_1(k6_relat_1(A_57),A_121),B_58) = k7_relat_1(k7_relat_1(B_58,A_57),A_121)
      | ~ v1_relat_1(B_58)
      | ~ v1_relat_1(k6_relat_1(A_57))
      | ~ v1_relat_1(B_58) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_724])).

tff(c_2074,plain,(
    ! [A_193,A_194,B_195] :
      ( k5_relat_1(k7_relat_1(k6_relat_1(A_193),A_194),B_195) = k7_relat_1(k7_relat_1(B_195,A_193),A_194)
      | ~ v1_relat_1(B_195) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_763])).

tff(c_2132,plain,(
    ! [B_195,A_78] :
      ( k7_relat_1(k7_relat_1(B_195,A_78),A_78) = k5_relat_1(k6_relat_1(A_78),B_195)
      | ~ v1_relat_1(B_195) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_200,c_2074])).

tff(c_18,plain,(
    ! [A_32,B_33] :
      ( v1_relat_1(k5_relat_1(A_32,B_33))
      | ~ v1_relat_1(B_33)
      | ~ v1_relat_1(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_677,plain,(
    ! [A_116,A_115] :
      ( v1_relat_1(k4_relat_1(k5_relat_1(A_116,k6_relat_1(A_115))))
      | ~ v1_relat_1(k4_relat_1(A_116))
      | ~ v1_relat_1(k6_relat_1(A_115))
      | ~ v1_relat_1(A_116) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_664,c_18])).

tff(c_694,plain,(
    ! [A_116,A_115] :
      ( v1_relat_1(k4_relat_1(k5_relat_1(A_116,k6_relat_1(A_115))))
      | ~ v1_relat_1(k4_relat_1(A_116))
      | ~ v1_relat_1(A_116) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_677])).

tff(c_803,plain,(
    ! [A_125,A_124] :
      ( v1_relat_1(k5_relat_1(k6_relat_1(A_125),k6_relat_1(A_124)))
      | ~ v1_relat_1(k4_relat_1(k6_relat_1(A_124)))
      | ~ v1_relat_1(k6_relat_1(A_124)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_797,c_694])).

tff(c_852,plain,(
    ! [A_126,A_127] : v1_relat_1(k5_relat_1(k6_relat_1(A_126),k6_relat_1(A_127))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_20,c_36,c_803])).

tff(c_862,plain,(
    ! [A_127,A_57] :
      ( v1_relat_1(k7_relat_1(k6_relat_1(A_127),A_57))
      | ~ v1_relat_1(k6_relat_1(A_127)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_852])).

tff(c_873,plain,(
    ! [A_127,A_57] : v1_relat_1(k7_relat_1(k6_relat_1(A_127),A_57)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_862])).

tff(c_995,plain,(
    ! [A_140,A_141] : k4_relat_1(k7_relat_1(k6_relat_1(A_140),A_141)) = k7_relat_1(k6_relat_1(A_141),A_140) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_920])).

tff(c_26,plain,(
    ! [A_39] :
      ( k1_relat_1(k4_relat_1(A_39)) = k2_relat_1(A_39)
      | ~ v1_relat_1(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_1010,plain,(
    ! [A_140,A_141] :
      ( k2_relat_1(k7_relat_1(k6_relat_1(A_140),A_141)) = k1_relat_1(k7_relat_1(k6_relat_1(A_141),A_140))
      | ~ v1_relat_1(k7_relat_1(k6_relat_1(A_140),A_141)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_995,c_26])).

tff(c_1035,plain,(
    ! [A_140,A_141] : k2_relat_1(k7_relat_1(k6_relat_1(A_140),A_141)) = k3_xboole_0(A_141,A_140) ),
    inference(demodulation,[status(thm),theory(equality)],[c_873,c_229,c_1010])).

tff(c_2520,plain,(
    ! [A_213,A_214] :
      ( k1_relat_1(k7_relat_1(k4_relat_1(A_213),A_214)) = k3_xboole_0(k2_relat_1(A_213),A_214)
      | ~ v1_relat_1(k4_relat_1(A_213))
      | ~ v1_relat_1(A_213) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_210])).

tff(c_2566,plain,(
    ! [A_136,A_137,A_214] :
      ( k3_xboole_0(k2_relat_1(k7_relat_1(k6_relat_1(A_136),A_137)),A_214) = k1_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(A_137),A_136),A_214))
      | ~ v1_relat_1(k4_relat_1(k7_relat_1(k6_relat_1(A_136),A_137)))
      | ~ v1_relat_1(k7_relat_1(k6_relat_1(A_136),A_137)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_958,c_2520])).

tff(c_3344,plain,(
    ! [A_232,A_233,A_234] : k1_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(A_232),A_233),A_234)) = k3_xboole_0(k3_xboole_0(A_232,A_233),A_234) ),
    inference(demodulation,[status(thm),theory(equality)],[c_873,c_873,c_958,c_1035,c_2566])).

tff(c_3391,plain,(
    ! [A_232,A_78] :
      ( k3_xboole_0(k3_xboole_0(A_232,A_78),A_78) = k1_relat_1(k5_relat_1(k6_relat_1(A_78),k6_relat_1(A_232)))
      | ~ v1_relat_1(k6_relat_1(A_232)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2132,c_3344])).

tff(c_3429,plain,(
    ! [A_232,A_78] : k3_xboole_0(k3_xboole_0(A_232,A_78),A_78) = k3_xboole_0(A_232,A_78) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_229,c_991,c_3391])).

tff(c_2136,plain,(
    ! [A_193,A_194] :
      ( k7_relat_1(k7_relat_1(k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(A_193),A_194))),A_193),A_194) = k7_relat_1(k6_relat_1(A_193),A_194)
      | ~ v1_relat_1(k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(A_193),A_194))))
      | ~ v1_relat_1(k7_relat_1(k6_relat_1(A_193),A_194)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_2074])).

tff(c_5329,plain,(
    ! [A_273,A_274] : k7_relat_1(k7_relat_1(k6_relat_1(k3_xboole_0(A_273,A_274)),A_274),A_273) = k7_relat_1(k6_relat_1(A_274),A_273) ),
    inference(demodulation,[status(thm),theory(equality)],[c_873,c_20,c_1035,c_2136])).

tff(c_2582,plain,(
    ! [A_137,A_136,A_214] : k1_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(A_137),A_136),A_214)) = k3_xboole_0(k3_xboole_0(A_137,A_136),A_214) ),
    inference(demodulation,[status(thm),theory(equality)],[c_873,c_873,c_958,c_1035,c_2566])).

tff(c_5353,plain,(
    ! [A_273,A_274] : k3_xboole_0(k3_xboole_0(k3_xboole_0(A_273,A_274),A_274),A_273) = k1_relat_1(k7_relat_1(k6_relat_1(A_274),A_273)) ),
    inference(superposition,[status(thm),theory(equality)],[c_5329,c_2582])).

tff(c_5454,plain,(
    ! [A_274,A_273] : k3_xboole_0(A_274,A_273) = k3_xboole_0(A_273,A_274) ),
    inference(demodulation,[status(thm),theory(equality)],[c_612,c_3429,c_229,c_5353])).

tff(c_5481,plain,(
    ! [A_276,A_275] : k3_xboole_0(A_276,A_275) = k3_xboole_0(A_275,A_276) ),
    inference(demodulation,[status(thm),theory(equality)],[c_612,c_3429,c_229,c_5353])).

tff(c_5704,plain,(
    ! [A_276,A_275] : r1_tarski(k3_xboole_0(A_276,A_275),A_275) ),
    inference(superposition,[status(thm),theory(equality)],[c_5481,c_2])).

tff(c_301,plain,(
    ! [A_89,A_50] :
      ( k5_relat_1(k6_relat_1(A_89),k6_relat_1(A_50)) = k6_relat_1(A_50)
      | ~ r1_tarski(A_50,A_89) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_298])).

tff(c_753,plain,(
    ! [A_89,A_121,A_50] :
      ( k5_relat_1(k7_relat_1(k6_relat_1(A_89),A_121),k6_relat_1(A_50)) = k7_relat_1(k6_relat_1(A_50),A_121)
      | ~ v1_relat_1(k6_relat_1(A_50))
      | ~ v1_relat_1(k6_relat_1(A_89))
      | ~ r1_tarski(A_50,A_89) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_301,c_724])).

tff(c_15035,plain,(
    ! [A_380,A_381,A_382] :
      ( k5_relat_1(k7_relat_1(k6_relat_1(A_380),A_381),k6_relat_1(A_382)) = k7_relat_1(k6_relat_1(A_382),A_381)
      | ~ r1_tarski(A_382,A_380) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_20,c_753])).

tff(c_15095,plain,(
    ! [A_380,A_381] :
      ( k7_relat_1(k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(A_380),A_381))),A_381) = k7_relat_1(k6_relat_1(A_380),A_381)
      | ~ v1_relat_1(k7_relat_1(k6_relat_1(A_380),A_381))
      | ~ r1_tarski(k2_relat_1(k7_relat_1(k6_relat_1(A_380),A_381)),A_380) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_15035,c_40])).

tff(c_15227,plain,(
    ! [A_383,A_384] : k7_relat_1(k6_relat_1(k3_xboole_0(A_383,A_384)),A_383) = k7_relat_1(k6_relat_1(A_384),A_383) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5704,c_1035,c_873,c_1035,c_15095])).

tff(c_512,plain,(
    ! [A_101,A_100] :
      ( k7_relat_1(k6_relat_1(A_101),A_100) = k6_relat_1(A_101)
      | ~ r1_tarski(A_101,A_100) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_474])).

tff(c_15306,plain,(
    ! [A_384,A_383] :
      ( k7_relat_1(k6_relat_1(A_384),A_383) = k6_relat_1(k3_xboole_0(A_383,A_384))
      | ~ r1_tarski(k3_xboole_0(A_383,A_384),A_383) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_15227,c_512])).

tff(c_15458,plain,(
    ! [A_384,A_383] : k7_relat_1(k6_relat_1(A_384),A_383) = k6_relat_1(k3_xboole_0(A_383,A_384)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_15306])).

tff(c_46,plain,(
    k5_relat_1(k6_relat_1('#skF_2'),k6_relat_1('#skF_1')) != k6_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_185,plain,
    ( k7_relat_1(k6_relat_1('#skF_1'),'#skF_2') != k6_relat_1(k3_xboole_0('#skF_1','#skF_2'))
    | ~ v1_relat_1(k6_relat_1('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_168,c_46])).

tff(c_204,plain,(
    k7_relat_1(k6_relat_1('#skF_1'),'#skF_2') != k6_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_185])).

tff(c_15498,plain,(
    k6_relat_1(k3_xboole_0('#skF_2','#skF_1')) != k6_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_15458,c_204])).

tff(c_15508,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5454,c_15498])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:46:45 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.01/3.22  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.01/3.23  
% 9.01/3.23  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.01/3.23  %$ r1_tarski > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k6_relat_1 > k4_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1
% 9.01/3.23  
% 9.01/3.23  %Foreground sorts:
% 9.01/3.23  
% 9.01/3.23  
% 9.01/3.23  %Background operators:
% 9.01/3.23  
% 9.01/3.23  
% 9.01/3.23  %Foreground operators:
% 9.01/3.23  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.01/3.23  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 9.01/3.23  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 9.01/3.23  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 9.01/3.23  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 9.01/3.23  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 9.01/3.23  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 9.01/3.23  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 9.01/3.23  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 9.01/3.23  tff('#skF_2', type, '#skF_2': $i).
% 9.01/3.23  tff('#skF_1', type, '#skF_1': $i).
% 9.01/3.23  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 9.01/3.23  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 9.01/3.23  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.01/3.23  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 9.01/3.23  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 9.01/3.23  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.01/3.23  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 9.01/3.23  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 9.01/3.23  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 9.01/3.23  tff(k4_relat_1, type, k4_relat_1: $i > $i).
% 9.01/3.23  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 9.01/3.23  
% 9.01/3.25  tff(f_27, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 9.01/3.25  tff(f_83, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 9.01/3.25  tff(f_49, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 9.01/3.25  tff(f_91, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k5_relat_1(k6_relat_1(A), B) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t77_relat_1)).
% 9.01/3.25  tff(f_103, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_relat_1)).
% 9.01/3.25  tff(f_99, axiom, (![A, B]: (v1_relat_1(B) => (k1_relat_1(k7_relat_1(B, A)) = k3_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t90_relat_1)).
% 9.01/3.25  tff(f_85, axiom, (![A]: (k4_relat_1(k6_relat_1(A)) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_relat_1)).
% 9.01/3.25  tff(f_69, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k4_relat_1(k5_relat_1(A, B)) = k5_relat_1(k4_relat_1(B), k4_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t54_relat_1)).
% 9.01/3.25  tff(f_95, axiom, (![A]: (v1_relat_1(A) => (k5_relat_1(A, k6_relat_1(k2_relat_1(A))) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t80_relat_1)).
% 9.01/3.25  tff(f_56, axiom, (![A, B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (k7_relat_1(k5_relat_1(B, C), A) = k5_relat_1(k7_relat_1(B, A), C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t112_relat_1)).
% 9.01/3.25  tff(f_47, axiom, (![A, B]: ((v1_relat_1(A) & v1_relat_1(B)) => v1_relat_1(k5_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k5_relat_1)).
% 9.01/3.25  tff(f_62, axiom, (![A]: (v1_relat_1(A) => ((k2_relat_1(A) = k1_relat_1(k4_relat_1(A))) & (k1_relat_1(A) = k2_relat_1(k4_relat_1(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t37_relat_1)).
% 9.01/3.25  tff(f_106, negated_conjecture, ~(![A, B]: (k5_relat_1(k6_relat_1(B), k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_funct_1)).
% 9.01/3.25  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(k3_xboole_0(A_1, B_2), A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 9.01/3.25  tff(c_32, plain, (![A_50]: (k1_relat_1(k6_relat_1(A_50))=A_50)), inference(cnfTransformation, [status(thm)], [f_83])).
% 9.01/3.25  tff(c_20, plain, (![A_34]: (v1_relat_1(k6_relat_1(A_34)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 9.01/3.25  tff(c_285, plain, (![A_89, B_90]: (k5_relat_1(k6_relat_1(A_89), B_90)=B_90 | ~r1_tarski(k1_relat_1(B_90), A_89) | ~v1_relat_1(B_90))), inference(cnfTransformation, [status(thm)], [f_91])).
% 9.01/3.25  tff(c_298, plain, (![A_89, A_50]: (k5_relat_1(k6_relat_1(A_89), k6_relat_1(A_50))=k6_relat_1(A_50) | ~r1_tarski(A_50, A_89) | ~v1_relat_1(k6_relat_1(A_50)))), inference(superposition, [status(thm), theory('equality')], [c_32, c_285])).
% 9.01/3.25  tff(c_464, plain, (![A_100, A_101]: (k5_relat_1(k6_relat_1(A_100), k6_relat_1(A_101))=k6_relat_1(A_101) | ~r1_tarski(A_101, A_100))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_298])).
% 9.01/3.25  tff(c_44, plain, (![A_57, B_58]: (k5_relat_1(k6_relat_1(A_57), B_58)=k7_relat_1(B_58, A_57) | ~v1_relat_1(B_58))), inference(cnfTransformation, [status(thm)], [f_103])).
% 9.01/3.25  tff(c_474, plain, (![A_101, A_100]: (k7_relat_1(k6_relat_1(A_101), A_100)=k6_relat_1(A_101) | ~v1_relat_1(k6_relat_1(A_101)) | ~r1_tarski(A_101, A_100))), inference(superposition, [status(thm), theory('equality')], [c_464, c_44])).
% 9.01/3.25  tff(c_531, plain, (![A_102, A_103]: (k7_relat_1(k6_relat_1(A_102), A_103)=k6_relat_1(A_102) | ~r1_tarski(A_102, A_103))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_474])).
% 9.01/3.25  tff(c_210, plain, (![B_80, A_81]: (k3_xboole_0(k1_relat_1(B_80), A_81)=k1_relat_1(k7_relat_1(B_80, A_81)) | ~v1_relat_1(B_80))), inference(cnfTransformation, [status(thm)], [f_99])).
% 9.01/3.25  tff(c_225, plain, (![A_50, A_81]: (k1_relat_1(k7_relat_1(k6_relat_1(A_50), A_81))=k3_xboole_0(A_50, A_81) | ~v1_relat_1(k6_relat_1(A_50)))), inference(superposition, [status(thm), theory('equality')], [c_32, c_210])).
% 9.01/3.25  tff(c_229, plain, (![A_50, A_81]: (k1_relat_1(k7_relat_1(k6_relat_1(A_50), A_81))=k3_xboole_0(A_50, A_81))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_225])).
% 9.01/3.25  tff(c_548, plain, (![A_102, A_103]: (k3_xboole_0(A_102, A_103)=k1_relat_1(k6_relat_1(A_102)) | ~r1_tarski(A_102, A_103))), inference(superposition, [status(thm), theory('equality')], [c_531, c_229])).
% 9.01/3.25  tff(c_599, plain, (![A_109, A_110]: (k3_xboole_0(A_109, A_110)=A_109 | ~r1_tarski(A_109, A_110))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_548])).
% 9.01/3.25  tff(c_612, plain, (![A_1, B_2]: (k3_xboole_0(k3_xboole_0(A_1, B_2), A_1)=k3_xboole_0(A_1, B_2))), inference(resolution, [status(thm)], [c_2, c_599])).
% 9.01/3.25  tff(c_36, plain, (![A_51]: (k4_relat_1(k6_relat_1(A_51))=k6_relat_1(A_51))), inference(cnfTransformation, [status(thm)], [f_85])).
% 9.01/3.25  tff(c_642, plain, (![B_113, A_114]: (k5_relat_1(k4_relat_1(B_113), k4_relat_1(A_114))=k4_relat_1(k5_relat_1(A_114, B_113)) | ~v1_relat_1(B_113) | ~v1_relat_1(A_114))), inference(cnfTransformation, [status(thm)], [f_69])).
% 9.01/3.25  tff(c_654, plain, (![A_51, A_114]: (k5_relat_1(k6_relat_1(A_51), k4_relat_1(A_114))=k4_relat_1(k5_relat_1(A_114, k6_relat_1(A_51))) | ~v1_relat_1(k6_relat_1(A_51)) | ~v1_relat_1(A_114))), inference(superposition, [status(thm), theory('equality')], [c_36, c_642])).
% 9.01/3.25  tff(c_664, plain, (![A_115, A_116]: (k5_relat_1(k6_relat_1(A_115), k4_relat_1(A_116))=k4_relat_1(k5_relat_1(A_116, k6_relat_1(A_115))) | ~v1_relat_1(A_116))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_654])).
% 9.01/3.25  tff(c_691, plain, (![A_51, A_115]: (k4_relat_1(k5_relat_1(k6_relat_1(A_51), k6_relat_1(A_115)))=k5_relat_1(k6_relat_1(A_115), k6_relat_1(A_51)) | ~v1_relat_1(k6_relat_1(A_51)))), inference(superposition, [status(thm), theory('equality')], [c_36, c_664])).
% 9.01/3.25  tff(c_797, plain, (![A_124, A_125]: (k4_relat_1(k5_relat_1(k6_relat_1(A_124), k6_relat_1(A_125)))=k5_relat_1(k6_relat_1(A_125), k6_relat_1(A_124)))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_691])).
% 9.01/3.25  tff(c_832, plain, (![A_125, A_57]: (k5_relat_1(k6_relat_1(A_125), k6_relat_1(A_57))=k4_relat_1(k7_relat_1(k6_relat_1(A_125), A_57)) | ~v1_relat_1(k6_relat_1(A_125)))), inference(superposition, [status(thm), theory('equality')], [c_44, c_797])).
% 9.01/3.25  tff(c_904, plain, (![A_136, A_137]: (k5_relat_1(k6_relat_1(A_136), k6_relat_1(A_137))=k4_relat_1(k7_relat_1(k6_relat_1(A_136), A_137)))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_832])).
% 9.01/3.25  tff(c_920, plain, (![A_136, A_137]: (k4_relat_1(k7_relat_1(k6_relat_1(A_136), A_137))=k7_relat_1(k6_relat_1(A_137), A_136) | ~v1_relat_1(k6_relat_1(A_137)))), inference(superposition, [status(thm), theory('equality')], [c_904, c_44])).
% 9.01/3.25  tff(c_958, plain, (![A_136, A_137]: (k4_relat_1(k7_relat_1(k6_relat_1(A_136), A_137))=k7_relat_1(k6_relat_1(A_137), A_136))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_920])).
% 9.01/3.25  tff(c_848, plain, (![A_125, A_57]: (k5_relat_1(k6_relat_1(A_125), k6_relat_1(A_57))=k4_relat_1(k7_relat_1(k6_relat_1(A_125), A_57)))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_832])).
% 9.01/3.25  tff(c_991, plain, (![A_125, A_57]: (k5_relat_1(k6_relat_1(A_125), k6_relat_1(A_57))=k7_relat_1(k6_relat_1(A_57), A_125))), inference(demodulation, [status(thm), theory('equality')], [c_958, c_848])).
% 9.01/3.25  tff(c_34, plain, (![A_50]: (k2_relat_1(k6_relat_1(A_50))=A_50)), inference(cnfTransformation, [status(thm)], [f_83])).
% 9.01/3.25  tff(c_168, plain, (![A_78, B_79]: (k5_relat_1(k6_relat_1(A_78), B_79)=k7_relat_1(B_79, A_78) | ~v1_relat_1(B_79))), inference(cnfTransformation, [status(thm)], [f_103])).
% 9.01/3.25  tff(c_40, plain, (![A_54]: (k5_relat_1(A_54, k6_relat_1(k2_relat_1(A_54)))=A_54 | ~v1_relat_1(A_54))), inference(cnfTransformation, [status(thm)], [f_95])).
% 9.01/3.25  tff(c_179, plain, (![A_78]: (k7_relat_1(k6_relat_1(k2_relat_1(k6_relat_1(A_78))), A_78)=k6_relat_1(A_78) | ~v1_relat_1(k6_relat_1(A_78)) | ~v1_relat_1(k6_relat_1(k2_relat_1(k6_relat_1(A_78)))))), inference(superposition, [status(thm), theory('equality')], [c_168, c_40])).
% 9.01/3.25  tff(c_200, plain, (![A_78]: (k7_relat_1(k6_relat_1(A_78), A_78)=k6_relat_1(A_78))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_20, c_34, c_179])).
% 9.01/3.25  tff(c_724, plain, (![B_119, C_120, A_121]: (k7_relat_1(k5_relat_1(B_119, C_120), A_121)=k5_relat_1(k7_relat_1(B_119, A_121), C_120) | ~v1_relat_1(C_120) | ~v1_relat_1(B_119))), inference(cnfTransformation, [status(thm)], [f_56])).
% 9.01/3.25  tff(c_763, plain, (![A_57, A_121, B_58]: (k5_relat_1(k7_relat_1(k6_relat_1(A_57), A_121), B_58)=k7_relat_1(k7_relat_1(B_58, A_57), A_121) | ~v1_relat_1(B_58) | ~v1_relat_1(k6_relat_1(A_57)) | ~v1_relat_1(B_58))), inference(superposition, [status(thm), theory('equality')], [c_44, c_724])).
% 9.01/3.25  tff(c_2074, plain, (![A_193, A_194, B_195]: (k5_relat_1(k7_relat_1(k6_relat_1(A_193), A_194), B_195)=k7_relat_1(k7_relat_1(B_195, A_193), A_194) | ~v1_relat_1(B_195))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_763])).
% 9.01/3.25  tff(c_2132, plain, (![B_195, A_78]: (k7_relat_1(k7_relat_1(B_195, A_78), A_78)=k5_relat_1(k6_relat_1(A_78), B_195) | ~v1_relat_1(B_195))), inference(superposition, [status(thm), theory('equality')], [c_200, c_2074])).
% 9.01/3.25  tff(c_18, plain, (![A_32, B_33]: (v1_relat_1(k5_relat_1(A_32, B_33)) | ~v1_relat_1(B_33) | ~v1_relat_1(A_32))), inference(cnfTransformation, [status(thm)], [f_47])).
% 9.01/3.25  tff(c_677, plain, (![A_116, A_115]: (v1_relat_1(k4_relat_1(k5_relat_1(A_116, k6_relat_1(A_115)))) | ~v1_relat_1(k4_relat_1(A_116)) | ~v1_relat_1(k6_relat_1(A_115)) | ~v1_relat_1(A_116))), inference(superposition, [status(thm), theory('equality')], [c_664, c_18])).
% 9.01/3.25  tff(c_694, plain, (![A_116, A_115]: (v1_relat_1(k4_relat_1(k5_relat_1(A_116, k6_relat_1(A_115)))) | ~v1_relat_1(k4_relat_1(A_116)) | ~v1_relat_1(A_116))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_677])).
% 9.01/3.25  tff(c_803, plain, (![A_125, A_124]: (v1_relat_1(k5_relat_1(k6_relat_1(A_125), k6_relat_1(A_124))) | ~v1_relat_1(k4_relat_1(k6_relat_1(A_124))) | ~v1_relat_1(k6_relat_1(A_124)))), inference(superposition, [status(thm), theory('equality')], [c_797, c_694])).
% 9.01/3.25  tff(c_852, plain, (![A_126, A_127]: (v1_relat_1(k5_relat_1(k6_relat_1(A_126), k6_relat_1(A_127))))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_20, c_36, c_803])).
% 9.01/3.25  tff(c_862, plain, (![A_127, A_57]: (v1_relat_1(k7_relat_1(k6_relat_1(A_127), A_57)) | ~v1_relat_1(k6_relat_1(A_127)))), inference(superposition, [status(thm), theory('equality')], [c_44, c_852])).
% 9.01/3.25  tff(c_873, plain, (![A_127, A_57]: (v1_relat_1(k7_relat_1(k6_relat_1(A_127), A_57)))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_862])).
% 9.01/3.25  tff(c_995, plain, (![A_140, A_141]: (k4_relat_1(k7_relat_1(k6_relat_1(A_140), A_141))=k7_relat_1(k6_relat_1(A_141), A_140))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_920])).
% 9.01/3.25  tff(c_26, plain, (![A_39]: (k1_relat_1(k4_relat_1(A_39))=k2_relat_1(A_39) | ~v1_relat_1(A_39))), inference(cnfTransformation, [status(thm)], [f_62])).
% 9.01/3.25  tff(c_1010, plain, (![A_140, A_141]: (k2_relat_1(k7_relat_1(k6_relat_1(A_140), A_141))=k1_relat_1(k7_relat_1(k6_relat_1(A_141), A_140)) | ~v1_relat_1(k7_relat_1(k6_relat_1(A_140), A_141)))), inference(superposition, [status(thm), theory('equality')], [c_995, c_26])).
% 9.01/3.25  tff(c_1035, plain, (![A_140, A_141]: (k2_relat_1(k7_relat_1(k6_relat_1(A_140), A_141))=k3_xboole_0(A_141, A_140))), inference(demodulation, [status(thm), theory('equality')], [c_873, c_229, c_1010])).
% 9.01/3.25  tff(c_2520, plain, (![A_213, A_214]: (k1_relat_1(k7_relat_1(k4_relat_1(A_213), A_214))=k3_xboole_0(k2_relat_1(A_213), A_214) | ~v1_relat_1(k4_relat_1(A_213)) | ~v1_relat_1(A_213))), inference(superposition, [status(thm), theory('equality')], [c_26, c_210])).
% 9.01/3.25  tff(c_2566, plain, (![A_136, A_137, A_214]: (k3_xboole_0(k2_relat_1(k7_relat_1(k6_relat_1(A_136), A_137)), A_214)=k1_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(A_137), A_136), A_214)) | ~v1_relat_1(k4_relat_1(k7_relat_1(k6_relat_1(A_136), A_137))) | ~v1_relat_1(k7_relat_1(k6_relat_1(A_136), A_137)))), inference(superposition, [status(thm), theory('equality')], [c_958, c_2520])).
% 9.01/3.25  tff(c_3344, plain, (![A_232, A_233, A_234]: (k1_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(A_232), A_233), A_234))=k3_xboole_0(k3_xboole_0(A_232, A_233), A_234))), inference(demodulation, [status(thm), theory('equality')], [c_873, c_873, c_958, c_1035, c_2566])).
% 9.01/3.25  tff(c_3391, plain, (![A_232, A_78]: (k3_xboole_0(k3_xboole_0(A_232, A_78), A_78)=k1_relat_1(k5_relat_1(k6_relat_1(A_78), k6_relat_1(A_232))) | ~v1_relat_1(k6_relat_1(A_232)))), inference(superposition, [status(thm), theory('equality')], [c_2132, c_3344])).
% 9.01/3.25  tff(c_3429, plain, (![A_232, A_78]: (k3_xboole_0(k3_xboole_0(A_232, A_78), A_78)=k3_xboole_0(A_232, A_78))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_229, c_991, c_3391])).
% 9.01/3.25  tff(c_2136, plain, (![A_193, A_194]: (k7_relat_1(k7_relat_1(k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(A_193), A_194))), A_193), A_194)=k7_relat_1(k6_relat_1(A_193), A_194) | ~v1_relat_1(k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(A_193), A_194)))) | ~v1_relat_1(k7_relat_1(k6_relat_1(A_193), A_194)))), inference(superposition, [status(thm), theory('equality')], [c_40, c_2074])).
% 9.01/3.25  tff(c_5329, plain, (![A_273, A_274]: (k7_relat_1(k7_relat_1(k6_relat_1(k3_xboole_0(A_273, A_274)), A_274), A_273)=k7_relat_1(k6_relat_1(A_274), A_273))), inference(demodulation, [status(thm), theory('equality')], [c_873, c_20, c_1035, c_2136])).
% 9.01/3.25  tff(c_2582, plain, (![A_137, A_136, A_214]: (k1_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(A_137), A_136), A_214))=k3_xboole_0(k3_xboole_0(A_137, A_136), A_214))), inference(demodulation, [status(thm), theory('equality')], [c_873, c_873, c_958, c_1035, c_2566])).
% 9.01/3.25  tff(c_5353, plain, (![A_273, A_274]: (k3_xboole_0(k3_xboole_0(k3_xboole_0(A_273, A_274), A_274), A_273)=k1_relat_1(k7_relat_1(k6_relat_1(A_274), A_273)))), inference(superposition, [status(thm), theory('equality')], [c_5329, c_2582])).
% 9.01/3.25  tff(c_5454, plain, (![A_274, A_273]: (k3_xboole_0(A_274, A_273)=k3_xboole_0(A_273, A_274))), inference(demodulation, [status(thm), theory('equality')], [c_612, c_3429, c_229, c_5353])).
% 9.01/3.25  tff(c_5481, plain, (![A_276, A_275]: (k3_xboole_0(A_276, A_275)=k3_xboole_0(A_275, A_276))), inference(demodulation, [status(thm), theory('equality')], [c_612, c_3429, c_229, c_5353])).
% 9.01/3.25  tff(c_5704, plain, (![A_276, A_275]: (r1_tarski(k3_xboole_0(A_276, A_275), A_275))), inference(superposition, [status(thm), theory('equality')], [c_5481, c_2])).
% 9.01/3.25  tff(c_301, plain, (![A_89, A_50]: (k5_relat_1(k6_relat_1(A_89), k6_relat_1(A_50))=k6_relat_1(A_50) | ~r1_tarski(A_50, A_89))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_298])).
% 9.01/3.25  tff(c_753, plain, (![A_89, A_121, A_50]: (k5_relat_1(k7_relat_1(k6_relat_1(A_89), A_121), k6_relat_1(A_50))=k7_relat_1(k6_relat_1(A_50), A_121) | ~v1_relat_1(k6_relat_1(A_50)) | ~v1_relat_1(k6_relat_1(A_89)) | ~r1_tarski(A_50, A_89))), inference(superposition, [status(thm), theory('equality')], [c_301, c_724])).
% 9.01/3.25  tff(c_15035, plain, (![A_380, A_381, A_382]: (k5_relat_1(k7_relat_1(k6_relat_1(A_380), A_381), k6_relat_1(A_382))=k7_relat_1(k6_relat_1(A_382), A_381) | ~r1_tarski(A_382, A_380))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_20, c_753])).
% 9.01/3.25  tff(c_15095, plain, (![A_380, A_381]: (k7_relat_1(k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(A_380), A_381))), A_381)=k7_relat_1(k6_relat_1(A_380), A_381) | ~v1_relat_1(k7_relat_1(k6_relat_1(A_380), A_381)) | ~r1_tarski(k2_relat_1(k7_relat_1(k6_relat_1(A_380), A_381)), A_380))), inference(superposition, [status(thm), theory('equality')], [c_15035, c_40])).
% 9.01/3.25  tff(c_15227, plain, (![A_383, A_384]: (k7_relat_1(k6_relat_1(k3_xboole_0(A_383, A_384)), A_383)=k7_relat_1(k6_relat_1(A_384), A_383))), inference(demodulation, [status(thm), theory('equality')], [c_5704, c_1035, c_873, c_1035, c_15095])).
% 9.01/3.25  tff(c_512, plain, (![A_101, A_100]: (k7_relat_1(k6_relat_1(A_101), A_100)=k6_relat_1(A_101) | ~r1_tarski(A_101, A_100))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_474])).
% 9.01/3.25  tff(c_15306, plain, (![A_384, A_383]: (k7_relat_1(k6_relat_1(A_384), A_383)=k6_relat_1(k3_xboole_0(A_383, A_384)) | ~r1_tarski(k3_xboole_0(A_383, A_384), A_383))), inference(superposition, [status(thm), theory('equality')], [c_15227, c_512])).
% 9.01/3.25  tff(c_15458, plain, (![A_384, A_383]: (k7_relat_1(k6_relat_1(A_384), A_383)=k6_relat_1(k3_xboole_0(A_383, A_384)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_15306])).
% 9.01/3.25  tff(c_46, plain, (k5_relat_1(k6_relat_1('#skF_2'), k6_relat_1('#skF_1'))!=k6_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_106])).
% 9.01/3.25  tff(c_185, plain, (k7_relat_1(k6_relat_1('#skF_1'), '#skF_2')!=k6_relat_1(k3_xboole_0('#skF_1', '#skF_2')) | ~v1_relat_1(k6_relat_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_168, c_46])).
% 9.01/3.25  tff(c_204, plain, (k7_relat_1(k6_relat_1('#skF_1'), '#skF_2')!=k6_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_185])).
% 9.01/3.25  tff(c_15498, plain, (k6_relat_1(k3_xboole_0('#skF_2', '#skF_1'))!=k6_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_15458, c_204])).
% 9.01/3.25  tff(c_15508, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_5454, c_15498])).
% 9.01/3.25  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.01/3.25  
% 9.01/3.25  Inference rules
% 9.01/3.25  ----------------------
% 9.01/3.25  #Ref     : 0
% 9.01/3.25  #Sup     : 3877
% 9.01/3.25  #Fact    : 0
% 9.01/3.25  #Define  : 0
% 9.01/3.25  #Split   : 2
% 9.01/3.25  #Chain   : 0
% 9.01/3.25  #Close   : 0
% 9.01/3.25  
% 9.01/3.25  Ordering : KBO
% 9.01/3.25  
% 9.01/3.25  Simplification rules
% 9.01/3.25  ----------------------
% 9.01/3.25  #Subsume      : 607
% 9.01/3.25  #Demod        : 3540
% 9.01/3.25  #Tautology    : 1361
% 9.01/3.25  #SimpNegUnit  : 0
% 9.01/3.25  #BackRed      : 30
% 9.01/3.25  
% 9.01/3.25  #Partial instantiations: 0
% 9.01/3.25  #Strategies tried      : 1
% 9.01/3.25  
% 9.01/3.25  Timing (in seconds)
% 9.01/3.25  ----------------------
% 9.01/3.26  Preprocessing        : 0.34
% 9.01/3.26  Parsing              : 0.19
% 9.01/3.26  CNF conversion       : 0.02
% 9.01/3.26  Main loop            : 2.09
% 9.01/3.26  Inferencing          : 0.59
% 9.01/3.26  Reduction            : 0.91
% 9.01/3.26  Demodulation         : 0.75
% 9.01/3.26  BG Simplification    : 0.09
% 9.01/3.26  Subsumption          : 0.38
% 9.01/3.26  Abstraction          : 0.13
% 9.01/3.26  MUC search           : 0.00
% 9.01/3.26  Cooper               : 0.00
% 9.01/3.26  Total                : 2.47
% 9.01/3.26  Index Insertion      : 0.00
% 9.01/3.26  Index Deletion       : 0.00
% 9.01/3.26  Index Matching       : 0.00
% 9.01/3.26  BG Taut test         : 0.00
%------------------------------------------------------------------------------

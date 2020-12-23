%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:03:30 EST 2020

% Result     : Theorem 8.73s
% Output     : CNFRefutation 8.73s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 503 expanded)
%              Number of leaves         :   33 ( 192 expanded)
%              Depth                    :   12
%              Number of atoms          :  143 ( 896 expanded)
%              Number of equality atoms :   52 ( 298 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > v1_funct_1 > k2_enumset1 > k1_enumset1 > k8_relat_1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1

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

tff(f_113,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_60,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k8_relat_1(A,B) = k5_relat_1(B,k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_relat_1)).

tff(f_109,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k5_relat_1(k6_relat_1(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).

tff(f_81,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k8_relat_1(A,B)) = k3_xboole_0(k2_relat_1(B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t119_relat_1)).

tff(f_67,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => r1_tarski(k2_relat_1(k5_relat_1(A,B)),k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_relat_1)).

tff(f_93,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k5_relat_1(k6_relat_1(A),B) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_relat_1)).

tff(f_105,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k1_relat_1(k7_relat_1(B,A)) = k3_xboole_0(k1_relat_1(B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_relat_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_relat_1(B) )
     => v1_relat_1(k5_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).

tff(f_101,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k5_relat_1(A,k6_relat_1(k2_relat_1(A))) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_relat_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ! [C] :
          ( v1_relat_1(C)
         => k7_relat_1(k5_relat_1(B,C),A) = k5_relat_1(k7_relat_1(B,A),C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t112_relat_1)).

tff(f_33,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_116,negated_conjecture,(
    ~ ! [A,B] : k5_relat_1(k6_relat_1(B),k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_funct_1)).

tff(c_46,plain,(
    ! [A_43] : v1_relat_1(k6_relat_1(A_43)) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_22,plain,(
    ! [B_21,A_20] :
      ( k5_relat_1(B_21,k6_relat_1(A_20)) = k8_relat_1(A_20,B_21)
      | ~ v1_relat_1(B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_286,plain,(
    ! [A_76,B_77] :
      ( k5_relat_1(k6_relat_1(A_76),B_77) = k7_relat_1(B_77,A_76)
      | ~ v1_relat_1(B_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_325,plain,(
    ! [A_20,A_76] :
      ( k8_relat_1(A_20,k6_relat_1(A_76)) = k7_relat_1(k6_relat_1(A_20),A_76)
      | ~ v1_relat_1(k6_relat_1(A_20))
      | ~ v1_relat_1(k6_relat_1(A_76)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_286])).

tff(c_351,plain,(
    ! [A_20,A_76] : k8_relat_1(A_20,k6_relat_1(A_76)) = k7_relat_1(k6_relat_1(A_20),A_76) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_46,c_325])).

tff(c_30,plain,(
    ! [A_32] : k2_relat_1(k6_relat_1(A_32)) = A_32 ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_411,plain,(
    ! [B_87,A_88] :
      ( k3_xboole_0(k2_relat_1(B_87),A_88) = k2_relat_1(k8_relat_1(A_88,B_87))
      | ~ v1_relat_1(B_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_423,plain,(
    ! [A_88,A_32] :
      ( k2_relat_1(k8_relat_1(A_88,k6_relat_1(A_32))) = k3_xboole_0(A_32,A_88)
      | ~ v1_relat_1(k6_relat_1(A_32)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_411])).

tff(c_427,plain,(
    ! [A_88,A_32] : k2_relat_1(k7_relat_1(k6_relat_1(A_88),A_32)) = k3_xboole_0(A_32,A_88) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_351,c_423])).

tff(c_660,plain,(
    ! [A_109,B_110] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_109,B_110)),k2_relat_1(B_110))
      | ~ v1_relat_1(B_110)
      | ~ v1_relat_1(A_109) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_671,plain,(
    ! [A_20,B_21] :
      ( r1_tarski(k2_relat_1(k8_relat_1(A_20,B_21)),k2_relat_1(k6_relat_1(A_20)))
      | ~ v1_relat_1(k6_relat_1(A_20))
      | ~ v1_relat_1(B_21)
      | ~ v1_relat_1(B_21) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_660])).

tff(c_699,plain,(
    ! [A_111,B_112] :
      ( r1_tarski(k2_relat_1(k8_relat_1(A_111,B_112)),A_111)
      | ~ v1_relat_1(B_112) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_30,c_671])).

tff(c_704,plain,(
    ! [A_20,A_76] :
      ( r1_tarski(k2_relat_1(k7_relat_1(k6_relat_1(A_20),A_76)),A_20)
      | ~ v1_relat_1(k6_relat_1(A_76)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_351,c_699])).

tff(c_710,plain,(
    ! [A_76,A_20] : r1_tarski(k3_xboole_0(A_76,A_20),A_20) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_427,c_704])).

tff(c_28,plain,(
    ! [A_32] : k1_relat_1(k6_relat_1(A_32)) = A_32 ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_607,plain,(
    ! [A_103,B_104] :
      ( k5_relat_1(k6_relat_1(A_103),B_104) = B_104
      | ~ r1_tarski(k1_relat_1(B_104),A_103)
      | ~ v1_relat_1(B_104) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_613,plain,(
    ! [A_103,A_32] :
      ( k5_relat_1(k6_relat_1(A_103),k6_relat_1(A_32)) = k6_relat_1(A_32)
      | ~ r1_tarski(A_32,A_103)
      | ~ v1_relat_1(k6_relat_1(A_32)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_607])).

tff(c_1166,plain,(
    ! [A_134,A_135] :
      ( k5_relat_1(k6_relat_1(A_134),k6_relat_1(A_135)) = k6_relat_1(A_135)
      | ~ r1_tarski(A_135,A_134) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_613])).

tff(c_44,plain,(
    ! [A_41,B_42] :
      ( k5_relat_1(k6_relat_1(A_41),B_42) = k7_relat_1(B_42,A_41)
      | ~ v1_relat_1(B_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_1184,plain,(
    ! [A_135,A_134] :
      ( k7_relat_1(k6_relat_1(A_135),A_134) = k6_relat_1(A_135)
      | ~ v1_relat_1(k6_relat_1(A_135))
      | ~ r1_tarski(A_135,A_134) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1166,c_44])).

tff(c_1278,plain,(
    ! [A_138,A_139] :
      ( k7_relat_1(k6_relat_1(A_138),A_139) = k6_relat_1(A_138)
      | ~ r1_tarski(A_138,A_139) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_1184])).

tff(c_460,plain,(
    ! [B_93,A_94] :
      ( k3_xboole_0(k1_relat_1(B_93),A_94) = k1_relat_1(k7_relat_1(B_93,A_94))
      | ~ v1_relat_1(B_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_472,plain,(
    ! [A_32,A_94] :
      ( k1_relat_1(k7_relat_1(k6_relat_1(A_32),A_94)) = k3_xboole_0(A_32,A_94)
      | ~ v1_relat_1(k6_relat_1(A_32)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_460])).

tff(c_476,plain,(
    ! [A_32,A_94] : k1_relat_1(k7_relat_1(k6_relat_1(A_32),A_94)) = k3_xboole_0(A_32,A_94) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_472])).

tff(c_1304,plain,(
    ! [A_138,A_139] :
      ( k3_xboole_0(A_138,A_139) = k1_relat_1(k6_relat_1(A_138))
      | ~ r1_tarski(A_138,A_139) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1278,c_476])).

tff(c_1366,plain,(
    ! [A_140,A_141] :
      ( k3_xboole_0(A_140,A_141) = A_140
      | ~ r1_tarski(A_140,A_141) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_1304])).

tff(c_1423,plain,(
    ! [A_76,A_20] : k3_xboole_0(k3_xboole_0(A_76,A_20),A_20) = k3_xboole_0(A_76,A_20) ),
    inference(resolution,[status(thm)],[c_710,c_1366])).

tff(c_384,plain,(
    ! [A_83,A_84] : k8_relat_1(A_83,k6_relat_1(A_84)) = k7_relat_1(k6_relat_1(A_83),A_84) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_46,c_325])).

tff(c_193,plain,(
    ! [B_66,A_67] :
      ( k5_relat_1(B_66,k6_relat_1(A_67)) = k8_relat_1(A_67,B_66)
      | ~ v1_relat_1(B_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_16,plain,(
    ! [A_12,B_13] :
      ( v1_relat_1(k5_relat_1(A_12,B_13))
      | ~ v1_relat_1(B_13)
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_203,plain,(
    ! [A_67,B_66] :
      ( v1_relat_1(k8_relat_1(A_67,B_66))
      | ~ v1_relat_1(k6_relat_1(A_67))
      | ~ v1_relat_1(B_66)
      | ~ v1_relat_1(B_66) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_193,c_16])).

tff(c_237,plain,(
    ! [A_67,B_66] :
      ( v1_relat_1(k8_relat_1(A_67,B_66))
      | ~ v1_relat_1(B_66) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_203])).

tff(c_394,plain,(
    ! [A_83,A_84] :
      ( v1_relat_1(k7_relat_1(k6_relat_1(A_83),A_84))
      | ~ v1_relat_1(k6_relat_1(A_84)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_384,c_237])).

tff(c_404,plain,(
    ! [A_83,A_84] : v1_relat_1(k7_relat_1(k6_relat_1(A_83),A_84)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_394])).

tff(c_40,plain,(
    ! [A_38] :
      ( k5_relat_1(A_38,k6_relat_1(k2_relat_1(A_38))) = A_38
      | ~ v1_relat_1(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_823,plain,(
    ! [B_120,C_121,A_122] :
      ( k7_relat_1(k5_relat_1(B_120,C_121),A_122) = k5_relat_1(k7_relat_1(B_120,A_122),C_121)
      | ~ v1_relat_1(C_121)
      | ~ v1_relat_1(B_120) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_849,plain,(
    ! [A_41,A_122,B_42] :
      ( k5_relat_1(k7_relat_1(k6_relat_1(A_41),A_122),B_42) = k7_relat_1(k7_relat_1(B_42,A_41),A_122)
      | ~ v1_relat_1(B_42)
      | ~ v1_relat_1(k6_relat_1(A_41))
      | ~ v1_relat_1(B_42) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_823])).

tff(c_2494,plain,(
    ! [A_177,A_178,B_179] :
      ( k5_relat_1(k7_relat_1(k6_relat_1(A_177),A_178),B_179) = k7_relat_1(k7_relat_1(B_179,A_177),A_178)
      | ~ v1_relat_1(B_179) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_849])).

tff(c_2561,plain,(
    ! [A_177,A_178] :
      ( k7_relat_1(k7_relat_1(k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(A_177),A_178))),A_177),A_178) = k7_relat_1(k6_relat_1(A_177),A_178)
      | ~ v1_relat_1(k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(A_177),A_178))))
      | ~ v1_relat_1(k7_relat_1(k6_relat_1(A_177),A_178)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_2494])).

tff(c_11299,plain,(
    ! [A_350,A_351] : k7_relat_1(k7_relat_1(k6_relat_1(k3_xboole_0(A_350,A_351)),A_351),A_350) = k7_relat_1(k6_relat_1(A_351),A_350) ),
    inference(demodulation,[status(thm),theory(equality)],[c_404,c_46,c_427,c_2561])).

tff(c_8,plain,(
    ! [A_3,B_4] : r1_tarski(k3_xboole_0(A_3,B_4),A_3) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_905,plain,(
    ! [B_125,A_126] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_125,A_126)),k1_relat_1(B_125))
      | ~ v1_relat_1(B_125) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_460,c_8])).

tff(c_922,plain,(
    ! [A_32,A_94,A_126] :
      ( r1_tarski(k1_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(A_32),A_94),A_126)),k3_xboole_0(A_32,A_94))
      | ~ v1_relat_1(k7_relat_1(k6_relat_1(A_32),A_94)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_476,c_905])).

tff(c_935,plain,(
    ! [A_32,A_94,A_126] : r1_tarski(k1_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(A_32),A_94),A_126)),k3_xboole_0(A_32,A_94)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_404,c_922])).

tff(c_11312,plain,(
    ! [A_351,A_350] : r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1(A_351),A_350)),k3_xboole_0(k3_xboole_0(A_350,A_351),A_351)) ),
    inference(superposition,[status(thm),theory(equality)],[c_11299,c_935])).

tff(c_11473,plain,(
    ! [A_351,A_350] : r1_tarski(k3_xboole_0(A_351,A_350),k3_xboole_0(A_350,A_351)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1423,c_476,c_11312])).

tff(c_11527,plain,(
    ! [A_352,A_353] : r1_tarski(k3_xboole_0(A_352,A_353),k3_xboole_0(A_353,A_352)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1423,c_476,c_11312])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_11540,plain,(
    ! [A_353,A_352] :
      ( k3_xboole_0(A_353,A_352) = k3_xboole_0(A_352,A_353)
      | ~ r1_tarski(k3_xboole_0(A_353,A_352),k3_xboole_0(A_352,A_353)) ) ),
    inference(resolution,[status(thm)],[c_11527,c_2])).

tff(c_11699,plain,(
    ! [A_353,A_352] : k3_xboole_0(A_353,A_352) = k3_xboole_0(A_352,A_353) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11473,c_11540])).

tff(c_1244,plain,(
    ! [A_135,A_134] :
      ( k7_relat_1(k6_relat_1(A_135),A_134) = k6_relat_1(A_135)
      | ~ r1_tarski(A_135,A_134) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_1184])).

tff(c_11459,plain,(
    ! [A_350,A_134] :
      ( k7_relat_1(k6_relat_1(k3_xboole_0(A_350,A_134)),A_350) = k7_relat_1(k6_relat_1(A_134),A_350)
      | ~ r1_tarski(k3_xboole_0(A_350,A_134),A_134) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1244,c_11299])).

tff(c_16682,plain,(
    ! [A_392,A_393] : k7_relat_1(k6_relat_1(k3_xboole_0(A_392,A_393)),A_392) = k7_relat_1(k6_relat_1(A_393),A_392) ),
    inference(demodulation,[status(thm),theory(equality)],[c_710,c_11459])).

tff(c_16782,plain,(
    ! [A_393,A_392] :
      ( k7_relat_1(k6_relat_1(A_393),A_392) = k6_relat_1(k3_xboole_0(A_392,A_393))
      | ~ r1_tarski(k3_xboole_0(A_392,A_393),A_392) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16682,c_1244])).

tff(c_16958,plain,(
    ! [A_393,A_392] : k7_relat_1(k6_relat_1(A_393),A_392) = k6_relat_1(k3_xboole_0(A_392,A_393)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_16782])).

tff(c_50,plain,(
    k5_relat_1(k6_relat_1('#skF_2'),k6_relat_1('#skF_1')) != k6_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_314,plain,
    ( k7_relat_1(k6_relat_1('#skF_1'),'#skF_2') != k6_relat_1(k3_xboole_0('#skF_1','#skF_2'))
    | ~ v1_relat_1(k6_relat_1('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_286,c_50])).

tff(c_348,plain,(
    k7_relat_1(k6_relat_1('#skF_1'),'#skF_2') != k6_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_314])).

tff(c_17262,plain,(
    k6_relat_1(k3_xboole_0('#skF_2','#skF_1')) != k6_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16958,c_348])).

tff(c_17276,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_11699,c_17262])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:09:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.73/3.20  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.73/3.21  
% 8.73/3.21  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.73/3.21  %$ r1_tarski > v1_relat_1 > v1_funct_1 > k2_enumset1 > k1_enumset1 > k8_relat_1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1
% 8.73/3.21  
% 8.73/3.21  %Foreground sorts:
% 8.73/3.21  
% 8.73/3.21  
% 8.73/3.21  %Background operators:
% 8.73/3.21  
% 8.73/3.21  
% 8.73/3.21  %Foreground operators:
% 8.73/3.21  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 8.73/3.21  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 8.73/3.21  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.73/3.21  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 8.73/3.21  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 8.73/3.21  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.73/3.21  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 8.73/3.21  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 8.73/3.21  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 8.73/3.21  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 8.73/3.21  tff('#skF_2', type, '#skF_2': $i).
% 8.73/3.21  tff('#skF_1', type, '#skF_1': $i).
% 8.73/3.21  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.73/3.21  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 8.73/3.21  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 8.73/3.21  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.73/3.21  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 8.73/3.21  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 8.73/3.21  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 8.73/3.21  
% 8.73/3.23  tff(f_113, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc3_funct_1)).
% 8.73/3.23  tff(f_60, axiom, (![A, B]: (v1_relat_1(B) => (k8_relat_1(A, B) = k5_relat_1(B, k6_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t123_relat_1)).
% 8.73/3.23  tff(f_109, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_relat_1)).
% 8.73/3.23  tff(f_81, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 8.73/3.23  tff(f_56, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k8_relat_1(A, B)) = k3_xboole_0(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t119_relat_1)).
% 8.73/3.23  tff(f_67, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k2_relat_1(k5_relat_1(A, B)), k2_relat_1(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t45_relat_1)).
% 8.73/3.23  tff(f_93, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k5_relat_1(k6_relat_1(A), B) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t77_relat_1)).
% 8.73/3.23  tff(f_105, axiom, (![A, B]: (v1_relat_1(B) => (k1_relat_1(k7_relat_1(B, A)) = k3_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t90_relat_1)).
% 8.73/3.23  tff(f_45, axiom, (![A, B]: ((v1_relat_1(A) & v1_relat_1(B)) => v1_relat_1(k5_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k5_relat_1)).
% 8.73/3.23  tff(f_101, axiom, (![A]: (v1_relat_1(A) => (k5_relat_1(A, k6_relat_1(k2_relat_1(A))) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t80_relat_1)).
% 8.73/3.23  tff(f_52, axiom, (![A, B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (k7_relat_1(k5_relat_1(B, C), A) = k5_relat_1(k7_relat_1(B, A), C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t112_relat_1)).
% 8.73/3.23  tff(f_33, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 8.73/3.23  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 8.73/3.23  tff(f_116, negated_conjecture, ~(![A, B]: (k5_relat_1(k6_relat_1(B), k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_funct_1)).
% 8.73/3.23  tff(c_46, plain, (![A_43]: (v1_relat_1(k6_relat_1(A_43)))), inference(cnfTransformation, [status(thm)], [f_113])).
% 8.73/3.23  tff(c_22, plain, (![B_21, A_20]: (k5_relat_1(B_21, k6_relat_1(A_20))=k8_relat_1(A_20, B_21) | ~v1_relat_1(B_21))), inference(cnfTransformation, [status(thm)], [f_60])).
% 8.73/3.23  tff(c_286, plain, (![A_76, B_77]: (k5_relat_1(k6_relat_1(A_76), B_77)=k7_relat_1(B_77, A_76) | ~v1_relat_1(B_77))), inference(cnfTransformation, [status(thm)], [f_109])).
% 8.73/3.23  tff(c_325, plain, (![A_20, A_76]: (k8_relat_1(A_20, k6_relat_1(A_76))=k7_relat_1(k6_relat_1(A_20), A_76) | ~v1_relat_1(k6_relat_1(A_20)) | ~v1_relat_1(k6_relat_1(A_76)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_286])).
% 8.73/3.23  tff(c_351, plain, (![A_20, A_76]: (k8_relat_1(A_20, k6_relat_1(A_76))=k7_relat_1(k6_relat_1(A_20), A_76))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_46, c_325])).
% 8.73/3.23  tff(c_30, plain, (![A_32]: (k2_relat_1(k6_relat_1(A_32))=A_32)), inference(cnfTransformation, [status(thm)], [f_81])).
% 8.73/3.23  tff(c_411, plain, (![B_87, A_88]: (k3_xboole_0(k2_relat_1(B_87), A_88)=k2_relat_1(k8_relat_1(A_88, B_87)) | ~v1_relat_1(B_87))), inference(cnfTransformation, [status(thm)], [f_56])).
% 8.73/3.23  tff(c_423, plain, (![A_88, A_32]: (k2_relat_1(k8_relat_1(A_88, k6_relat_1(A_32)))=k3_xboole_0(A_32, A_88) | ~v1_relat_1(k6_relat_1(A_32)))), inference(superposition, [status(thm), theory('equality')], [c_30, c_411])).
% 8.73/3.23  tff(c_427, plain, (![A_88, A_32]: (k2_relat_1(k7_relat_1(k6_relat_1(A_88), A_32))=k3_xboole_0(A_32, A_88))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_351, c_423])).
% 8.73/3.23  tff(c_660, plain, (![A_109, B_110]: (r1_tarski(k2_relat_1(k5_relat_1(A_109, B_110)), k2_relat_1(B_110)) | ~v1_relat_1(B_110) | ~v1_relat_1(A_109))), inference(cnfTransformation, [status(thm)], [f_67])).
% 8.73/3.23  tff(c_671, plain, (![A_20, B_21]: (r1_tarski(k2_relat_1(k8_relat_1(A_20, B_21)), k2_relat_1(k6_relat_1(A_20))) | ~v1_relat_1(k6_relat_1(A_20)) | ~v1_relat_1(B_21) | ~v1_relat_1(B_21))), inference(superposition, [status(thm), theory('equality')], [c_22, c_660])).
% 8.73/3.23  tff(c_699, plain, (![A_111, B_112]: (r1_tarski(k2_relat_1(k8_relat_1(A_111, B_112)), A_111) | ~v1_relat_1(B_112))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_30, c_671])).
% 8.73/3.23  tff(c_704, plain, (![A_20, A_76]: (r1_tarski(k2_relat_1(k7_relat_1(k6_relat_1(A_20), A_76)), A_20) | ~v1_relat_1(k6_relat_1(A_76)))), inference(superposition, [status(thm), theory('equality')], [c_351, c_699])).
% 8.73/3.23  tff(c_710, plain, (![A_76, A_20]: (r1_tarski(k3_xboole_0(A_76, A_20), A_20))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_427, c_704])).
% 8.73/3.23  tff(c_28, plain, (![A_32]: (k1_relat_1(k6_relat_1(A_32))=A_32)), inference(cnfTransformation, [status(thm)], [f_81])).
% 8.73/3.23  tff(c_607, plain, (![A_103, B_104]: (k5_relat_1(k6_relat_1(A_103), B_104)=B_104 | ~r1_tarski(k1_relat_1(B_104), A_103) | ~v1_relat_1(B_104))), inference(cnfTransformation, [status(thm)], [f_93])).
% 8.73/3.23  tff(c_613, plain, (![A_103, A_32]: (k5_relat_1(k6_relat_1(A_103), k6_relat_1(A_32))=k6_relat_1(A_32) | ~r1_tarski(A_32, A_103) | ~v1_relat_1(k6_relat_1(A_32)))), inference(superposition, [status(thm), theory('equality')], [c_28, c_607])).
% 8.73/3.23  tff(c_1166, plain, (![A_134, A_135]: (k5_relat_1(k6_relat_1(A_134), k6_relat_1(A_135))=k6_relat_1(A_135) | ~r1_tarski(A_135, A_134))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_613])).
% 8.73/3.23  tff(c_44, plain, (![A_41, B_42]: (k5_relat_1(k6_relat_1(A_41), B_42)=k7_relat_1(B_42, A_41) | ~v1_relat_1(B_42))), inference(cnfTransformation, [status(thm)], [f_109])).
% 8.73/3.23  tff(c_1184, plain, (![A_135, A_134]: (k7_relat_1(k6_relat_1(A_135), A_134)=k6_relat_1(A_135) | ~v1_relat_1(k6_relat_1(A_135)) | ~r1_tarski(A_135, A_134))), inference(superposition, [status(thm), theory('equality')], [c_1166, c_44])).
% 8.73/3.23  tff(c_1278, plain, (![A_138, A_139]: (k7_relat_1(k6_relat_1(A_138), A_139)=k6_relat_1(A_138) | ~r1_tarski(A_138, A_139))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_1184])).
% 8.73/3.23  tff(c_460, plain, (![B_93, A_94]: (k3_xboole_0(k1_relat_1(B_93), A_94)=k1_relat_1(k7_relat_1(B_93, A_94)) | ~v1_relat_1(B_93))), inference(cnfTransformation, [status(thm)], [f_105])).
% 8.73/3.23  tff(c_472, plain, (![A_32, A_94]: (k1_relat_1(k7_relat_1(k6_relat_1(A_32), A_94))=k3_xboole_0(A_32, A_94) | ~v1_relat_1(k6_relat_1(A_32)))), inference(superposition, [status(thm), theory('equality')], [c_28, c_460])).
% 8.73/3.23  tff(c_476, plain, (![A_32, A_94]: (k1_relat_1(k7_relat_1(k6_relat_1(A_32), A_94))=k3_xboole_0(A_32, A_94))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_472])).
% 8.73/3.23  tff(c_1304, plain, (![A_138, A_139]: (k3_xboole_0(A_138, A_139)=k1_relat_1(k6_relat_1(A_138)) | ~r1_tarski(A_138, A_139))), inference(superposition, [status(thm), theory('equality')], [c_1278, c_476])).
% 8.73/3.23  tff(c_1366, plain, (![A_140, A_141]: (k3_xboole_0(A_140, A_141)=A_140 | ~r1_tarski(A_140, A_141))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_1304])).
% 8.73/3.23  tff(c_1423, plain, (![A_76, A_20]: (k3_xboole_0(k3_xboole_0(A_76, A_20), A_20)=k3_xboole_0(A_76, A_20))), inference(resolution, [status(thm)], [c_710, c_1366])).
% 8.73/3.23  tff(c_384, plain, (![A_83, A_84]: (k8_relat_1(A_83, k6_relat_1(A_84))=k7_relat_1(k6_relat_1(A_83), A_84))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_46, c_325])).
% 8.73/3.23  tff(c_193, plain, (![B_66, A_67]: (k5_relat_1(B_66, k6_relat_1(A_67))=k8_relat_1(A_67, B_66) | ~v1_relat_1(B_66))), inference(cnfTransformation, [status(thm)], [f_60])).
% 8.73/3.23  tff(c_16, plain, (![A_12, B_13]: (v1_relat_1(k5_relat_1(A_12, B_13)) | ~v1_relat_1(B_13) | ~v1_relat_1(A_12))), inference(cnfTransformation, [status(thm)], [f_45])).
% 8.73/3.23  tff(c_203, plain, (![A_67, B_66]: (v1_relat_1(k8_relat_1(A_67, B_66)) | ~v1_relat_1(k6_relat_1(A_67)) | ~v1_relat_1(B_66) | ~v1_relat_1(B_66))), inference(superposition, [status(thm), theory('equality')], [c_193, c_16])).
% 8.73/3.23  tff(c_237, plain, (![A_67, B_66]: (v1_relat_1(k8_relat_1(A_67, B_66)) | ~v1_relat_1(B_66))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_203])).
% 8.73/3.23  tff(c_394, plain, (![A_83, A_84]: (v1_relat_1(k7_relat_1(k6_relat_1(A_83), A_84)) | ~v1_relat_1(k6_relat_1(A_84)))), inference(superposition, [status(thm), theory('equality')], [c_384, c_237])).
% 8.73/3.23  tff(c_404, plain, (![A_83, A_84]: (v1_relat_1(k7_relat_1(k6_relat_1(A_83), A_84)))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_394])).
% 8.73/3.23  tff(c_40, plain, (![A_38]: (k5_relat_1(A_38, k6_relat_1(k2_relat_1(A_38)))=A_38 | ~v1_relat_1(A_38))), inference(cnfTransformation, [status(thm)], [f_101])).
% 8.73/3.23  tff(c_823, plain, (![B_120, C_121, A_122]: (k7_relat_1(k5_relat_1(B_120, C_121), A_122)=k5_relat_1(k7_relat_1(B_120, A_122), C_121) | ~v1_relat_1(C_121) | ~v1_relat_1(B_120))), inference(cnfTransformation, [status(thm)], [f_52])).
% 8.73/3.23  tff(c_849, plain, (![A_41, A_122, B_42]: (k5_relat_1(k7_relat_1(k6_relat_1(A_41), A_122), B_42)=k7_relat_1(k7_relat_1(B_42, A_41), A_122) | ~v1_relat_1(B_42) | ~v1_relat_1(k6_relat_1(A_41)) | ~v1_relat_1(B_42))), inference(superposition, [status(thm), theory('equality')], [c_44, c_823])).
% 8.73/3.23  tff(c_2494, plain, (![A_177, A_178, B_179]: (k5_relat_1(k7_relat_1(k6_relat_1(A_177), A_178), B_179)=k7_relat_1(k7_relat_1(B_179, A_177), A_178) | ~v1_relat_1(B_179))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_849])).
% 8.73/3.23  tff(c_2561, plain, (![A_177, A_178]: (k7_relat_1(k7_relat_1(k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(A_177), A_178))), A_177), A_178)=k7_relat_1(k6_relat_1(A_177), A_178) | ~v1_relat_1(k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(A_177), A_178)))) | ~v1_relat_1(k7_relat_1(k6_relat_1(A_177), A_178)))), inference(superposition, [status(thm), theory('equality')], [c_40, c_2494])).
% 8.73/3.23  tff(c_11299, plain, (![A_350, A_351]: (k7_relat_1(k7_relat_1(k6_relat_1(k3_xboole_0(A_350, A_351)), A_351), A_350)=k7_relat_1(k6_relat_1(A_351), A_350))), inference(demodulation, [status(thm), theory('equality')], [c_404, c_46, c_427, c_2561])).
% 8.73/3.23  tff(c_8, plain, (![A_3, B_4]: (r1_tarski(k3_xboole_0(A_3, B_4), A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 8.73/3.23  tff(c_905, plain, (![B_125, A_126]: (r1_tarski(k1_relat_1(k7_relat_1(B_125, A_126)), k1_relat_1(B_125)) | ~v1_relat_1(B_125))), inference(superposition, [status(thm), theory('equality')], [c_460, c_8])).
% 8.73/3.23  tff(c_922, plain, (![A_32, A_94, A_126]: (r1_tarski(k1_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(A_32), A_94), A_126)), k3_xboole_0(A_32, A_94)) | ~v1_relat_1(k7_relat_1(k6_relat_1(A_32), A_94)))), inference(superposition, [status(thm), theory('equality')], [c_476, c_905])).
% 8.73/3.23  tff(c_935, plain, (![A_32, A_94, A_126]: (r1_tarski(k1_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(A_32), A_94), A_126)), k3_xboole_0(A_32, A_94)))), inference(demodulation, [status(thm), theory('equality')], [c_404, c_922])).
% 8.73/3.23  tff(c_11312, plain, (![A_351, A_350]: (r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1(A_351), A_350)), k3_xboole_0(k3_xboole_0(A_350, A_351), A_351)))), inference(superposition, [status(thm), theory('equality')], [c_11299, c_935])).
% 8.73/3.23  tff(c_11473, plain, (![A_351, A_350]: (r1_tarski(k3_xboole_0(A_351, A_350), k3_xboole_0(A_350, A_351)))), inference(demodulation, [status(thm), theory('equality')], [c_1423, c_476, c_11312])).
% 8.73/3.23  tff(c_11527, plain, (![A_352, A_353]: (r1_tarski(k3_xboole_0(A_352, A_353), k3_xboole_0(A_353, A_352)))), inference(demodulation, [status(thm), theory('equality')], [c_1423, c_476, c_11312])).
% 8.73/3.23  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 8.73/3.23  tff(c_11540, plain, (![A_353, A_352]: (k3_xboole_0(A_353, A_352)=k3_xboole_0(A_352, A_353) | ~r1_tarski(k3_xboole_0(A_353, A_352), k3_xboole_0(A_352, A_353)))), inference(resolution, [status(thm)], [c_11527, c_2])).
% 8.73/3.23  tff(c_11699, plain, (![A_353, A_352]: (k3_xboole_0(A_353, A_352)=k3_xboole_0(A_352, A_353))), inference(demodulation, [status(thm), theory('equality')], [c_11473, c_11540])).
% 8.73/3.23  tff(c_1244, plain, (![A_135, A_134]: (k7_relat_1(k6_relat_1(A_135), A_134)=k6_relat_1(A_135) | ~r1_tarski(A_135, A_134))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_1184])).
% 8.73/3.23  tff(c_11459, plain, (![A_350, A_134]: (k7_relat_1(k6_relat_1(k3_xboole_0(A_350, A_134)), A_350)=k7_relat_1(k6_relat_1(A_134), A_350) | ~r1_tarski(k3_xboole_0(A_350, A_134), A_134))), inference(superposition, [status(thm), theory('equality')], [c_1244, c_11299])).
% 8.73/3.23  tff(c_16682, plain, (![A_392, A_393]: (k7_relat_1(k6_relat_1(k3_xboole_0(A_392, A_393)), A_392)=k7_relat_1(k6_relat_1(A_393), A_392))), inference(demodulation, [status(thm), theory('equality')], [c_710, c_11459])).
% 8.73/3.23  tff(c_16782, plain, (![A_393, A_392]: (k7_relat_1(k6_relat_1(A_393), A_392)=k6_relat_1(k3_xboole_0(A_392, A_393)) | ~r1_tarski(k3_xboole_0(A_392, A_393), A_392))), inference(superposition, [status(thm), theory('equality')], [c_16682, c_1244])).
% 8.73/3.23  tff(c_16958, plain, (![A_393, A_392]: (k7_relat_1(k6_relat_1(A_393), A_392)=k6_relat_1(k3_xboole_0(A_392, A_393)))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_16782])).
% 8.73/3.23  tff(c_50, plain, (k5_relat_1(k6_relat_1('#skF_2'), k6_relat_1('#skF_1'))!=k6_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_116])).
% 8.73/3.23  tff(c_314, plain, (k7_relat_1(k6_relat_1('#skF_1'), '#skF_2')!=k6_relat_1(k3_xboole_0('#skF_1', '#skF_2')) | ~v1_relat_1(k6_relat_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_286, c_50])).
% 8.73/3.23  tff(c_348, plain, (k7_relat_1(k6_relat_1('#skF_1'), '#skF_2')!=k6_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_314])).
% 8.73/3.23  tff(c_17262, plain, (k6_relat_1(k3_xboole_0('#skF_2', '#skF_1'))!=k6_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_16958, c_348])).
% 8.73/3.23  tff(c_17276, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_11699, c_17262])).
% 8.73/3.23  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.73/3.23  
% 8.73/3.23  Inference rules
% 8.73/3.23  ----------------------
% 8.73/3.23  #Ref     : 0
% 8.73/3.23  #Sup     : 4247
% 8.73/3.23  #Fact    : 0
% 8.73/3.23  #Define  : 0
% 8.73/3.23  #Split   : 1
% 8.73/3.23  #Chain   : 0
% 8.73/3.23  #Close   : 0
% 8.73/3.23  
% 8.73/3.23  Ordering : KBO
% 8.73/3.23  
% 8.73/3.23  Simplification rules
% 8.73/3.23  ----------------------
% 8.73/3.23  #Subsume      : 538
% 8.73/3.23  #Demod        : 3853
% 8.73/3.23  #Tautology    : 1500
% 8.73/3.23  #SimpNegUnit  : 0
% 8.73/3.23  #BackRed      : 51
% 8.73/3.23  
% 8.73/3.23  #Partial instantiations: 0
% 8.73/3.23  #Strategies tried      : 1
% 8.73/3.23  
% 8.73/3.23  Timing (in seconds)
% 8.73/3.23  ----------------------
% 8.73/3.23  Preprocessing        : 0.32
% 8.73/3.23  Parsing              : 0.17
% 8.73/3.23  CNF conversion       : 0.02
% 8.73/3.23  Main loop            : 2.08
% 8.73/3.23  Inferencing          : 0.60
% 8.73/3.23  Reduction            : 0.83
% 8.73/3.23  Demodulation         : 0.68
% 8.73/3.23  BG Simplification    : 0.08
% 8.73/3.23  Subsumption          : 0.44
% 8.73/3.23  Abstraction          : 0.13
% 8.73/3.23  MUC search           : 0.00
% 8.73/3.23  Cooper               : 0.00
% 8.73/3.23  Total                : 2.44
% 8.73/3.23  Index Insertion      : 0.00
% 8.73/3.23  Index Deletion       : 0.00
% 8.73/3.23  Index Matching       : 0.00
% 8.73/3.23  BG Taut test         : 0.00
%------------------------------------------------------------------------------

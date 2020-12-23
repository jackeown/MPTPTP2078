%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:03:32 EST 2020

% Result     : Theorem 14.29s
% Output     : CNFRefutation 14.29s
% Verified   : 
% Statistics : Number of formulae       :  128 ( 907 expanded)
%              Number of leaves         :   38 ( 339 expanded)
%              Depth                    :   15
%              Number of atoms          :  201 (1465 expanded)
%              Number of equality atoms :   94 ( 552 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    8 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k8_relat_1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k6_relat_1 > k4_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1

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

tff(k4_relat_1,type,(
    k4_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_27,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_88,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_49,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_112,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k5_relat_1(k6_relat_1(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).

tff(f_60,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k8_relat_1(A,B) = k5_relat_1(B,k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_relat_1)).

tff(f_96,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k5_relat_1(k6_relat_1(A),B) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_relat_1)).

tff(f_108,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k1_relat_1(k7_relat_1(B,A)) = k3_xboole_0(k1_relat_1(B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_relat_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_relat_1(B) )
     => v1_relat_1(k5_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).

tff(f_104,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k5_relat_1(A,k6_relat_1(k2_relat_1(A))) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_relat_1)).

tff(f_67,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ! [C] :
          ( v1_relat_1(C)
         => k8_relat_1(A,k5_relat_1(B,C)) = k5_relat_1(B,k8_relat_1(A,C)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t139_relat_1)).

tff(f_90,axiom,(
    ! [A] : k4_relat_1(k6_relat_1(A)) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_relat_1)).

tff(f_74,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k4_relat_1(k5_relat_1(A,B)) = k5_relat_1(k4_relat_1(B),k4_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_relat_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ! [C] :
          ( v1_relat_1(C)
         => k7_relat_1(k5_relat_1(B,C),A) = k5_relat_1(k7_relat_1(B,A),C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t112_relat_1)).

tff(f_100,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k5_relat_1(k6_relat_1(k1_relat_1(A)),A) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_relat_1)).

tff(f_115,negated_conjecture,(
    ~ ! [A,B] : k5_relat_1(k6_relat_1(B),k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_funct_1)).

tff(c_2,plain,(
    ! [A_1,B_2] : r1_tarski(k3_xboole_0(A_1,B_2),A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_32,plain,(
    ! [A_55] : k1_relat_1(k6_relat_1(A_55)) = A_55 ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_20,plain,(
    ! [A_34] : v1_relat_1(k6_relat_1(A_34)) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_46,plain,(
    ! [A_63,B_64] :
      ( k5_relat_1(k6_relat_1(A_63),B_64) = k7_relat_1(B_64,A_63)
      | ~ v1_relat_1(B_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_225,plain,(
    ! [B_88,A_89] :
      ( k5_relat_1(B_88,k6_relat_1(A_89)) = k8_relat_1(A_89,B_88)
      | ~ v1_relat_1(B_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_257,plain,(
    ! [A_89,A_63] :
      ( k8_relat_1(A_89,k6_relat_1(A_63)) = k7_relat_1(k6_relat_1(A_89),A_63)
      | ~ v1_relat_1(k6_relat_1(A_63))
      | ~ v1_relat_1(k6_relat_1(A_89)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_225])).

tff(c_281,plain,(
    ! [A_89,A_63] : k8_relat_1(A_89,k6_relat_1(A_63)) = k7_relat_1(k6_relat_1(A_89),A_63) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_20,c_257])).

tff(c_403,plain,(
    ! [A_107,B_108] :
      ( k5_relat_1(k6_relat_1(A_107),B_108) = B_108
      | ~ r1_tarski(k1_relat_1(B_108),A_107)
      | ~ v1_relat_1(B_108) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_413,plain,(
    ! [A_107,A_55] :
      ( k5_relat_1(k6_relat_1(A_107),k6_relat_1(A_55)) = k6_relat_1(A_55)
      | ~ r1_tarski(A_55,A_107)
      | ~ v1_relat_1(k6_relat_1(A_55)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_403])).

tff(c_593,plain,(
    ! [A_116,A_117] :
      ( k5_relat_1(k6_relat_1(A_116),k6_relat_1(A_117)) = k6_relat_1(A_117)
      | ~ r1_tarski(A_117,A_116) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_413])).

tff(c_24,plain,(
    ! [B_40,A_39] :
      ( k5_relat_1(B_40,k6_relat_1(A_39)) = k8_relat_1(A_39,B_40)
      | ~ v1_relat_1(B_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_599,plain,(
    ! [A_117,A_116] :
      ( k8_relat_1(A_117,k6_relat_1(A_116)) = k6_relat_1(A_117)
      | ~ v1_relat_1(k6_relat_1(A_116))
      | ~ r1_tarski(A_117,A_116) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_593,c_24])).

tff(c_680,plain,(
    ! [A_123,A_124] :
      ( k7_relat_1(k6_relat_1(A_123),A_124) = k6_relat_1(A_123)
      | ~ r1_tarski(A_123,A_124) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_281,c_599])).

tff(c_303,plain,(
    ! [B_93,A_94] :
      ( k3_xboole_0(k1_relat_1(B_93),A_94) = k1_relat_1(k7_relat_1(B_93,A_94))
      | ~ v1_relat_1(B_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_315,plain,(
    ! [A_55,A_94] :
      ( k1_relat_1(k7_relat_1(k6_relat_1(A_55),A_94)) = k3_xboole_0(A_55,A_94)
      | ~ v1_relat_1(k6_relat_1(A_55)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_303])).

tff(c_319,plain,(
    ! [A_55,A_94] : k1_relat_1(k7_relat_1(k6_relat_1(A_55),A_94)) = k3_xboole_0(A_55,A_94) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_315])).

tff(c_697,plain,(
    ! [A_123,A_124] :
      ( k3_xboole_0(A_123,A_124) = k1_relat_1(k6_relat_1(A_123))
      | ~ r1_tarski(A_123,A_124) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_680,c_319])).

tff(c_742,plain,(
    ! [A_125,A_126] :
      ( k3_xboole_0(A_125,A_126) = A_125
      | ~ r1_tarski(A_125,A_126) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_697])).

tff(c_755,plain,(
    ! [A_1,B_2] : k3_xboole_0(k3_xboole_0(A_1,B_2),A_1) = k3_xboole_0(A_1,B_2) ),
    inference(resolution,[status(thm)],[c_2,c_742])).

tff(c_322,plain,(
    ! [A_95,A_96] : k8_relat_1(A_95,k6_relat_1(A_96)) = k7_relat_1(k6_relat_1(A_95),A_96) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_20,c_257])).

tff(c_18,plain,(
    ! [A_32,B_33] :
      ( v1_relat_1(k5_relat_1(A_32,B_33))
      | ~ v1_relat_1(B_33)
      | ~ v1_relat_1(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_235,plain,(
    ! [A_89,B_88] :
      ( v1_relat_1(k8_relat_1(A_89,B_88))
      | ~ v1_relat_1(k6_relat_1(A_89))
      | ~ v1_relat_1(B_88)
      | ~ v1_relat_1(B_88) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_225,c_18])).

tff(c_272,plain,(
    ! [A_89,B_88] :
      ( v1_relat_1(k8_relat_1(A_89,B_88))
      | ~ v1_relat_1(B_88) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_235])).

tff(c_332,plain,(
    ! [A_95,A_96] :
      ( v1_relat_1(k7_relat_1(k6_relat_1(A_95),A_96))
      | ~ v1_relat_1(k6_relat_1(A_96)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_322,c_272])).

tff(c_342,plain,(
    ! [A_95,A_96] : v1_relat_1(k7_relat_1(k6_relat_1(A_95),A_96)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_332])).

tff(c_34,plain,(
    ! [A_55] : k2_relat_1(k6_relat_1(A_55)) = A_55 ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_96,plain,(
    ! [A_75] :
      ( k5_relat_1(A_75,k6_relat_1(k2_relat_1(A_75))) = A_75
      | ~ v1_relat_1(A_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_105,plain,(
    ! [A_55] :
      ( k5_relat_1(k6_relat_1(A_55),k6_relat_1(A_55)) = k6_relat_1(A_55)
      | ~ v1_relat_1(k6_relat_1(A_55)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_96])).

tff(c_109,plain,(
    ! [A_55] : k5_relat_1(k6_relat_1(A_55),k6_relat_1(A_55)) = k6_relat_1(A_55) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_105])).

tff(c_785,plain,(
    ! [A_129,B_130,C_131] :
      ( k8_relat_1(A_129,k5_relat_1(B_130,C_131)) = k5_relat_1(B_130,k8_relat_1(A_129,C_131))
      | ~ v1_relat_1(C_131)
      | ~ v1_relat_1(B_130) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_820,plain,(
    ! [A_55,A_129] :
      ( k5_relat_1(k6_relat_1(A_55),k8_relat_1(A_129,k6_relat_1(A_55))) = k8_relat_1(A_129,k6_relat_1(A_55))
      | ~ v1_relat_1(k6_relat_1(A_55))
      | ~ v1_relat_1(k6_relat_1(A_55)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_109,c_785])).

tff(c_1053,plain,(
    ! [A_145,A_146] : k5_relat_1(k6_relat_1(A_145),k7_relat_1(k6_relat_1(A_146),A_145)) = k7_relat_1(k6_relat_1(A_146),A_145) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_20,c_281,c_281,c_820])).

tff(c_1065,plain,(
    ! [A_146,A_145] :
      ( k7_relat_1(k7_relat_1(k6_relat_1(A_146),A_145),A_145) = k7_relat_1(k6_relat_1(A_146),A_145)
      | ~ v1_relat_1(k7_relat_1(k6_relat_1(A_146),A_145)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1053,c_46])).

tff(c_1092,plain,(
    ! [A_146,A_145] : k7_relat_1(k7_relat_1(k6_relat_1(A_146),A_145),A_145) = k7_relat_1(k6_relat_1(A_146),A_145) ),
    inference(demodulation,[status(thm),theory(equality)],[c_342,c_1065])).

tff(c_358,plain,(
    ! [A_103,A_104] : k1_relat_1(k7_relat_1(k6_relat_1(A_103),A_104)) = k3_xboole_0(A_103,A_104) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_315])).

tff(c_44,plain,(
    ! [B_62,A_61] :
      ( k3_xboole_0(k1_relat_1(B_62),A_61) = k1_relat_1(k7_relat_1(B_62,A_61))
      | ~ v1_relat_1(B_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_364,plain,(
    ! [A_103,A_104,A_61] :
      ( k1_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(A_103),A_104),A_61)) = k3_xboole_0(k3_xboole_0(A_103,A_104),A_61)
      | ~ v1_relat_1(k7_relat_1(k6_relat_1(A_103),A_104)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_358,c_44])).

tff(c_3295,plain,(
    ! [A_233,A_234,A_235] : k1_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(A_233),A_234),A_235)) = k3_xboole_0(k3_xboole_0(A_233,A_234),A_235) ),
    inference(demodulation,[status(thm),theory(equality)],[c_342,c_364])).

tff(c_3344,plain,(
    ! [A_146,A_145] : k3_xboole_0(k3_xboole_0(A_146,A_145),A_145) = k1_relat_1(k7_relat_1(k6_relat_1(A_146),A_145)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1092,c_3295])).

tff(c_3373,plain,(
    ! [A_146,A_145] : k3_xboole_0(k3_xboole_0(A_146,A_145),A_145) = k3_xboole_0(A_146,A_145) ),
    inference(demodulation,[status(thm),theory(equality)],[c_319,c_3344])).

tff(c_36,plain,(
    ! [A_56] : k4_relat_1(k6_relat_1(A_56)) = k6_relat_1(A_56) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_482,plain,(
    ! [B_111,A_112] :
      ( k5_relat_1(k4_relat_1(B_111),k4_relat_1(A_112)) = k4_relat_1(k5_relat_1(A_112,B_111))
      | ~ v1_relat_1(B_111)
      | ~ v1_relat_1(A_112) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_497,plain,(
    ! [B_111,A_56] :
      ( k5_relat_1(k4_relat_1(B_111),k6_relat_1(A_56)) = k4_relat_1(k5_relat_1(k6_relat_1(A_56),B_111))
      | ~ v1_relat_1(B_111)
      | ~ v1_relat_1(k6_relat_1(A_56)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_482])).

tff(c_1386,plain,(
    ! [B_164,A_165] :
      ( k5_relat_1(k4_relat_1(B_164),k6_relat_1(A_165)) = k4_relat_1(k5_relat_1(k6_relat_1(A_165),B_164))
      | ~ v1_relat_1(B_164) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_497])).

tff(c_1422,plain,(
    ! [A_165,A_56] :
      ( k4_relat_1(k5_relat_1(k6_relat_1(A_165),k6_relat_1(A_56))) = k5_relat_1(k6_relat_1(A_56),k6_relat_1(A_165))
      | ~ v1_relat_1(k6_relat_1(A_56)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_1386])).

tff(c_1485,plain,(
    ! [A_170,A_171] : k4_relat_1(k5_relat_1(k6_relat_1(A_170),k6_relat_1(A_171))) = k5_relat_1(k6_relat_1(A_171),k6_relat_1(A_170)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_1422])).

tff(c_1510,plain,(
    ! [A_39,A_170] :
      ( k5_relat_1(k6_relat_1(A_39),k6_relat_1(A_170)) = k4_relat_1(k8_relat_1(A_39,k6_relat_1(A_170)))
      | ~ v1_relat_1(k6_relat_1(A_170)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_1485])).

tff(c_1927,plain,(
    ! [A_191,A_192] : k5_relat_1(k6_relat_1(A_191),k6_relat_1(A_192)) = k4_relat_1(k7_relat_1(k6_relat_1(A_191),A_192)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_281,c_1510])).

tff(c_1974,plain,(
    ! [A_63,A_192] :
      ( k4_relat_1(k7_relat_1(k6_relat_1(A_63),A_192)) = k7_relat_1(k6_relat_1(A_192),A_63)
      | ~ v1_relat_1(k6_relat_1(A_192)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_1927])).

tff(c_2010,plain,(
    ! [A_63,A_192] : k4_relat_1(k7_relat_1(k6_relat_1(A_63),A_192)) = k7_relat_1(k6_relat_1(A_192),A_63) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_1974])).

tff(c_933,plain,(
    ! [B_140,C_141,A_142] :
      ( k7_relat_1(k5_relat_1(B_140,C_141),A_142) = k5_relat_1(k7_relat_1(B_140,A_142),C_141)
      | ~ v1_relat_1(C_141)
      | ~ v1_relat_1(B_140) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_969,plain,(
    ! [A_63,A_142,B_64] :
      ( k5_relat_1(k7_relat_1(k6_relat_1(A_63),A_142),B_64) = k7_relat_1(k7_relat_1(B_64,A_63),A_142)
      | ~ v1_relat_1(B_64)
      | ~ v1_relat_1(k6_relat_1(A_63))
      | ~ v1_relat_1(B_64) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_933])).

tff(c_5554,plain,(
    ! [A_298,A_299,B_300] :
      ( k5_relat_1(k7_relat_1(k6_relat_1(A_298),A_299),B_300) = k7_relat_1(k7_relat_1(B_300,A_298),A_299)
      | ~ v1_relat_1(B_300) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_969])).

tff(c_5606,plain,(
    ! [A_39,A_298,A_299] :
      ( k8_relat_1(A_39,k7_relat_1(k6_relat_1(A_298),A_299)) = k7_relat_1(k7_relat_1(k6_relat_1(A_39),A_298),A_299)
      | ~ v1_relat_1(k7_relat_1(k6_relat_1(A_298),A_299))
      | ~ v1_relat_1(k6_relat_1(A_39)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5554,c_24])).

tff(c_5693,plain,(
    ! [A_39,A_298,A_299] : k8_relat_1(A_39,k7_relat_1(k6_relat_1(A_298),A_299)) = k7_relat_1(k7_relat_1(k6_relat_1(A_39),A_298),A_299) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_342,c_5606])).

tff(c_40,plain,(
    ! [A_59] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(A_59)),A_59) = A_59
      | ~ v1_relat_1(A_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_367,plain,(
    ! [A_103,A_104] :
      ( k5_relat_1(k6_relat_1(k3_xboole_0(A_103,A_104)),k7_relat_1(k6_relat_1(A_103),A_104)) = k7_relat_1(k6_relat_1(A_103),A_104)
      | ~ v1_relat_1(k7_relat_1(k6_relat_1(A_103),A_104)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_358,c_40])).

tff(c_378,plain,(
    ! [A_103,A_104] : k5_relat_1(k6_relat_1(k3_xboole_0(A_103,A_104)),k7_relat_1(k6_relat_1(A_103),A_104)) = k7_relat_1(k6_relat_1(A_103),A_104) ),
    inference(demodulation,[status(thm),theory(equality)],[c_342,c_367])).

tff(c_33596,plain,(
    ! [A_687,B_688] :
      ( k4_relat_1(k5_relat_1(k6_relat_1(A_687),B_688)) = k8_relat_1(A_687,k4_relat_1(B_688))
      | ~ v1_relat_1(B_688)
      | ~ v1_relat_1(k4_relat_1(B_688)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_1386])).

tff(c_33669,plain,(
    ! [A_103,A_104] :
      ( k8_relat_1(k3_xboole_0(A_103,A_104),k4_relat_1(k7_relat_1(k6_relat_1(A_103),A_104))) = k4_relat_1(k7_relat_1(k6_relat_1(A_103),A_104))
      | ~ v1_relat_1(k7_relat_1(k6_relat_1(A_103),A_104))
      | ~ v1_relat_1(k4_relat_1(k7_relat_1(k6_relat_1(A_103),A_104))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_378,c_33596])).

tff(c_35576,plain,(
    ! [A_697,A_698] : k7_relat_1(k7_relat_1(k6_relat_1(k3_xboole_0(A_697,A_698)),A_698),A_697) = k7_relat_1(k6_relat_1(A_698),A_697) ),
    inference(demodulation,[status(thm),theory(equality)],[c_342,c_2010,c_342,c_5693,c_2010,c_2010,c_33669])).

tff(c_376,plain,(
    ! [A_103,A_104,A_61] : k1_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(A_103),A_104),A_61)) = k3_xboole_0(k3_xboole_0(A_103,A_104),A_61) ),
    inference(demodulation,[status(thm),theory(equality)],[c_342,c_364])).

tff(c_35686,plain,(
    ! [A_697,A_698] : k3_xboole_0(k3_xboole_0(k3_xboole_0(A_697,A_698),A_698),A_697) = k1_relat_1(k7_relat_1(k6_relat_1(A_698),A_697)) ),
    inference(superposition,[status(thm),theory(equality)],[c_35576,c_376])).

tff(c_35950,plain,(
    ! [A_700,A_699] : k3_xboole_0(A_700,A_699) = k3_xboole_0(A_699,A_700) ),
    inference(demodulation,[status(thm),theory(equality)],[c_755,c_3373,c_319,c_35686])).

tff(c_36663,plain,(
    ! [A_700,A_699] : r1_tarski(k3_xboole_0(A_700,A_699),A_699) ),
    inference(superposition,[status(thm),theory(equality)],[c_35950,c_2])).

tff(c_149,plain,(
    ! [A_80,B_81] :
      ( k5_relat_1(k6_relat_1(A_80),B_81) = k7_relat_1(B_81,A_80)
      | ~ v1_relat_1(B_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_42,plain,(
    ! [A_60] :
      ( k5_relat_1(A_60,k6_relat_1(k2_relat_1(A_60))) = A_60
      | ~ v1_relat_1(A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_170,plain,(
    ! [A_80] :
      ( k7_relat_1(k6_relat_1(k2_relat_1(k6_relat_1(A_80))),A_80) = k6_relat_1(A_80)
      | ~ v1_relat_1(k6_relat_1(A_80))
      | ~ v1_relat_1(k6_relat_1(k2_relat_1(k6_relat_1(A_80)))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_149,c_42])).

tff(c_192,plain,(
    ! [A_80] : k7_relat_1(k6_relat_1(A_80),A_80) = k6_relat_1(A_80) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_20,c_34,c_170])).

tff(c_645,plain,(
    ! [A_117,A_116] :
      ( k7_relat_1(k6_relat_1(A_117),A_116) = k6_relat_1(A_117)
      | ~ r1_tarski(A_117,A_116) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_281,c_599])).

tff(c_419,plain,(
    ! [A_109] :
      ( k7_relat_1(A_109,k1_relat_1(A_109)) = A_109
      | ~ v1_relat_1(A_109)
      | ~ v1_relat_1(A_109) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_149])).

tff(c_439,plain,(
    ! [A_55,A_94] :
      ( k7_relat_1(k7_relat_1(k6_relat_1(A_55),A_94),k3_xboole_0(A_55,A_94)) = k7_relat_1(k6_relat_1(A_55),A_94)
      | ~ v1_relat_1(k7_relat_1(k6_relat_1(A_55),A_94))
      | ~ v1_relat_1(k7_relat_1(k6_relat_1(A_55),A_94)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_319,c_419])).

tff(c_4779,plain,(
    ! [A_265,A_266] : k7_relat_1(k7_relat_1(k6_relat_1(A_265),A_266),k3_xboole_0(A_265,A_266)) = k7_relat_1(k6_relat_1(A_265),A_266) ),
    inference(demodulation,[status(thm),theory(equality)],[c_342,c_342,c_439])).

tff(c_12819,plain,(
    ! [A_421,A_422] :
      ( k7_relat_1(k6_relat_1(A_421),k3_xboole_0(A_421,A_422)) = k7_relat_1(k6_relat_1(A_421),A_422)
      | ~ r1_tarski(A_421,A_422) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_645,c_4779])).

tff(c_13010,plain,(
    ! [A_1,B_2] :
      ( k7_relat_1(k6_relat_1(k3_xboole_0(A_1,B_2)),k3_xboole_0(A_1,B_2)) = k7_relat_1(k6_relat_1(k3_xboole_0(A_1,B_2)),A_1)
      | ~ r1_tarski(k3_xboole_0(A_1,B_2),A_1) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_755,c_12819])).

tff(c_13096,plain,(
    ! [A_423,B_424] : k7_relat_1(k6_relat_1(k3_xboole_0(A_423,B_424)),A_423) = k6_relat_1(k3_xboole_0(A_423,B_424)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_192,c_13010])).

tff(c_13198,plain,(
    ! [A_423,B_424] : k7_relat_1(k6_relat_1(A_423),k3_xboole_0(A_423,B_424)) = k4_relat_1(k6_relat_1(k3_xboole_0(A_423,B_424))) ),
    inference(superposition,[status(thm),theory(equality)],[c_13096,c_2010])).

tff(c_13337,plain,(
    ! [A_423,B_424] : k7_relat_1(k6_relat_1(A_423),k3_xboole_0(A_423,B_424)) = k6_relat_1(k3_xboole_0(A_423,B_424)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_13198])).

tff(c_418,plain,(
    ! [A_107,A_55] :
      ( k5_relat_1(k6_relat_1(A_107),k6_relat_1(A_55)) = k6_relat_1(A_55)
      | ~ r1_tarski(A_55,A_107) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_413])).

tff(c_956,plain,(
    ! [A_107,A_142,A_55] :
      ( k5_relat_1(k7_relat_1(k6_relat_1(A_107),A_142),k6_relat_1(A_55)) = k7_relat_1(k6_relat_1(A_55),A_142)
      | ~ v1_relat_1(k6_relat_1(A_55))
      | ~ v1_relat_1(k6_relat_1(A_107))
      | ~ r1_tarski(A_55,A_107) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_418,c_933])).

tff(c_982,plain,(
    ! [A_107,A_142,A_55] :
      ( k5_relat_1(k7_relat_1(k6_relat_1(A_107),A_142),k6_relat_1(A_55)) = k7_relat_1(k6_relat_1(A_55),A_142)
      | ~ r1_tarski(A_55,A_107) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_20,c_956])).

tff(c_494,plain,(
    ! [A_56,A_112] :
      ( k5_relat_1(k6_relat_1(A_56),k4_relat_1(A_112)) = k4_relat_1(k5_relat_1(A_112,k6_relat_1(A_56)))
      | ~ v1_relat_1(k6_relat_1(A_56))
      | ~ v1_relat_1(A_112) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_482])).

tff(c_1864,plain,(
    ! [A_189,A_190] :
      ( k5_relat_1(k6_relat_1(A_189),k4_relat_1(A_190)) = k4_relat_1(k5_relat_1(A_190,k6_relat_1(A_189)))
      | ~ v1_relat_1(A_190) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_494])).

tff(c_44027,plain,(
    ! [A_750] :
      ( k4_relat_1(k5_relat_1(A_750,k6_relat_1(k1_relat_1(k4_relat_1(A_750))))) = k4_relat_1(A_750)
      | ~ v1_relat_1(k4_relat_1(A_750))
      | ~ v1_relat_1(A_750) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1864,c_40])).

tff(c_44114,plain,(
    ! [A_107,A_142] :
      ( k4_relat_1(k7_relat_1(k6_relat_1(k1_relat_1(k4_relat_1(k7_relat_1(k6_relat_1(A_107),A_142)))),A_142)) = k4_relat_1(k7_relat_1(k6_relat_1(A_107),A_142))
      | ~ v1_relat_1(k4_relat_1(k7_relat_1(k6_relat_1(A_107),A_142)))
      | ~ v1_relat_1(k7_relat_1(k6_relat_1(A_107),A_142))
      | ~ r1_tarski(k1_relat_1(k4_relat_1(k7_relat_1(k6_relat_1(A_107),A_142))),A_107) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_982,c_44027])).

tff(c_44169,plain,(
    ! [A_142,A_107] : k7_relat_1(k6_relat_1(A_142),A_107) = k6_relat_1(k3_xboole_0(A_142,A_107)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36663,c_319,c_2010,c_342,c_342,c_2010,c_13337,c_2010,c_2010,c_319,c_2010,c_44114])).

tff(c_48,plain,(
    k5_relat_1(k6_relat_1('#skF_2'),k6_relat_1('#skF_1')) != k6_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_162,plain,
    ( k7_relat_1(k6_relat_1('#skF_1'),'#skF_2') != k6_relat_1(k3_xboole_0('#skF_1','#skF_2'))
    | ~ v1_relat_1(k6_relat_1('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_149,c_48])).

tff(c_188,plain,(
    k7_relat_1(k6_relat_1('#skF_1'),'#skF_2') != k6_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_162])).

tff(c_44258,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44169,c_188])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 19:54:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 14.29/6.83  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 14.29/6.84  
% 14.29/6.84  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 14.29/6.85  %$ r1_tarski > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k8_relat_1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k6_relat_1 > k4_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1
% 14.29/6.85  
% 14.29/6.85  %Foreground sorts:
% 14.29/6.85  
% 14.29/6.85  
% 14.29/6.85  %Background operators:
% 14.29/6.85  
% 14.29/6.85  
% 14.29/6.85  %Foreground operators:
% 14.29/6.85  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 14.29/6.85  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 14.29/6.85  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 14.29/6.85  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 14.29/6.85  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 14.29/6.85  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 14.29/6.85  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 14.29/6.85  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 14.29/6.85  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 14.29/6.85  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 14.29/6.85  tff('#skF_2', type, '#skF_2': $i).
% 14.29/6.85  tff('#skF_1', type, '#skF_1': $i).
% 14.29/6.85  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 14.29/6.85  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 14.29/6.85  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 14.29/6.85  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 14.29/6.85  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 14.29/6.85  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 14.29/6.85  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 14.29/6.85  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 14.29/6.85  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 14.29/6.85  tff(k4_relat_1, type, k4_relat_1: $i > $i).
% 14.29/6.85  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 14.29/6.85  
% 14.29/6.87  tff(f_27, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 14.29/6.87  tff(f_88, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 14.29/6.87  tff(f_49, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 14.29/6.87  tff(f_112, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_relat_1)).
% 14.29/6.87  tff(f_60, axiom, (![A, B]: (v1_relat_1(B) => (k8_relat_1(A, B) = k5_relat_1(B, k6_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t123_relat_1)).
% 14.29/6.87  tff(f_96, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k5_relat_1(k6_relat_1(A), B) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t77_relat_1)).
% 14.29/6.87  tff(f_108, axiom, (![A, B]: (v1_relat_1(B) => (k1_relat_1(k7_relat_1(B, A)) = k3_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t90_relat_1)).
% 14.29/6.87  tff(f_47, axiom, (![A, B]: ((v1_relat_1(A) & v1_relat_1(B)) => v1_relat_1(k5_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k5_relat_1)).
% 14.29/6.87  tff(f_104, axiom, (![A]: (v1_relat_1(A) => (k5_relat_1(A, k6_relat_1(k2_relat_1(A))) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t80_relat_1)).
% 14.29/6.87  tff(f_67, axiom, (![A, B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (k8_relat_1(A, k5_relat_1(B, C)) = k5_relat_1(B, k8_relat_1(A, C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t139_relat_1)).
% 14.29/6.87  tff(f_90, axiom, (![A]: (k4_relat_1(k6_relat_1(A)) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_relat_1)).
% 14.29/6.87  tff(f_74, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k4_relat_1(k5_relat_1(A, B)) = k5_relat_1(k4_relat_1(B), k4_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t54_relat_1)).
% 14.29/6.87  tff(f_56, axiom, (![A, B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (k7_relat_1(k5_relat_1(B, C), A) = k5_relat_1(k7_relat_1(B, A), C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t112_relat_1)).
% 14.29/6.87  tff(f_100, axiom, (![A]: (v1_relat_1(A) => (k5_relat_1(k6_relat_1(k1_relat_1(A)), A) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t78_relat_1)).
% 14.29/6.87  tff(f_115, negated_conjecture, ~(![A, B]: (k5_relat_1(k6_relat_1(B), k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_funct_1)).
% 14.29/6.87  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(k3_xboole_0(A_1, B_2), A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 14.29/6.87  tff(c_32, plain, (![A_55]: (k1_relat_1(k6_relat_1(A_55))=A_55)), inference(cnfTransformation, [status(thm)], [f_88])).
% 14.29/6.87  tff(c_20, plain, (![A_34]: (v1_relat_1(k6_relat_1(A_34)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 14.29/6.87  tff(c_46, plain, (![A_63, B_64]: (k5_relat_1(k6_relat_1(A_63), B_64)=k7_relat_1(B_64, A_63) | ~v1_relat_1(B_64))), inference(cnfTransformation, [status(thm)], [f_112])).
% 14.29/6.87  tff(c_225, plain, (![B_88, A_89]: (k5_relat_1(B_88, k6_relat_1(A_89))=k8_relat_1(A_89, B_88) | ~v1_relat_1(B_88))), inference(cnfTransformation, [status(thm)], [f_60])).
% 14.29/6.87  tff(c_257, plain, (![A_89, A_63]: (k8_relat_1(A_89, k6_relat_1(A_63))=k7_relat_1(k6_relat_1(A_89), A_63) | ~v1_relat_1(k6_relat_1(A_63)) | ~v1_relat_1(k6_relat_1(A_89)))), inference(superposition, [status(thm), theory('equality')], [c_46, c_225])).
% 14.29/6.87  tff(c_281, plain, (![A_89, A_63]: (k8_relat_1(A_89, k6_relat_1(A_63))=k7_relat_1(k6_relat_1(A_89), A_63))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_20, c_257])).
% 14.29/6.87  tff(c_403, plain, (![A_107, B_108]: (k5_relat_1(k6_relat_1(A_107), B_108)=B_108 | ~r1_tarski(k1_relat_1(B_108), A_107) | ~v1_relat_1(B_108))), inference(cnfTransformation, [status(thm)], [f_96])).
% 14.29/6.87  tff(c_413, plain, (![A_107, A_55]: (k5_relat_1(k6_relat_1(A_107), k6_relat_1(A_55))=k6_relat_1(A_55) | ~r1_tarski(A_55, A_107) | ~v1_relat_1(k6_relat_1(A_55)))), inference(superposition, [status(thm), theory('equality')], [c_32, c_403])).
% 14.29/6.87  tff(c_593, plain, (![A_116, A_117]: (k5_relat_1(k6_relat_1(A_116), k6_relat_1(A_117))=k6_relat_1(A_117) | ~r1_tarski(A_117, A_116))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_413])).
% 14.29/6.87  tff(c_24, plain, (![B_40, A_39]: (k5_relat_1(B_40, k6_relat_1(A_39))=k8_relat_1(A_39, B_40) | ~v1_relat_1(B_40))), inference(cnfTransformation, [status(thm)], [f_60])).
% 14.29/6.87  tff(c_599, plain, (![A_117, A_116]: (k8_relat_1(A_117, k6_relat_1(A_116))=k6_relat_1(A_117) | ~v1_relat_1(k6_relat_1(A_116)) | ~r1_tarski(A_117, A_116))), inference(superposition, [status(thm), theory('equality')], [c_593, c_24])).
% 14.29/6.87  tff(c_680, plain, (![A_123, A_124]: (k7_relat_1(k6_relat_1(A_123), A_124)=k6_relat_1(A_123) | ~r1_tarski(A_123, A_124))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_281, c_599])).
% 14.29/6.87  tff(c_303, plain, (![B_93, A_94]: (k3_xboole_0(k1_relat_1(B_93), A_94)=k1_relat_1(k7_relat_1(B_93, A_94)) | ~v1_relat_1(B_93))), inference(cnfTransformation, [status(thm)], [f_108])).
% 14.29/6.87  tff(c_315, plain, (![A_55, A_94]: (k1_relat_1(k7_relat_1(k6_relat_1(A_55), A_94))=k3_xboole_0(A_55, A_94) | ~v1_relat_1(k6_relat_1(A_55)))), inference(superposition, [status(thm), theory('equality')], [c_32, c_303])).
% 14.29/6.87  tff(c_319, plain, (![A_55, A_94]: (k1_relat_1(k7_relat_1(k6_relat_1(A_55), A_94))=k3_xboole_0(A_55, A_94))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_315])).
% 14.29/6.87  tff(c_697, plain, (![A_123, A_124]: (k3_xboole_0(A_123, A_124)=k1_relat_1(k6_relat_1(A_123)) | ~r1_tarski(A_123, A_124))), inference(superposition, [status(thm), theory('equality')], [c_680, c_319])).
% 14.29/6.87  tff(c_742, plain, (![A_125, A_126]: (k3_xboole_0(A_125, A_126)=A_125 | ~r1_tarski(A_125, A_126))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_697])).
% 14.29/6.87  tff(c_755, plain, (![A_1, B_2]: (k3_xboole_0(k3_xboole_0(A_1, B_2), A_1)=k3_xboole_0(A_1, B_2))), inference(resolution, [status(thm)], [c_2, c_742])).
% 14.29/6.87  tff(c_322, plain, (![A_95, A_96]: (k8_relat_1(A_95, k6_relat_1(A_96))=k7_relat_1(k6_relat_1(A_95), A_96))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_20, c_257])).
% 14.29/6.87  tff(c_18, plain, (![A_32, B_33]: (v1_relat_1(k5_relat_1(A_32, B_33)) | ~v1_relat_1(B_33) | ~v1_relat_1(A_32))), inference(cnfTransformation, [status(thm)], [f_47])).
% 14.29/6.87  tff(c_235, plain, (![A_89, B_88]: (v1_relat_1(k8_relat_1(A_89, B_88)) | ~v1_relat_1(k6_relat_1(A_89)) | ~v1_relat_1(B_88) | ~v1_relat_1(B_88))), inference(superposition, [status(thm), theory('equality')], [c_225, c_18])).
% 14.29/6.87  tff(c_272, plain, (![A_89, B_88]: (v1_relat_1(k8_relat_1(A_89, B_88)) | ~v1_relat_1(B_88))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_235])).
% 14.29/6.87  tff(c_332, plain, (![A_95, A_96]: (v1_relat_1(k7_relat_1(k6_relat_1(A_95), A_96)) | ~v1_relat_1(k6_relat_1(A_96)))), inference(superposition, [status(thm), theory('equality')], [c_322, c_272])).
% 14.29/6.87  tff(c_342, plain, (![A_95, A_96]: (v1_relat_1(k7_relat_1(k6_relat_1(A_95), A_96)))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_332])).
% 14.29/6.87  tff(c_34, plain, (![A_55]: (k2_relat_1(k6_relat_1(A_55))=A_55)), inference(cnfTransformation, [status(thm)], [f_88])).
% 14.29/6.87  tff(c_96, plain, (![A_75]: (k5_relat_1(A_75, k6_relat_1(k2_relat_1(A_75)))=A_75 | ~v1_relat_1(A_75))), inference(cnfTransformation, [status(thm)], [f_104])).
% 14.29/6.87  tff(c_105, plain, (![A_55]: (k5_relat_1(k6_relat_1(A_55), k6_relat_1(A_55))=k6_relat_1(A_55) | ~v1_relat_1(k6_relat_1(A_55)))), inference(superposition, [status(thm), theory('equality')], [c_34, c_96])).
% 14.29/6.87  tff(c_109, plain, (![A_55]: (k5_relat_1(k6_relat_1(A_55), k6_relat_1(A_55))=k6_relat_1(A_55))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_105])).
% 14.29/6.87  tff(c_785, plain, (![A_129, B_130, C_131]: (k8_relat_1(A_129, k5_relat_1(B_130, C_131))=k5_relat_1(B_130, k8_relat_1(A_129, C_131)) | ~v1_relat_1(C_131) | ~v1_relat_1(B_130))), inference(cnfTransformation, [status(thm)], [f_67])).
% 14.29/6.87  tff(c_820, plain, (![A_55, A_129]: (k5_relat_1(k6_relat_1(A_55), k8_relat_1(A_129, k6_relat_1(A_55)))=k8_relat_1(A_129, k6_relat_1(A_55)) | ~v1_relat_1(k6_relat_1(A_55)) | ~v1_relat_1(k6_relat_1(A_55)))), inference(superposition, [status(thm), theory('equality')], [c_109, c_785])).
% 14.29/6.87  tff(c_1053, plain, (![A_145, A_146]: (k5_relat_1(k6_relat_1(A_145), k7_relat_1(k6_relat_1(A_146), A_145))=k7_relat_1(k6_relat_1(A_146), A_145))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_20, c_281, c_281, c_820])).
% 14.29/6.87  tff(c_1065, plain, (![A_146, A_145]: (k7_relat_1(k7_relat_1(k6_relat_1(A_146), A_145), A_145)=k7_relat_1(k6_relat_1(A_146), A_145) | ~v1_relat_1(k7_relat_1(k6_relat_1(A_146), A_145)))), inference(superposition, [status(thm), theory('equality')], [c_1053, c_46])).
% 14.29/6.87  tff(c_1092, plain, (![A_146, A_145]: (k7_relat_1(k7_relat_1(k6_relat_1(A_146), A_145), A_145)=k7_relat_1(k6_relat_1(A_146), A_145))), inference(demodulation, [status(thm), theory('equality')], [c_342, c_1065])).
% 14.29/6.87  tff(c_358, plain, (![A_103, A_104]: (k1_relat_1(k7_relat_1(k6_relat_1(A_103), A_104))=k3_xboole_0(A_103, A_104))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_315])).
% 14.29/6.87  tff(c_44, plain, (![B_62, A_61]: (k3_xboole_0(k1_relat_1(B_62), A_61)=k1_relat_1(k7_relat_1(B_62, A_61)) | ~v1_relat_1(B_62))), inference(cnfTransformation, [status(thm)], [f_108])).
% 14.29/6.87  tff(c_364, plain, (![A_103, A_104, A_61]: (k1_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(A_103), A_104), A_61))=k3_xboole_0(k3_xboole_0(A_103, A_104), A_61) | ~v1_relat_1(k7_relat_1(k6_relat_1(A_103), A_104)))), inference(superposition, [status(thm), theory('equality')], [c_358, c_44])).
% 14.29/6.87  tff(c_3295, plain, (![A_233, A_234, A_235]: (k1_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(A_233), A_234), A_235))=k3_xboole_0(k3_xboole_0(A_233, A_234), A_235))), inference(demodulation, [status(thm), theory('equality')], [c_342, c_364])).
% 14.29/6.87  tff(c_3344, plain, (![A_146, A_145]: (k3_xboole_0(k3_xboole_0(A_146, A_145), A_145)=k1_relat_1(k7_relat_1(k6_relat_1(A_146), A_145)))), inference(superposition, [status(thm), theory('equality')], [c_1092, c_3295])).
% 14.29/6.87  tff(c_3373, plain, (![A_146, A_145]: (k3_xboole_0(k3_xboole_0(A_146, A_145), A_145)=k3_xboole_0(A_146, A_145))), inference(demodulation, [status(thm), theory('equality')], [c_319, c_3344])).
% 14.29/6.87  tff(c_36, plain, (![A_56]: (k4_relat_1(k6_relat_1(A_56))=k6_relat_1(A_56))), inference(cnfTransformation, [status(thm)], [f_90])).
% 14.29/6.87  tff(c_482, plain, (![B_111, A_112]: (k5_relat_1(k4_relat_1(B_111), k4_relat_1(A_112))=k4_relat_1(k5_relat_1(A_112, B_111)) | ~v1_relat_1(B_111) | ~v1_relat_1(A_112))), inference(cnfTransformation, [status(thm)], [f_74])).
% 14.29/6.87  tff(c_497, plain, (![B_111, A_56]: (k5_relat_1(k4_relat_1(B_111), k6_relat_1(A_56))=k4_relat_1(k5_relat_1(k6_relat_1(A_56), B_111)) | ~v1_relat_1(B_111) | ~v1_relat_1(k6_relat_1(A_56)))), inference(superposition, [status(thm), theory('equality')], [c_36, c_482])).
% 14.29/6.87  tff(c_1386, plain, (![B_164, A_165]: (k5_relat_1(k4_relat_1(B_164), k6_relat_1(A_165))=k4_relat_1(k5_relat_1(k6_relat_1(A_165), B_164)) | ~v1_relat_1(B_164))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_497])).
% 14.29/6.87  tff(c_1422, plain, (![A_165, A_56]: (k4_relat_1(k5_relat_1(k6_relat_1(A_165), k6_relat_1(A_56)))=k5_relat_1(k6_relat_1(A_56), k6_relat_1(A_165)) | ~v1_relat_1(k6_relat_1(A_56)))), inference(superposition, [status(thm), theory('equality')], [c_36, c_1386])).
% 14.29/6.87  tff(c_1485, plain, (![A_170, A_171]: (k4_relat_1(k5_relat_1(k6_relat_1(A_170), k6_relat_1(A_171)))=k5_relat_1(k6_relat_1(A_171), k6_relat_1(A_170)))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_1422])).
% 14.29/6.87  tff(c_1510, plain, (![A_39, A_170]: (k5_relat_1(k6_relat_1(A_39), k6_relat_1(A_170))=k4_relat_1(k8_relat_1(A_39, k6_relat_1(A_170))) | ~v1_relat_1(k6_relat_1(A_170)))), inference(superposition, [status(thm), theory('equality')], [c_24, c_1485])).
% 14.29/6.87  tff(c_1927, plain, (![A_191, A_192]: (k5_relat_1(k6_relat_1(A_191), k6_relat_1(A_192))=k4_relat_1(k7_relat_1(k6_relat_1(A_191), A_192)))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_281, c_1510])).
% 14.29/6.87  tff(c_1974, plain, (![A_63, A_192]: (k4_relat_1(k7_relat_1(k6_relat_1(A_63), A_192))=k7_relat_1(k6_relat_1(A_192), A_63) | ~v1_relat_1(k6_relat_1(A_192)))), inference(superposition, [status(thm), theory('equality')], [c_46, c_1927])).
% 14.29/6.87  tff(c_2010, plain, (![A_63, A_192]: (k4_relat_1(k7_relat_1(k6_relat_1(A_63), A_192))=k7_relat_1(k6_relat_1(A_192), A_63))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_1974])).
% 14.29/6.87  tff(c_933, plain, (![B_140, C_141, A_142]: (k7_relat_1(k5_relat_1(B_140, C_141), A_142)=k5_relat_1(k7_relat_1(B_140, A_142), C_141) | ~v1_relat_1(C_141) | ~v1_relat_1(B_140))), inference(cnfTransformation, [status(thm)], [f_56])).
% 14.29/6.87  tff(c_969, plain, (![A_63, A_142, B_64]: (k5_relat_1(k7_relat_1(k6_relat_1(A_63), A_142), B_64)=k7_relat_1(k7_relat_1(B_64, A_63), A_142) | ~v1_relat_1(B_64) | ~v1_relat_1(k6_relat_1(A_63)) | ~v1_relat_1(B_64))), inference(superposition, [status(thm), theory('equality')], [c_46, c_933])).
% 14.29/6.87  tff(c_5554, plain, (![A_298, A_299, B_300]: (k5_relat_1(k7_relat_1(k6_relat_1(A_298), A_299), B_300)=k7_relat_1(k7_relat_1(B_300, A_298), A_299) | ~v1_relat_1(B_300))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_969])).
% 14.29/6.87  tff(c_5606, plain, (![A_39, A_298, A_299]: (k8_relat_1(A_39, k7_relat_1(k6_relat_1(A_298), A_299))=k7_relat_1(k7_relat_1(k6_relat_1(A_39), A_298), A_299) | ~v1_relat_1(k7_relat_1(k6_relat_1(A_298), A_299)) | ~v1_relat_1(k6_relat_1(A_39)))), inference(superposition, [status(thm), theory('equality')], [c_5554, c_24])).
% 14.29/6.87  tff(c_5693, plain, (![A_39, A_298, A_299]: (k8_relat_1(A_39, k7_relat_1(k6_relat_1(A_298), A_299))=k7_relat_1(k7_relat_1(k6_relat_1(A_39), A_298), A_299))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_342, c_5606])).
% 14.29/6.87  tff(c_40, plain, (![A_59]: (k5_relat_1(k6_relat_1(k1_relat_1(A_59)), A_59)=A_59 | ~v1_relat_1(A_59))), inference(cnfTransformation, [status(thm)], [f_100])).
% 14.29/6.87  tff(c_367, plain, (![A_103, A_104]: (k5_relat_1(k6_relat_1(k3_xboole_0(A_103, A_104)), k7_relat_1(k6_relat_1(A_103), A_104))=k7_relat_1(k6_relat_1(A_103), A_104) | ~v1_relat_1(k7_relat_1(k6_relat_1(A_103), A_104)))), inference(superposition, [status(thm), theory('equality')], [c_358, c_40])).
% 14.29/6.87  tff(c_378, plain, (![A_103, A_104]: (k5_relat_1(k6_relat_1(k3_xboole_0(A_103, A_104)), k7_relat_1(k6_relat_1(A_103), A_104))=k7_relat_1(k6_relat_1(A_103), A_104))), inference(demodulation, [status(thm), theory('equality')], [c_342, c_367])).
% 14.29/6.87  tff(c_33596, plain, (![A_687, B_688]: (k4_relat_1(k5_relat_1(k6_relat_1(A_687), B_688))=k8_relat_1(A_687, k4_relat_1(B_688)) | ~v1_relat_1(B_688) | ~v1_relat_1(k4_relat_1(B_688)))), inference(superposition, [status(thm), theory('equality')], [c_24, c_1386])).
% 14.29/6.87  tff(c_33669, plain, (![A_103, A_104]: (k8_relat_1(k3_xboole_0(A_103, A_104), k4_relat_1(k7_relat_1(k6_relat_1(A_103), A_104)))=k4_relat_1(k7_relat_1(k6_relat_1(A_103), A_104)) | ~v1_relat_1(k7_relat_1(k6_relat_1(A_103), A_104)) | ~v1_relat_1(k4_relat_1(k7_relat_1(k6_relat_1(A_103), A_104))))), inference(superposition, [status(thm), theory('equality')], [c_378, c_33596])).
% 14.29/6.87  tff(c_35576, plain, (![A_697, A_698]: (k7_relat_1(k7_relat_1(k6_relat_1(k3_xboole_0(A_697, A_698)), A_698), A_697)=k7_relat_1(k6_relat_1(A_698), A_697))), inference(demodulation, [status(thm), theory('equality')], [c_342, c_2010, c_342, c_5693, c_2010, c_2010, c_33669])).
% 14.29/6.87  tff(c_376, plain, (![A_103, A_104, A_61]: (k1_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(A_103), A_104), A_61))=k3_xboole_0(k3_xboole_0(A_103, A_104), A_61))), inference(demodulation, [status(thm), theory('equality')], [c_342, c_364])).
% 14.29/6.87  tff(c_35686, plain, (![A_697, A_698]: (k3_xboole_0(k3_xboole_0(k3_xboole_0(A_697, A_698), A_698), A_697)=k1_relat_1(k7_relat_1(k6_relat_1(A_698), A_697)))), inference(superposition, [status(thm), theory('equality')], [c_35576, c_376])).
% 14.29/6.87  tff(c_35950, plain, (![A_700, A_699]: (k3_xboole_0(A_700, A_699)=k3_xboole_0(A_699, A_700))), inference(demodulation, [status(thm), theory('equality')], [c_755, c_3373, c_319, c_35686])).
% 14.29/6.87  tff(c_36663, plain, (![A_700, A_699]: (r1_tarski(k3_xboole_0(A_700, A_699), A_699))), inference(superposition, [status(thm), theory('equality')], [c_35950, c_2])).
% 14.29/6.87  tff(c_149, plain, (![A_80, B_81]: (k5_relat_1(k6_relat_1(A_80), B_81)=k7_relat_1(B_81, A_80) | ~v1_relat_1(B_81))), inference(cnfTransformation, [status(thm)], [f_112])).
% 14.29/6.87  tff(c_42, plain, (![A_60]: (k5_relat_1(A_60, k6_relat_1(k2_relat_1(A_60)))=A_60 | ~v1_relat_1(A_60))), inference(cnfTransformation, [status(thm)], [f_104])).
% 14.29/6.87  tff(c_170, plain, (![A_80]: (k7_relat_1(k6_relat_1(k2_relat_1(k6_relat_1(A_80))), A_80)=k6_relat_1(A_80) | ~v1_relat_1(k6_relat_1(A_80)) | ~v1_relat_1(k6_relat_1(k2_relat_1(k6_relat_1(A_80)))))), inference(superposition, [status(thm), theory('equality')], [c_149, c_42])).
% 14.29/6.87  tff(c_192, plain, (![A_80]: (k7_relat_1(k6_relat_1(A_80), A_80)=k6_relat_1(A_80))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_20, c_34, c_170])).
% 14.29/6.87  tff(c_645, plain, (![A_117, A_116]: (k7_relat_1(k6_relat_1(A_117), A_116)=k6_relat_1(A_117) | ~r1_tarski(A_117, A_116))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_281, c_599])).
% 14.29/6.87  tff(c_419, plain, (![A_109]: (k7_relat_1(A_109, k1_relat_1(A_109))=A_109 | ~v1_relat_1(A_109) | ~v1_relat_1(A_109))), inference(superposition, [status(thm), theory('equality')], [c_40, c_149])).
% 14.29/6.87  tff(c_439, plain, (![A_55, A_94]: (k7_relat_1(k7_relat_1(k6_relat_1(A_55), A_94), k3_xboole_0(A_55, A_94))=k7_relat_1(k6_relat_1(A_55), A_94) | ~v1_relat_1(k7_relat_1(k6_relat_1(A_55), A_94)) | ~v1_relat_1(k7_relat_1(k6_relat_1(A_55), A_94)))), inference(superposition, [status(thm), theory('equality')], [c_319, c_419])).
% 14.29/6.87  tff(c_4779, plain, (![A_265, A_266]: (k7_relat_1(k7_relat_1(k6_relat_1(A_265), A_266), k3_xboole_0(A_265, A_266))=k7_relat_1(k6_relat_1(A_265), A_266))), inference(demodulation, [status(thm), theory('equality')], [c_342, c_342, c_439])).
% 14.29/6.87  tff(c_12819, plain, (![A_421, A_422]: (k7_relat_1(k6_relat_1(A_421), k3_xboole_0(A_421, A_422))=k7_relat_1(k6_relat_1(A_421), A_422) | ~r1_tarski(A_421, A_422))), inference(superposition, [status(thm), theory('equality')], [c_645, c_4779])).
% 14.29/6.87  tff(c_13010, plain, (![A_1, B_2]: (k7_relat_1(k6_relat_1(k3_xboole_0(A_1, B_2)), k3_xboole_0(A_1, B_2))=k7_relat_1(k6_relat_1(k3_xboole_0(A_1, B_2)), A_1) | ~r1_tarski(k3_xboole_0(A_1, B_2), A_1))), inference(superposition, [status(thm), theory('equality')], [c_755, c_12819])).
% 14.29/6.87  tff(c_13096, plain, (![A_423, B_424]: (k7_relat_1(k6_relat_1(k3_xboole_0(A_423, B_424)), A_423)=k6_relat_1(k3_xboole_0(A_423, B_424)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_192, c_13010])).
% 14.29/6.87  tff(c_13198, plain, (![A_423, B_424]: (k7_relat_1(k6_relat_1(A_423), k3_xboole_0(A_423, B_424))=k4_relat_1(k6_relat_1(k3_xboole_0(A_423, B_424))))), inference(superposition, [status(thm), theory('equality')], [c_13096, c_2010])).
% 14.29/6.87  tff(c_13337, plain, (![A_423, B_424]: (k7_relat_1(k6_relat_1(A_423), k3_xboole_0(A_423, B_424))=k6_relat_1(k3_xboole_0(A_423, B_424)))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_13198])).
% 14.29/6.87  tff(c_418, plain, (![A_107, A_55]: (k5_relat_1(k6_relat_1(A_107), k6_relat_1(A_55))=k6_relat_1(A_55) | ~r1_tarski(A_55, A_107))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_413])).
% 14.29/6.87  tff(c_956, plain, (![A_107, A_142, A_55]: (k5_relat_1(k7_relat_1(k6_relat_1(A_107), A_142), k6_relat_1(A_55))=k7_relat_1(k6_relat_1(A_55), A_142) | ~v1_relat_1(k6_relat_1(A_55)) | ~v1_relat_1(k6_relat_1(A_107)) | ~r1_tarski(A_55, A_107))), inference(superposition, [status(thm), theory('equality')], [c_418, c_933])).
% 14.29/6.87  tff(c_982, plain, (![A_107, A_142, A_55]: (k5_relat_1(k7_relat_1(k6_relat_1(A_107), A_142), k6_relat_1(A_55))=k7_relat_1(k6_relat_1(A_55), A_142) | ~r1_tarski(A_55, A_107))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_20, c_956])).
% 14.29/6.87  tff(c_494, plain, (![A_56, A_112]: (k5_relat_1(k6_relat_1(A_56), k4_relat_1(A_112))=k4_relat_1(k5_relat_1(A_112, k6_relat_1(A_56))) | ~v1_relat_1(k6_relat_1(A_56)) | ~v1_relat_1(A_112))), inference(superposition, [status(thm), theory('equality')], [c_36, c_482])).
% 14.29/6.87  tff(c_1864, plain, (![A_189, A_190]: (k5_relat_1(k6_relat_1(A_189), k4_relat_1(A_190))=k4_relat_1(k5_relat_1(A_190, k6_relat_1(A_189))) | ~v1_relat_1(A_190))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_494])).
% 14.29/6.87  tff(c_44027, plain, (![A_750]: (k4_relat_1(k5_relat_1(A_750, k6_relat_1(k1_relat_1(k4_relat_1(A_750)))))=k4_relat_1(A_750) | ~v1_relat_1(k4_relat_1(A_750)) | ~v1_relat_1(A_750))), inference(superposition, [status(thm), theory('equality')], [c_1864, c_40])).
% 14.29/6.87  tff(c_44114, plain, (![A_107, A_142]: (k4_relat_1(k7_relat_1(k6_relat_1(k1_relat_1(k4_relat_1(k7_relat_1(k6_relat_1(A_107), A_142)))), A_142))=k4_relat_1(k7_relat_1(k6_relat_1(A_107), A_142)) | ~v1_relat_1(k4_relat_1(k7_relat_1(k6_relat_1(A_107), A_142))) | ~v1_relat_1(k7_relat_1(k6_relat_1(A_107), A_142)) | ~r1_tarski(k1_relat_1(k4_relat_1(k7_relat_1(k6_relat_1(A_107), A_142))), A_107))), inference(superposition, [status(thm), theory('equality')], [c_982, c_44027])).
% 14.29/6.87  tff(c_44169, plain, (![A_142, A_107]: (k7_relat_1(k6_relat_1(A_142), A_107)=k6_relat_1(k3_xboole_0(A_142, A_107)))), inference(demodulation, [status(thm), theory('equality')], [c_36663, c_319, c_2010, c_342, c_342, c_2010, c_13337, c_2010, c_2010, c_319, c_2010, c_44114])).
% 14.29/6.87  tff(c_48, plain, (k5_relat_1(k6_relat_1('#skF_2'), k6_relat_1('#skF_1'))!=k6_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_115])).
% 14.29/6.87  tff(c_162, plain, (k7_relat_1(k6_relat_1('#skF_1'), '#skF_2')!=k6_relat_1(k3_xboole_0('#skF_1', '#skF_2')) | ~v1_relat_1(k6_relat_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_149, c_48])).
% 14.29/6.87  tff(c_188, plain, (k7_relat_1(k6_relat_1('#skF_1'), '#skF_2')!=k6_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_162])).
% 14.29/6.87  tff(c_44258, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_44169, c_188])).
% 14.29/6.87  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 14.29/6.87  
% 14.29/6.87  Inference rules
% 14.29/6.87  ----------------------
% 14.29/6.87  #Ref     : 0
% 14.29/6.87  #Sup     : 11055
% 14.29/6.87  #Fact    : 0
% 14.29/6.87  #Define  : 0
% 14.29/6.87  #Split   : 2
% 14.29/6.87  #Chain   : 0
% 14.29/6.87  #Close   : 0
% 14.29/6.87  
% 14.29/6.87  Ordering : KBO
% 14.29/6.87  
% 14.29/6.87  Simplification rules
% 14.29/6.87  ----------------------
% 14.29/6.87  #Subsume      : 1828
% 14.29/6.87  #Demod        : 11236
% 14.29/6.87  #Tautology    : 3442
% 14.29/6.87  #SimpNegUnit  : 0
% 14.29/6.87  #BackRed      : 78
% 14.29/6.87  
% 14.29/6.87  #Partial instantiations: 0
% 14.29/6.87  #Strategies tried      : 1
% 14.29/6.87  
% 14.29/6.87  Timing (in seconds)
% 14.29/6.87  ----------------------
% 14.29/6.87  Preprocessing        : 0.34
% 14.29/6.87  Parsing              : 0.19
% 14.29/6.87  CNF conversion       : 0.02
% 14.29/6.87  Main loop            : 5.73
% 14.29/6.87  Inferencing          : 1.26
% 14.29/6.87  Reduction            : 2.15
% 14.29/6.87  Demodulation         : 1.76
% 14.29/6.87  BG Simplification    : 0.19
% 14.29/6.87  Subsumption          : 1.81
% 14.29/6.87  Abstraction          : 0.31
% 14.29/6.87  MUC search           : 0.00
% 14.29/6.87  Cooper               : 0.00
% 14.29/6.87  Total                : 6.12
% 14.29/6.87  Index Insertion      : 0.00
% 14.29/6.87  Index Deletion       : 0.00
% 14.29/6.87  Index Matching       : 0.00
% 14.29/6.87  BG Taut test         : 0.00
%------------------------------------------------------------------------------

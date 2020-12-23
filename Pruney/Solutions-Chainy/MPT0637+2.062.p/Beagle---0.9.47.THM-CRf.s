%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:03:32 EST 2020

% Result     : Theorem 46.32s
% Output     : CNFRefutation 46.32s
% Verified   : 
% Statistics : Number of formulae       :  188 (2398 expanded)
%              Number of leaves         :   37 ( 869 expanded)
%              Depth                    :   30
%              Number of atoms          :  323 (4197 expanded)
%              Number of equality atoms :  112 (1409 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    7 (   2 average)

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_118,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k5_relat_1(k6_relat_1(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).

tff(f_60,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k8_relat_1(A,B) = k5_relat_1(B,k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_relat_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_relat_1(B) )
     => v1_relat_1(k5_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).

tff(f_88,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_110,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k5_relat_1(A,k6_relat_1(k2_relat_1(A))) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_relat_1)).

tff(f_114,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k1_relat_1(k7_relat_1(B,A)) = k3_xboole_0(k1_relat_1(B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_relat_1)).

tff(f_67,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ! [C] :
          ( v1_relat_1(C)
         => k8_relat_1(A,k5_relat_1(B,C)) = k5_relat_1(B,k8_relat_1(A,C)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t139_relat_1)).

tff(f_27,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_100,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k5_relat_1(k6_relat_1(A),B) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_relat_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ! [C] :
          ( v1_relat_1(C)
         => k7_relat_1(k5_relat_1(B,C),A) = k5_relat_1(k7_relat_1(B,A),C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t112_relat_1)).

tff(f_94,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k5_relat_1(B,k6_relat_1(A)),B)
        & r1_tarski(k5_relat_1(k6_relat_1(A),B),B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_relat_1)).

tff(f_106,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k2_relat_1(B),A)
       => k5_relat_1(B,k6_relat_1(A)) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_relat_1)).

tff(f_74,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => r1_tarski(k2_relat_1(k5_relat_1(A,B)),k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_relat_1)).

tff(f_121,negated_conjecture,(
    ~ ! [A,B] : k5_relat_1(k6_relat_1(B),k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_funct_1)).

tff(c_20,plain,(
    ! [A_34] : v1_relat_1(k6_relat_1(A_34)) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_222,plain,(
    ! [A_96,B_97] :
      ( k5_relat_1(k6_relat_1(A_96),B_97) = k7_relat_1(B_97,A_96)
      | ~ v1_relat_1(B_97) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_24,plain,(
    ! [B_40,A_39] :
      ( k5_relat_1(B_40,k6_relat_1(A_39)) = k8_relat_1(A_39,B_40)
      | ~ v1_relat_1(B_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_229,plain,(
    ! [A_39,A_96] :
      ( k8_relat_1(A_39,k6_relat_1(A_96)) = k7_relat_1(k6_relat_1(A_39),A_96)
      | ~ v1_relat_1(k6_relat_1(A_96))
      | ~ v1_relat_1(k6_relat_1(A_39)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_222,c_24])).

tff(c_366,plain,(
    ! [A_109,A_110] : k8_relat_1(A_109,k6_relat_1(A_110)) = k7_relat_1(k6_relat_1(A_109),A_110) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_20,c_229])).

tff(c_146,plain,(
    ! [B_86,A_87] :
      ( k5_relat_1(B_86,k6_relat_1(A_87)) = k8_relat_1(A_87,B_86)
      | ~ v1_relat_1(B_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_18,plain,(
    ! [A_32,B_33] :
      ( v1_relat_1(k5_relat_1(A_32,B_33))
      | ~ v1_relat_1(B_33)
      | ~ v1_relat_1(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_156,plain,(
    ! [A_87,B_86] :
      ( v1_relat_1(k8_relat_1(A_87,B_86))
      | ~ v1_relat_1(k6_relat_1(A_87))
      | ~ v1_relat_1(B_86)
      | ~ v1_relat_1(B_86) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_146,c_18])).

tff(c_184,plain,(
    ! [A_87,B_86] :
      ( v1_relat_1(k8_relat_1(A_87,B_86))
      | ~ v1_relat_1(B_86) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_156])).

tff(c_376,plain,(
    ! [A_109,A_110] :
      ( v1_relat_1(k7_relat_1(k6_relat_1(A_109),A_110))
      | ~ v1_relat_1(k6_relat_1(A_110)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_366,c_184])).

tff(c_386,plain,(
    ! [A_109,A_110] : v1_relat_1(k7_relat_1(k6_relat_1(A_109),A_110)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_376])).

tff(c_32,plain,(
    ! [A_55] : k1_relat_1(k6_relat_1(A_55)) = A_55 ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_34,plain,(
    ! [A_55] : k2_relat_1(k6_relat_1(A_55)) = A_55 ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_44,plain,(
    ! [A_62] :
      ( k5_relat_1(A_62,k6_relat_1(k2_relat_1(A_62))) = A_62
      | ~ v1_relat_1(A_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_246,plain,(
    ! [A_96] :
      ( k7_relat_1(k6_relat_1(k2_relat_1(k6_relat_1(A_96))),A_96) = k6_relat_1(A_96)
      | ~ v1_relat_1(k6_relat_1(A_96))
      | ~ v1_relat_1(k6_relat_1(k2_relat_1(k6_relat_1(A_96)))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_222,c_44])).

tff(c_275,plain,(
    ! [A_96] : k7_relat_1(k6_relat_1(A_96),A_96) = k6_relat_1(A_96) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_20,c_34,c_246])).

tff(c_301,plain,(
    ! [B_101,A_102] :
      ( k3_xboole_0(k1_relat_1(B_101),A_102) = k1_relat_1(k7_relat_1(B_101,A_102))
      | ~ v1_relat_1(B_101) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_313,plain,(
    ! [A_55,A_102] :
      ( k1_relat_1(k7_relat_1(k6_relat_1(A_55),A_102)) = k3_xboole_0(A_55,A_102)
      | ~ v1_relat_1(k6_relat_1(A_55)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_301])).

tff(c_325,plain,(
    ! [A_105,A_106] : k1_relat_1(k7_relat_1(k6_relat_1(A_105),A_106)) = k3_xboole_0(A_105,A_106) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_313])).

tff(c_337,plain,(
    ! [A_96] : k3_xboole_0(A_96,A_96) = k1_relat_1(k6_relat_1(A_96)) ),
    inference(superposition,[status(thm),theory(equality)],[c_275,c_325])).

tff(c_340,plain,(
    ! [A_96] : k3_xboole_0(A_96,A_96) = A_96 ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_337])).

tff(c_317,plain,(
    ! [A_55,A_102] : k1_relat_1(k7_relat_1(k6_relat_1(A_55),A_102)) = k3_xboole_0(A_55,A_102) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_313])).

tff(c_267,plain,(
    ! [A_39,A_96] : k8_relat_1(A_39,k6_relat_1(A_96)) = k7_relat_1(k6_relat_1(A_39),A_96) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_20,c_229])).

tff(c_90,plain,(
    ! [A_78] :
      ( k5_relat_1(A_78,k6_relat_1(k2_relat_1(A_78))) = A_78
      | ~ v1_relat_1(A_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_102,plain,(
    ! [A_55] :
      ( k5_relat_1(k6_relat_1(A_55),k6_relat_1(A_55)) = k6_relat_1(A_55)
      | ~ v1_relat_1(k6_relat_1(A_55)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_90])).

tff(c_106,plain,(
    ! [A_55] : k5_relat_1(k6_relat_1(A_55),k6_relat_1(A_55)) = k6_relat_1(A_55) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_102])).

tff(c_1444,plain,(
    ! [A_169,B_170,C_171] :
      ( k8_relat_1(A_169,k5_relat_1(B_170,C_171)) = k5_relat_1(B_170,k8_relat_1(A_169,C_171))
      | ~ v1_relat_1(C_171)
      | ~ v1_relat_1(B_170) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_1485,plain,(
    ! [A_55,A_169] :
      ( k5_relat_1(k6_relat_1(A_55),k8_relat_1(A_169,k6_relat_1(A_55))) = k8_relat_1(A_169,k6_relat_1(A_55))
      | ~ v1_relat_1(k6_relat_1(A_55))
      | ~ v1_relat_1(k6_relat_1(A_55)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_106,c_1444])).

tff(c_2179,plain,(
    ! [A_212,A_213] : k5_relat_1(k6_relat_1(A_212),k7_relat_1(k6_relat_1(A_213),A_212)) = k7_relat_1(k6_relat_1(A_213),A_212) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_20,c_267,c_267,c_1485])).

tff(c_48,plain,(
    ! [A_65,B_66] :
      ( k5_relat_1(k6_relat_1(A_65),B_66) = k7_relat_1(B_66,A_65)
      | ~ v1_relat_1(B_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_2197,plain,(
    ! [A_213,A_212] :
      ( k7_relat_1(k7_relat_1(k6_relat_1(A_213),A_212),A_212) = k7_relat_1(k6_relat_1(A_213),A_212)
      | ~ v1_relat_1(k7_relat_1(k6_relat_1(A_213),A_212)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2179,c_48])).

tff(c_2234,plain,(
    ! [A_213,A_212] : k7_relat_1(k7_relat_1(k6_relat_1(A_213),A_212),A_212) = k7_relat_1(k6_relat_1(A_213),A_212) ),
    inference(demodulation,[status(thm),theory(equality)],[c_386,c_2197])).

tff(c_46,plain,(
    ! [B_64,A_63] :
      ( k3_xboole_0(k1_relat_1(B_64),A_63) = k1_relat_1(k7_relat_1(B_64,A_63))
      | ~ v1_relat_1(B_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_2,plain,(
    ! [A_1,B_2] : r1_tarski(k3_xboole_0(A_1,B_2),A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_393,plain,(
    ! [A_113,B_114] :
      ( k5_relat_1(k6_relat_1(A_113),B_114) = B_114
      | ~ r1_tarski(k1_relat_1(B_114),A_113)
      | ~ v1_relat_1(B_114) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_403,plain,(
    ! [A_113,A_55] :
      ( k5_relat_1(k6_relat_1(A_113),k6_relat_1(A_55)) = k6_relat_1(A_55)
      | ~ r1_tarski(A_55,A_113)
      | ~ v1_relat_1(k6_relat_1(A_55)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_393])).

tff(c_1147,plain,(
    ! [A_161,A_162] :
      ( k5_relat_1(k6_relat_1(A_161),k6_relat_1(A_162)) = k6_relat_1(A_162)
      | ~ r1_tarski(A_162,A_161) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_403])).

tff(c_1210,plain,(
    ! [A_39,A_161] :
      ( k8_relat_1(A_39,k6_relat_1(A_161)) = k6_relat_1(A_39)
      | ~ r1_tarski(A_39,A_161)
      | ~ v1_relat_1(k6_relat_1(A_161)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_1147])).

tff(c_1257,plain,(
    ! [A_163,A_164] :
      ( k7_relat_1(k6_relat_1(A_163),A_164) = k6_relat_1(A_163)
      | ~ r1_tarski(A_163,A_164) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_267,c_1210])).

tff(c_1291,plain,(
    ! [A_163,A_164] :
      ( k3_xboole_0(A_163,A_164) = k1_relat_1(k6_relat_1(A_163))
      | ~ r1_tarski(A_163,A_164) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1257,c_317])).

tff(c_1346,plain,(
    ! [A_165,A_166] :
      ( k3_xboole_0(A_165,A_166) = A_165
      | ~ r1_tarski(A_165,A_166) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_1291])).

tff(c_1408,plain,(
    ! [A_167,B_168] : k3_xboole_0(k3_xboole_0(A_167,B_168),A_167) = k3_xboole_0(A_167,B_168) ),
    inference(resolution,[status(thm)],[c_2,c_1346])).

tff(c_22654,plain,(
    ! [B_660,A_661] :
      ( k3_xboole_0(k1_relat_1(k7_relat_1(B_660,A_661)),k1_relat_1(B_660)) = k3_xboole_0(k1_relat_1(B_660),A_661)
      | ~ v1_relat_1(B_660) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_1408])).

tff(c_22820,plain,(
    ! [A_213,A_212] :
      ( k3_xboole_0(k1_relat_1(k7_relat_1(k6_relat_1(A_213),A_212)),k1_relat_1(k7_relat_1(k6_relat_1(A_213),A_212))) = k3_xboole_0(k1_relat_1(k7_relat_1(k6_relat_1(A_213),A_212)),A_212)
      | ~ v1_relat_1(k7_relat_1(k6_relat_1(A_213),A_212)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2234,c_22654])).

tff(c_22861,plain,(
    ! [A_213,A_212] : k3_xboole_0(k3_xboole_0(A_213,A_212),A_212) = k3_xboole_0(A_213,A_212) ),
    inference(demodulation,[status(thm),theory(equality)],[c_386,c_340,c_317,c_317,c_317,c_22820])).

tff(c_515,plain,(
    ! [B_124,A_125] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_124,A_125)),k1_relat_1(B_124))
      | ~ v1_relat_1(B_124) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_301,c_2])).

tff(c_40,plain,(
    ! [A_58,B_59] :
      ( k5_relat_1(k6_relat_1(A_58),B_59) = B_59
      | ~ r1_tarski(k1_relat_1(B_59),A_58)
      | ~ v1_relat_1(B_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_156784,plain,(
    ! [B_1649,A_1650] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(B_1649)),k7_relat_1(B_1649,A_1650)) = k7_relat_1(B_1649,A_1650)
      | ~ v1_relat_1(k7_relat_1(B_1649,A_1650))
      | ~ v1_relat_1(B_1649) ) ),
    inference(resolution,[status(thm)],[c_515,c_40])).

tff(c_1482,plain,(
    ! [B_40,A_169,A_39] :
      ( k5_relat_1(B_40,k8_relat_1(A_169,k6_relat_1(A_39))) = k8_relat_1(A_169,k8_relat_1(A_39,B_40))
      | ~ v1_relat_1(k6_relat_1(A_39))
      | ~ v1_relat_1(B_40)
      | ~ v1_relat_1(B_40) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_1444])).

tff(c_5822,plain,(
    ! [B_303,A_304,A_305] :
      ( k5_relat_1(B_303,k7_relat_1(k6_relat_1(A_304),A_305)) = k8_relat_1(A_304,k8_relat_1(A_305,B_303))
      | ~ v1_relat_1(B_303) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_267,c_1482])).

tff(c_5869,plain,(
    ! [A_304,A_305,A_65] :
      ( k8_relat_1(A_304,k8_relat_1(A_305,k6_relat_1(A_65))) = k7_relat_1(k7_relat_1(k6_relat_1(A_304),A_305),A_65)
      | ~ v1_relat_1(k7_relat_1(k6_relat_1(A_304),A_305))
      | ~ v1_relat_1(k6_relat_1(A_65)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5822,c_48])).

tff(c_5943,plain,(
    ! [A_304,A_305,A_65] : k8_relat_1(A_304,k7_relat_1(k6_relat_1(A_305),A_65)) = k7_relat_1(k7_relat_1(k6_relat_1(A_304),A_305),A_65) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_386,c_267,c_5869])).

tff(c_1479,plain,(
    ! [A_65,A_169,B_66] :
      ( k5_relat_1(k6_relat_1(A_65),k8_relat_1(A_169,B_66)) = k8_relat_1(A_169,k7_relat_1(B_66,A_65))
      | ~ v1_relat_1(B_66)
      | ~ v1_relat_1(k6_relat_1(A_65))
      | ~ v1_relat_1(B_66) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_1444])).

tff(c_3396,plain,(
    ! [A_243,A_244,B_245] :
      ( k5_relat_1(k6_relat_1(A_243),k8_relat_1(A_244,B_245)) = k8_relat_1(A_244,k7_relat_1(B_245,A_243))
      | ~ v1_relat_1(B_245) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_1479])).

tff(c_3446,plain,(
    ! [A_243,A_39,A_96] :
      ( k5_relat_1(k6_relat_1(A_243),k7_relat_1(k6_relat_1(A_39),A_96)) = k8_relat_1(A_39,k7_relat_1(k6_relat_1(A_96),A_243))
      | ~ v1_relat_1(k6_relat_1(A_96)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_267,c_3396])).

tff(c_3469,plain,(
    ! [A_243,A_39,A_96] : k5_relat_1(k6_relat_1(A_243),k7_relat_1(k6_relat_1(A_39),A_96)) = k8_relat_1(A_39,k7_relat_1(k6_relat_1(A_96),A_243)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_3446])).

tff(c_40778,plain,(
    ! [A_243,A_39,A_96] : k5_relat_1(k6_relat_1(A_243),k7_relat_1(k6_relat_1(A_39),A_96)) = k7_relat_1(k7_relat_1(k6_relat_1(A_39),A_96),A_243) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5943,c_3469])).

tff(c_156859,plain,(
    ! [A_39,A_1650] :
      ( k7_relat_1(k7_relat_1(k6_relat_1(A_39),A_1650),k1_relat_1(k6_relat_1(A_39))) = k7_relat_1(k6_relat_1(A_39),A_1650)
      | ~ v1_relat_1(k7_relat_1(k6_relat_1(A_39),A_1650))
      | ~ v1_relat_1(k6_relat_1(A_39)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_156784,c_40778])).

tff(c_157189,plain,(
    ! [A_1651,A_1652] : k7_relat_1(k7_relat_1(k6_relat_1(A_1651),A_1652),A_1651) = k7_relat_1(k6_relat_1(A_1651),A_1652) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_386,c_32,c_156859])).

tff(c_1084,plain,(
    ! [B_158,C_159,A_160] :
      ( k7_relat_1(k5_relat_1(B_158,C_159),A_160) = k5_relat_1(k7_relat_1(B_158,A_160),C_159)
      | ~ v1_relat_1(C_159)
      | ~ v1_relat_1(B_158) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_1123,plain,(
    ! [A_65,A_160,B_66] :
      ( k5_relat_1(k7_relat_1(k6_relat_1(A_65),A_160),B_66) = k7_relat_1(k7_relat_1(B_66,A_65),A_160)
      | ~ v1_relat_1(B_66)
      | ~ v1_relat_1(k6_relat_1(A_65))
      | ~ v1_relat_1(B_66) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_1084])).

tff(c_4917,plain,(
    ! [A_274,A_275,B_276] :
      ( k5_relat_1(k7_relat_1(k6_relat_1(A_274),A_275),B_276) = k7_relat_1(k7_relat_1(B_276,A_274),A_275)
      | ~ v1_relat_1(B_276) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_1123])).

tff(c_38,plain,(
    ! [B_57,A_56] :
      ( r1_tarski(k5_relat_1(B_57,k6_relat_1(A_56)),B_57)
      | ~ v1_relat_1(B_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_4971,plain,(
    ! [A_56,A_274,A_275] :
      ( r1_tarski(k7_relat_1(k7_relat_1(k6_relat_1(A_56),A_274),A_275),k7_relat_1(k6_relat_1(A_274),A_275))
      | ~ v1_relat_1(k7_relat_1(k6_relat_1(A_274),A_275))
      | ~ v1_relat_1(k6_relat_1(A_56)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4917,c_38])).

tff(c_5045,plain,(
    ! [A_56,A_274,A_275] : r1_tarski(k7_relat_1(k7_relat_1(k6_relat_1(A_56),A_274),A_275),k7_relat_1(k6_relat_1(A_274),A_275)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_386,c_4971])).

tff(c_157528,plain,(
    ! [A_1651,A_1652] : r1_tarski(k7_relat_1(k6_relat_1(A_1651),A_1652),k7_relat_1(k6_relat_1(A_1652),A_1651)) ),
    inference(superposition,[status(thm),theory(equality)],[c_157189,c_5045])).

tff(c_157956,plain,(
    ! [A_1653,A_1654] : r1_tarski(k7_relat_1(k6_relat_1(A_1653),A_1654),k7_relat_1(k6_relat_1(A_1654),A_1653)) ),
    inference(superposition,[status(thm),theory(equality)],[c_157189,c_5045])).

tff(c_639,plain,(
    ! [B_139,A_140] :
      ( k5_relat_1(B_139,k6_relat_1(A_140)) = B_139
      | ~ r1_tarski(k2_relat_1(B_139),A_140)
      | ~ v1_relat_1(B_139) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_661,plain,(
    ! [A_55,A_140] :
      ( k5_relat_1(k6_relat_1(A_55),k6_relat_1(A_140)) = k6_relat_1(A_55)
      | ~ r1_tarski(A_55,A_140)
      | ~ v1_relat_1(k6_relat_1(A_55)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_639])).

tff(c_805,plain,(
    ! [A_148,A_149] :
      ( k5_relat_1(k6_relat_1(A_148),k6_relat_1(A_149)) = k6_relat_1(A_148)
      | ~ r1_tarski(A_148,A_149) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_661])).

tff(c_859,plain,(
    ! [A_39,A_148] :
      ( k8_relat_1(A_39,k6_relat_1(A_148)) = k6_relat_1(A_148)
      | ~ r1_tarski(A_148,A_39)
      | ~ v1_relat_1(k6_relat_1(A_148)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_805])).

tff(c_896,plain,(
    ! [A_39,A_148] :
      ( k7_relat_1(k6_relat_1(A_39),A_148) = k6_relat_1(A_148)
      | ~ r1_tarski(A_148,A_39) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_267,c_859])).

tff(c_468,plain,(
    ! [A_118,B_119] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_118,B_119)),k2_relat_1(B_119))
      | ~ v1_relat_1(B_119)
      | ~ v1_relat_1(A_118) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_477,plain,(
    ! [A_39,B_40] :
      ( r1_tarski(k2_relat_1(k8_relat_1(A_39,B_40)),k2_relat_1(k6_relat_1(A_39)))
      | ~ v1_relat_1(k6_relat_1(A_39))
      | ~ v1_relat_1(B_40)
      | ~ v1_relat_1(B_40) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_468])).

tff(c_499,plain,(
    ! [A_120,B_121] :
      ( r1_tarski(k2_relat_1(k8_relat_1(A_120,B_121)),A_120)
      | ~ v1_relat_1(B_121) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_34,c_477])).

tff(c_502,plain,(
    ! [A_39,A_96] :
      ( r1_tarski(k2_relat_1(k7_relat_1(k6_relat_1(A_39),A_96)),A_39)
      | ~ v1_relat_1(k6_relat_1(A_96)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_267,c_499])).

tff(c_507,plain,(
    ! [A_39,A_96] : r1_tarski(k2_relat_1(k7_relat_1(k6_relat_1(A_39),A_96)),A_39) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_502])).

tff(c_1250,plain,(
    ! [A_39,A_161] :
      ( k7_relat_1(k6_relat_1(A_39),A_161) = k6_relat_1(A_39)
      | ~ r1_tarski(A_39,A_161) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_267,c_1210])).

tff(c_5016,plain,(
    ! [A_274,A_275] :
      ( k7_relat_1(k7_relat_1(k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(A_274),A_275))),A_274),A_275) = k7_relat_1(k6_relat_1(A_274),A_275)
      | ~ v1_relat_1(k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(A_274),A_275))))
      | ~ v1_relat_1(k7_relat_1(k6_relat_1(A_274),A_275)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_4917])).

tff(c_46461,plain,(
    ! [A_939,A_940] : k7_relat_1(k7_relat_1(k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(A_939),A_940))),A_939),A_940) = k7_relat_1(k6_relat_1(A_939),A_940) ),
    inference(demodulation,[status(thm),theory(equality)],[c_386,c_20,c_5016])).

tff(c_524,plain,(
    ! [A_55,A_102,A_125] :
      ( r1_tarski(k1_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(A_55),A_102),A_125)),k3_xboole_0(A_55,A_102))
      | ~ v1_relat_1(k7_relat_1(k6_relat_1(A_55),A_102)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_317,c_515])).

tff(c_535,plain,(
    ! [A_55,A_102,A_125] : r1_tarski(k1_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(A_55),A_102),A_125)),k3_xboole_0(A_55,A_102)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_386,c_524])).

tff(c_486,plain,(
    ! [A_118,A_55] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_118,k6_relat_1(A_55))),A_55)
      | ~ v1_relat_1(k6_relat_1(A_55))
      | ~ v1_relat_1(A_118) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_468])).

tff(c_498,plain,(
    ! [A_118,A_55] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_118,k6_relat_1(A_55))),A_55)
      | ~ v1_relat_1(A_118) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_486])).

tff(c_4953,plain,(
    ! [A_55,A_274,A_275] :
      ( r1_tarski(k2_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(A_55),A_274),A_275)),A_55)
      | ~ v1_relat_1(k7_relat_1(k6_relat_1(A_274),A_275))
      | ~ v1_relat_1(k6_relat_1(A_55)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4917,c_498])).

tff(c_5128,plain,(
    ! [A_283,A_284,A_285] : r1_tarski(k2_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(A_283),A_284),A_285)),A_283) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_386,c_4953])).

tff(c_5332,plain,(
    ! [A_288,A_289,A_290] :
      ( r1_tarski(k2_relat_1(k7_relat_1(k6_relat_1(A_288),A_289)),A_290)
      | ~ r1_tarski(A_288,A_290) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_896,c_5128])).

tff(c_5363,plain,(
    ! [A_148,A_290,A_39] :
      ( r1_tarski(k2_relat_1(k6_relat_1(A_148)),A_290)
      | ~ r1_tarski(A_39,A_290)
      | ~ r1_tarski(A_148,A_39) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_896,c_5332])).

tff(c_5384,plain,(
    ! [A_291,A_292,A_293] :
      ( r1_tarski(A_291,A_292)
      | ~ r1_tarski(A_293,A_292)
      | ~ r1_tarski(A_291,A_293) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_5363])).

tff(c_5451,plain,(
    ! [A_294,A_295,B_296] :
      ( r1_tarski(A_294,A_295)
      | ~ r1_tarski(A_294,k3_xboole_0(A_295,B_296)) ) ),
    inference(resolution,[status(thm)],[c_2,c_5384])).

tff(c_5582,plain,(
    ! [A_55,A_102,A_125] : r1_tarski(k1_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(A_55),A_102),A_125)),A_55) ),
    inference(resolution,[status(thm)],[c_535,c_5451])).

tff(c_46644,plain,(
    ! [A_939,A_940] : r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1(A_939),A_940)),k2_relat_1(k7_relat_1(k6_relat_1(A_939),A_940))) ),
    inference(superposition,[status(thm),theory(equality)],[c_46461,c_5582])).

tff(c_46866,plain,(
    ! [A_941,A_942] : r1_tarski(k3_xboole_0(A_941,A_942),k2_relat_1(k7_relat_1(k6_relat_1(A_941),A_942))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_317,c_46644])).

tff(c_66282,plain,(
    ! [B_1125,A_1126] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_1125,A_1126)),k2_relat_1(k7_relat_1(k6_relat_1(k1_relat_1(B_1125)),A_1126)))
      | ~ v1_relat_1(B_1125) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_46866])).

tff(c_66344,plain,(
    ! [A_39,A_161] :
      ( r1_tarski(k1_relat_1(k6_relat_1(A_39)),k2_relat_1(k7_relat_1(k6_relat_1(k1_relat_1(k6_relat_1(A_39))),A_161)))
      | ~ v1_relat_1(k6_relat_1(A_39))
      | ~ r1_tarski(A_39,A_161) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1250,c_66282])).

tff(c_66428,plain,(
    ! [A_1127,A_1128] :
      ( r1_tarski(A_1127,k2_relat_1(k7_relat_1(k6_relat_1(A_1127),A_1128)))
      | ~ r1_tarski(A_1127,A_1128) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_32,c_32,c_66344])).

tff(c_671,plain,(
    ! [A_55,A_140] :
      ( k5_relat_1(k6_relat_1(A_55),k6_relat_1(A_140)) = k6_relat_1(A_55)
      | ~ r1_tarski(A_55,A_140) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_661])).

tff(c_1156,plain,(
    ! [A_162,A_161] :
      ( k6_relat_1(A_162) = k6_relat_1(A_161)
      | ~ r1_tarski(A_161,A_162)
      | ~ r1_tarski(A_162,A_161) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1147,c_671])).

tff(c_66455,plain,(
    ! [A_1127,A_1128] :
      ( k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(A_1127),A_1128))) = k6_relat_1(A_1127)
      | ~ r1_tarski(k2_relat_1(k7_relat_1(k6_relat_1(A_1127),A_1128)),A_1127)
      | ~ r1_tarski(A_1127,A_1128) ) ),
    inference(resolution,[status(thm)],[c_66428,c_1156])).

tff(c_66533,plain,(
    ! [A_1129,A_1130] :
      ( k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(A_1129),A_1130))) = k6_relat_1(A_1129)
      | ~ r1_tarski(A_1129,A_1130) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_507,c_66455])).

tff(c_67381,plain,(
    ! [A_1129,A_1130] :
      ( k2_relat_1(k7_relat_1(k6_relat_1(A_1129),A_1130)) = k1_relat_1(k6_relat_1(A_1129))
      | ~ r1_tarski(A_1129,A_1130) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_66533,c_32])).

tff(c_67514,plain,(
    ! [A_1131,A_1132] :
      ( k2_relat_1(k7_relat_1(k6_relat_1(A_1131),A_1132)) = A_1131
      | ~ r1_tarski(A_1131,A_1132) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_67381])).

tff(c_67762,plain,(
    ! [A_148,A_39] :
      ( k2_relat_1(k6_relat_1(A_148)) = A_39
      | ~ r1_tarski(A_39,A_148)
      | ~ r1_tarski(A_148,A_39) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_896,c_67514])).

tff(c_67860,plain,(
    ! [A_39,A_148] :
      ( A_39 = A_148
      | ~ r1_tarski(A_39,A_148)
      | ~ r1_tarski(A_148,A_39) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_67762])).

tff(c_157970,plain,(
    ! [A_1654,A_1653] :
      ( k7_relat_1(k6_relat_1(A_1654),A_1653) = k7_relat_1(k6_relat_1(A_1653),A_1654)
      | ~ r1_tarski(k7_relat_1(k6_relat_1(A_1654),A_1653),k7_relat_1(k6_relat_1(A_1653),A_1654)) ) ),
    inference(resolution,[status(thm)],[c_157956,c_67860])).

tff(c_158216,plain,(
    ! [A_1656,A_1655] : k7_relat_1(k6_relat_1(A_1656),A_1655) = k7_relat_1(k6_relat_1(A_1655),A_1656) ),
    inference(demodulation,[status(thm),theory(equality)],[c_157528,c_157970])).

tff(c_1435,plain,(
    ! [B_64,A_63] :
      ( k3_xboole_0(k1_relat_1(k7_relat_1(B_64,A_63)),k1_relat_1(B_64)) = k3_xboole_0(k1_relat_1(B_64),A_63)
      | ~ v1_relat_1(B_64) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_1408])).

tff(c_159612,plain,(
    ! [A_1655,A_1656] :
      ( k3_xboole_0(k1_relat_1(k7_relat_1(k6_relat_1(A_1655),A_1656)),k1_relat_1(k6_relat_1(A_1656))) = k3_xboole_0(k1_relat_1(k6_relat_1(A_1656)),A_1655)
      | ~ v1_relat_1(k6_relat_1(A_1656)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_158216,c_1435])).

tff(c_160652,plain,(
    ! [A_1656,A_1655] : k3_xboole_0(A_1656,A_1655) = k3_xboole_0(A_1655,A_1656) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_22861,c_317,c_32,c_32,c_159612])).

tff(c_36,plain,(
    ! [A_56,B_57] :
      ( r1_tarski(k5_relat_1(k6_relat_1(A_56),B_57),B_57)
      | ~ v1_relat_1(B_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_153,plain,(
    ! [A_87,A_56] :
      ( r1_tarski(k8_relat_1(A_87,k6_relat_1(A_56)),k6_relat_1(A_87))
      | ~ v1_relat_1(k6_relat_1(A_87))
      | ~ v1_relat_1(k6_relat_1(A_56)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_146,c_36])).

tff(c_182,plain,(
    ! [A_87,A_56] : r1_tarski(k8_relat_1(A_87,k6_relat_1(A_56)),k6_relat_1(A_87)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_20,c_153])).

tff(c_364,plain,(
    ! [A_87,A_56] : r1_tarski(k7_relat_1(k6_relat_1(A_87),A_56),k6_relat_1(A_87)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_267,c_182])).

tff(c_904,plain,(
    ! [A_152,A_153] :
      ( k7_relat_1(k6_relat_1(A_152),A_153) = k6_relat_1(A_153)
      | ~ r1_tarski(A_153,A_152) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_267,c_859])).

tff(c_935,plain,(
    ! [A_152,A_153] :
      ( k3_xboole_0(A_152,A_153) = k1_relat_1(k6_relat_1(A_153))
      | ~ r1_tarski(A_153,A_152) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_904,c_317])).

tff(c_986,plain,(
    ! [A_154,A_155] :
      ( k3_xboole_0(A_154,A_155) = A_155
      | ~ r1_tarski(A_155,A_154) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_935])).

tff(c_4041,plain,(
    ! [A_256,A_257] : k3_xboole_0(k6_relat_1(A_256),k7_relat_1(k6_relat_1(A_256),A_257)) = k7_relat_1(k6_relat_1(A_256),A_257) ),
    inference(resolution,[status(thm)],[c_364,c_986])).

tff(c_108120,plain,(
    ! [A_1428,A_1429] :
      ( k3_xboole_0(k6_relat_1(A_1428),k6_relat_1(A_1429)) = k7_relat_1(k6_relat_1(A_1428),A_1429)
      | ~ r1_tarski(A_1429,A_1428) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_896,c_4041])).

tff(c_341,plain,(
    ! [A_107] : k3_xboole_0(A_107,A_107) = A_107 ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_337])).

tff(c_351,plain,(
    ! [A_107] : r1_tarski(A_107,A_107) ),
    inference(superposition,[status(thm),theory(equality)],[c_341,c_2])).

tff(c_827,plain,(
    ! [A_148,A_149] :
      ( r1_tarski(k6_relat_1(A_148),k6_relat_1(A_149))
      | ~ v1_relat_1(k6_relat_1(A_149))
      | ~ r1_tarski(A_148,A_149) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_805,c_36])).

tff(c_879,plain,(
    ! [A_148,A_149] :
      ( r1_tarski(k6_relat_1(A_148),k6_relat_1(A_149))
      | ~ r1_tarski(A_148,A_149) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_827])).

tff(c_13558,plain,(
    ! [A_498,A_499,A_500] :
      ( r1_tarski(A_498,k6_relat_1(A_499))
      | ~ r1_tarski(A_498,k6_relat_1(A_500))
      | ~ r1_tarski(A_500,A_499) ) ),
    inference(resolution,[status(thm)],[c_879,c_5384])).

tff(c_14447,plain,(
    ! [A_514,A_515,A_516] :
      ( r1_tarski(k6_relat_1(A_514),k6_relat_1(A_515))
      | ~ r1_tarski(A_516,A_515)
      | ~ r1_tarski(A_514,A_516) ) ),
    inference(resolution,[status(thm)],[c_879,c_13558])).

tff(c_14655,plain,(
    ! [A_517,A_518,B_519] :
      ( r1_tarski(k6_relat_1(A_517),k6_relat_1(A_518))
      | ~ r1_tarski(A_517,k3_xboole_0(A_518,B_519)) ) ),
    inference(resolution,[status(thm)],[c_2,c_14447])).

tff(c_14848,plain,(
    ! [A_520,B_521] : r1_tarski(k6_relat_1(k3_xboole_0(A_520,B_521)),k6_relat_1(A_520)) ),
    inference(resolution,[status(thm)],[c_351,c_14655])).

tff(c_972,plain,(
    ! [A_152,A_153] :
      ( k3_xboole_0(A_152,A_153) = A_153
      | ~ r1_tarski(A_153,A_152) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_935])).

tff(c_14943,plain,(
    ! [A_520,B_521] : k3_xboole_0(k6_relat_1(A_520),k6_relat_1(k3_xboole_0(A_520,B_521))) = k6_relat_1(k3_xboole_0(A_520,B_521)) ),
    inference(resolution,[status(thm)],[c_14848,c_972])).

tff(c_108328,plain,(
    ! [A_1428,B_521] :
      ( k7_relat_1(k6_relat_1(A_1428),k3_xboole_0(A_1428,B_521)) = k6_relat_1(k3_xboole_0(A_1428,B_521))
      | ~ r1_tarski(k3_xboole_0(A_1428,B_521),A_1428) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_108120,c_14943])).

tff(c_108955,plain,(
    ! [A_1433,B_1434] : k7_relat_1(k6_relat_1(A_1433),k3_xboole_0(A_1433,B_1434)) = k6_relat_1(k3_xboole_0(A_1433,B_1434)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_108328])).

tff(c_3421,plain,(
    ! [A_244,B_245,A_243] :
      ( r1_tarski(k8_relat_1(A_244,k7_relat_1(B_245,A_243)),k8_relat_1(A_244,B_245))
      | ~ v1_relat_1(k8_relat_1(A_244,B_245))
      | ~ v1_relat_1(B_245) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3396,c_36])).

tff(c_109126,plain,(
    ! [A_244,A_1433,B_1434] :
      ( r1_tarski(k8_relat_1(A_244,k6_relat_1(k3_xboole_0(A_1433,B_1434))),k8_relat_1(A_244,k6_relat_1(A_1433)))
      | ~ v1_relat_1(k8_relat_1(A_244,k6_relat_1(A_1433)))
      | ~ v1_relat_1(k6_relat_1(A_1433)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_108955,c_3421])).

tff(c_111480,plain,(
    ! [A_1441,A_1442,B_1443] : r1_tarski(k7_relat_1(k6_relat_1(A_1441),k3_xboole_0(A_1442,B_1443)),k7_relat_1(k6_relat_1(A_1441),A_1442)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_386,c_267,c_267,c_267,c_109126])).

tff(c_112358,plain,(
    ! [A_1448,B_1449] : r1_tarski(k6_relat_1(k3_xboole_0(A_1448,B_1449)),k7_relat_1(k6_relat_1(k3_xboole_0(A_1448,B_1449)),A_1448)) ),
    inference(superposition,[status(thm),theory(equality)],[c_275,c_111480])).

tff(c_112365,plain,(
    ! [A_1448,B_1449] :
      ( k7_relat_1(k6_relat_1(k3_xboole_0(A_1448,B_1449)),A_1448) = k6_relat_1(k3_xboole_0(A_1448,B_1449))
      | ~ r1_tarski(k7_relat_1(k6_relat_1(k3_xboole_0(A_1448,B_1449)),A_1448),k6_relat_1(k3_xboole_0(A_1448,B_1449))) ) ),
    inference(resolution,[status(thm)],[c_112358,c_67860])).

tff(c_112752,plain,(
    ! [A_1448,B_1449] : k7_relat_1(k6_relat_1(k3_xboole_0(A_1448,B_1449)),A_1448) = k6_relat_1(k3_xboole_0(A_1448,B_1449)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_364,c_112365])).

tff(c_46723,plain,(
    ! [A_161,A_940] :
      ( k7_relat_1(k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(A_161),A_940))),A_940) = k7_relat_1(k6_relat_1(A_161),A_940)
      | ~ r1_tarski(k2_relat_1(k7_relat_1(k6_relat_1(A_161),A_940)),A_161) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1250,c_46461])).

tff(c_88388,plain,(
    ! [A_1262,A_1263] : k7_relat_1(k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(A_1262),A_1263))),A_1263) = k7_relat_1(k6_relat_1(A_1262),A_1263) ),
    inference(demodulation,[status(thm),theory(equality)],[c_507,c_46723])).

tff(c_88988,plain,(
    ! [A_1262,A_1263] : k3_xboole_0(k2_relat_1(k7_relat_1(k6_relat_1(A_1262),A_1263)),A_1263) = k1_relat_1(k7_relat_1(k6_relat_1(A_1262),A_1263)) ),
    inference(superposition,[status(thm),theory(equality)],[c_88388,c_317])).

tff(c_89278,plain,(
    ! [A_1262,A_1263] : k3_xboole_0(k2_relat_1(k7_relat_1(k6_relat_1(A_1262),A_1263)),A_1263) = k3_xboole_0(A_1262,A_1263) ),
    inference(demodulation,[status(thm),theory(equality)],[c_317,c_88988])).

tff(c_1398,plain,(
    ! [A_39,A_96] : k3_xboole_0(k2_relat_1(k7_relat_1(k6_relat_1(A_39),A_96)),A_39) = k2_relat_1(k7_relat_1(k6_relat_1(A_39),A_96)) ),
    inference(resolution,[status(thm)],[c_507,c_1346])).

tff(c_158572,plain,(
    ! [A_1655,A_1656] : k3_xboole_0(k2_relat_1(k7_relat_1(k6_relat_1(A_1655),A_1656)),A_1656) = k2_relat_1(k7_relat_1(k6_relat_1(A_1656),A_1655)) ),
    inference(superposition,[status(thm),theory(equality)],[c_158216,c_1398])).

tff(c_160376,plain,(
    ! [A_1656,A_1655] : k2_relat_1(k7_relat_1(k6_relat_1(A_1656),A_1655)) = k3_xboole_0(A_1655,A_1656) ),
    inference(demodulation,[status(thm),theory(equality)],[c_89278,c_158572])).

tff(c_46860,plain,(
    ! [A_161,A_940] : k7_relat_1(k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(A_161),A_940))),A_940) = k7_relat_1(k6_relat_1(A_161),A_940) ),
    inference(demodulation,[status(thm),theory(equality)],[c_507,c_46723])).

tff(c_173340,plain,(
    ! [A_940,A_161] : k7_relat_1(k6_relat_1(k3_xboole_0(A_940,A_161)),A_940) = k7_relat_1(k6_relat_1(A_161),A_940) ),
    inference(demodulation,[status(thm),theory(equality)],[c_160376,c_46860])).

tff(c_173374,plain,(
    ! [A_161,A_940] : k7_relat_1(k6_relat_1(A_161),A_940) = k6_relat_1(k3_xboole_0(A_940,A_161)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_112752,c_173340])).

tff(c_50,plain,(
    k5_relat_1(k6_relat_1('#skF_2'),k6_relat_1('#skF_1')) != k6_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_242,plain,
    ( k7_relat_1(k6_relat_1('#skF_1'),'#skF_2') != k6_relat_1(k3_xboole_0('#skF_1','#skF_2'))
    | ~ v1_relat_1(k6_relat_1('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_222,c_50])).

tff(c_273,plain,(
    k7_relat_1(k6_relat_1('#skF_1'),'#skF_2') != k6_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_242])).

tff(c_173853,plain,(
    k6_relat_1(k3_xboole_0('#skF_2','#skF_1')) != k6_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_173374,c_273])).

tff(c_173895,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_160652,c_173853])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:53:22 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 46.32/35.69  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 46.32/35.71  
% 46.32/35.71  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 46.32/35.71  %$ r1_tarski > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k8_relat_1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1
% 46.32/35.71  
% 46.32/35.71  %Foreground sorts:
% 46.32/35.71  
% 46.32/35.71  
% 46.32/35.71  %Background operators:
% 46.32/35.71  
% 46.32/35.71  
% 46.32/35.71  %Foreground operators:
% 46.32/35.71  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 46.32/35.71  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 46.32/35.71  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 46.32/35.71  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 46.32/35.71  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 46.32/35.71  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 46.32/35.71  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 46.32/35.71  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 46.32/35.71  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 46.32/35.71  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 46.32/35.71  tff('#skF_2', type, '#skF_2': $i).
% 46.32/35.71  tff('#skF_1', type, '#skF_1': $i).
% 46.32/35.71  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 46.32/35.71  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 46.32/35.71  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 46.32/35.71  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 46.32/35.71  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 46.32/35.71  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 46.32/35.71  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 46.32/35.71  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 46.32/35.71  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 46.32/35.71  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 46.32/35.71  
% 46.32/35.74  tff(f_49, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 46.32/35.74  tff(f_118, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_relat_1)).
% 46.32/35.74  tff(f_60, axiom, (![A, B]: (v1_relat_1(B) => (k8_relat_1(A, B) = k5_relat_1(B, k6_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t123_relat_1)).
% 46.32/35.74  tff(f_47, axiom, (![A, B]: ((v1_relat_1(A) & v1_relat_1(B)) => v1_relat_1(k5_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k5_relat_1)).
% 46.32/35.74  tff(f_88, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 46.32/35.74  tff(f_110, axiom, (![A]: (v1_relat_1(A) => (k5_relat_1(A, k6_relat_1(k2_relat_1(A))) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t80_relat_1)).
% 46.32/35.74  tff(f_114, axiom, (![A, B]: (v1_relat_1(B) => (k1_relat_1(k7_relat_1(B, A)) = k3_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t90_relat_1)).
% 46.32/35.74  tff(f_67, axiom, (![A, B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (k8_relat_1(A, k5_relat_1(B, C)) = k5_relat_1(B, k8_relat_1(A, C))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t139_relat_1)).
% 46.32/35.74  tff(f_27, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 46.32/35.74  tff(f_100, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k5_relat_1(k6_relat_1(A), B) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t77_relat_1)).
% 46.32/35.74  tff(f_56, axiom, (![A, B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (k7_relat_1(k5_relat_1(B, C), A) = k5_relat_1(k7_relat_1(B, A), C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t112_relat_1)).
% 46.32/35.74  tff(f_94, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k5_relat_1(B, k6_relat_1(A)), B) & r1_tarski(k5_relat_1(k6_relat_1(A), B), B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t76_relat_1)).
% 46.32/35.74  tff(f_106, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k5_relat_1(B, k6_relat_1(A)) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_relat_1)).
% 46.32/35.74  tff(f_74, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k2_relat_1(k5_relat_1(A, B)), k2_relat_1(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t45_relat_1)).
% 46.32/35.74  tff(f_121, negated_conjecture, ~(![A, B]: (k5_relat_1(k6_relat_1(B), k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_funct_1)).
% 46.32/35.74  tff(c_20, plain, (![A_34]: (v1_relat_1(k6_relat_1(A_34)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 46.32/35.74  tff(c_222, plain, (![A_96, B_97]: (k5_relat_1(k6_relat_1(A_96), B_97)=k7_relat_1(B_97, A_96) | ~v1_relat_1(B_97))), inference(cnfTransformation, [status(thm)], [f_118])).
% 46.32/35.74  tff(c_24, plain, (![B_40, A_39]: (k5_relat_1(B_40, k6_relat_1(A_39))=k8_relat_1(A_39, B_40) | ~v1_relat_1(B_40))), inference(cnfTransformation, [status(thm)], [f_60])).
% 46.32/35.74  tff(c_229, plain, (![A_39, A_96]: (k8_relat_1(A_39, k6_relat_1(A_96))=k7_relat_1(k6_relat_1(A_39), A_96) | ~v1_relat_1(k6_relat_1(A_96)) | ~v1_relat_1(k6_relat_1(A_39)))), inference(superposition, [status(thm), theory('equality')], [c_222, c_24])).
% 46.32/35.74  tff(c_366, plain, (![A_109, A_110]: (k8_relat_1(A_109, k6_relat_1(A_110))=k7_relat_1(k6_relat_1(A_109), A_110))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_20, c_229])).
% 46.32/35.74  tff(c_146, plain, (![B_86, A_87]: (k5_relat_1(B_86, k6_relat_1(A_87))=k8_relat_1(A_87, B_86) | ~v1_relat_1(B_86))), inference(cnfTransformation, [status(thm)], [f_60])).
% 46.32/35.74  tff(c_18, plain, (![A_32, B_33]: (v1_relat_1(k5_relat_1(A_32, B_33)) | ~v1_relat_1(B_33) | ~v1_relat_1(A_32))), inference(cnfTransformation, [status(thm)], [f_47])).
% 46.32/35.74  tff(c_156, plain, (![A_87, B_86]: (v1_relat_1(k8_relat_1(A_87, B_86)) | ~v1_relat_1(k6_relat_1(A_87)) | ~v1_relat_1(B_86) | ~v1_relat_1(B_86))), inference(superposition, [status(thm), theory('equality')], [c_146, c_18])).
% 46.32/35.74  tff(c_184, plain, (![A_87, B_86]: (v1_relat_1(k8_relat_1(A_87, B_86)) | ~v1_relat_1(B_86))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_156])).
% 46.32/35.74  tff(c_376, plain, (![A_109, A_110]: (v1_relat_1(k7_relat_1(k6_relat_1(A_109), A_110)) | ~v1_relat_1(k6_relat_1(A_110)))), inference(superposition, [status(thm), theory('equality')], [c_366, c_184])).
% 46.32/35.74  tff(c_386, plain, (![A_109, A_110]: (v1_relat_1(k7_relat_1(k6_relat_1(A_109), A_110)))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_376])).
% 46.32/35.74  tff(c_32, plain, (![A_55]: (k1_relat_1(k6_relat_1(A_55))=A_55)), inference(cnfTransformation, [status(thm)], [f_88])).
% 46.32/35.74  tff(c_34, plain, (![A_55]: (k2_relat_1(k6_relat_1(A_55))=A_55)), inference(cnfTransformation, [status(thm)], [f_88])).
% 46.32/35.74  tff(c_44, plain, (![A_62]: (k5_relat_1(A_62, k6_relat_1(k2_relat_1(A_62)))=A_62 | ~v1_relat_1(A_62))), inference(cnfTransformation, [status(thm)], [f_110])).
% 46.32/35.74  tff(c_246, plain, (![A_96]: (k7_relat_1(k6_relat_1(k2_relat_1(k6_relat_1(A_96))), A_96)=k6_relat_1(A_96) | ~v1_relat_1(k6_relat_1(A_96)) | ~v1_relat_1(k6_relat_1(k2_relat_1(k6_relat_1(A_96)))))), inference(superposition, [status(thm), theory('equality')], [c_222, c_44])).
% 46.32/35.74  tff(c_275, plain, (![A_96]: (k7_relat_1(k6_relat_1(A_96), A_96)=k6_relat_1(A_96))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_20, c_34, c_246])).
% 46.32/35.74  tff(c_301, plain, (![B_101, A_102]: (k3_xboole_0(k1_relat_1(B_101), A_102)=k1_relat_1(k7_relat_1(B_101, A_102)) | ~v1_relat_1(B_101))), inference(cnfTransformation, [status(thm)], [f_114])).
% 46.32/35.74  tff(c_313, plain, (![A_55, A_102]: (k1_relat_1(k7_relat_1(k6_relat_1(A_55), A_102))=k3_xboole_0(A_55, A_102) | ~v1_relat_1(k6_relat_1(A_55)))), inference(superposition, [status(thm), theory('equality')], [c_32, c_301])).
% 46.32/35.74  tff(c_325, plain, (![A_105, A_106]: (k1_relat_1(k7_relat_1(k6_relat_1(A_105), A_106))=k3_xboole_0(A_105, A_106))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_313])).
% 46.32/35.74  tff(c_337, plain, (![A_96]: (k3_xboole_0(A_96, A_96)=k1_relat_1(k6_relat_1(A_96)))), inference(superposition, [status(thm), theory('equality')], [c_275, c_325])).
% 46.32/35.74  tff(c_340, plain, (![A_96]: (k3_xboole_0(A_96, A_96)=A_96)), inference(demodulation, [status(thm), theory('equality')], [c_32, c_337])).
% 46.32/35.74  tff(c_317, plain, (![A_55, A_102]: (k1_relat_1(k7_relat_1(k6_relat_1(A_55), A_102))=k3_xboole_0(A_55, A_102))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_313])).
% 46.32/35.74  tff(c_267, plain, (![A_39, A_96]: (k8_relat_1(A_39, k6_relat_1(A_96))=k7_relat_1(k6_relat_1(A_39), A_96))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_20, c_229])).
% 46.32/35.74  tff(c_90, plain, (![A_78]: (k5_relat_1(A_78, k6_relat_1(k2_relat_1(A_78)))=A_78 | ~v1_relat_1(A_78))), inference(cnfTransformation, [status(thm)], [f_110])).
% 46.32/35.74  tff(c_102, plain, (![A_55]: (k5_relat_1(k6_relat_1(A_55), k6_relat_1(A_55))=k6_relat_1(A_55) | ~v1_relat_1(k6_relat_1(A_55)))), inference(superposition, [status(thm), theory('equality')], [c_34, c_90])).
% 46.32/35.74  tff(c_106, plain, (![A_55]: (k5_relat_1(k6_relat_1(A_55), k6_relat_1(A_55))=k6_relat_1(A_55))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_102])).
% 46.32/35.74  tff(c_1444, plain, (![A_169, B_170, C_171]: (k8_relat_1(A_169, k5_relat_1(B_170, C_171))=k5_relat_1(B_170, k8_relat_1(A_169, C_171)) | ~v1_relat_1(C_171) | ~v1_relat_1(B_170))), inference(cnfTransformation, [status(thm)], [f_67])).
% 46.32/35.74  tff(c_1485, plain, (![A_55, A_169]: (k5_relat_1(k6_relat_1(A_55), k8_relat_1(A_169, k6_relat_1(A_55)))=k8_relat_1(A_169, k6_relat_1(A_55)) | ~v1_relat_1(k6_relat_1(A_55)) | ~v1_relat_1(k6_relat_1(A_55)))), inference(superposition, [status(thm), theory('equality')], [c_106, c_1444])).
% 46.32/35.74  tff(c_2179, plain, (![A_212, A_213]: (k5_relat_1(k6_relat_1(A_212), k7_relat_1(k6_relat_1(A_213), A_212))=k7_relat_1(k6_relat_1(A_213), A_212))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_20, c_267, c_267, c_1485])).
% 46.32/35.74  tff(c_48, plain, (![A_65, B_66]: (k5_relat_1(k6_relat_1(A_65), B_66)=k7_relat_1(B_66, A_65) | ~v1_relat_1(B_66))), inference(cnfTransformation, [status(thm)], [f_118])).
% 46.32/35.74  tff(c_2197, plain, (![A_213, A_212]: (k7_relat_1(k7_relat_1(k6_relat_1(A_213), A_212), A_212)=k7_relat_1(k6_relat_1(A_213), A_212) | ~v1_relat_1(k7_relat_1(k6_relat_1(A_213), A_212)))), inference(superposition, [status(thm), theory('equality')], [c_2179, c_48])).
% 46.32/35.74  tff(c_2234, plain, (![A_213, A_212]: (k7_relat_1(k7_relat_1(k6_relat_1(A_213), A_212), A_212)=k7_relat_1(k6_relat_1(A_213), A_212))), inference(demodulation, [status(thm), theory('equality')], [c_386, c_2197])).
% 46.32/35.74  tff(c_46, plain, (![B_64, A_63]: (k3_xboole_0(k1_relat_1(B_64), A_63)=k1_relat_1(k7_relat_1(B_64, A_63)) | ~v1_relat_1(B_64))), inference(cnfTransformation, [status(thm)], [f_114])).
% 46.32/35.74  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(k3_xboole_0(A_1, B_2), A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 46.32/35.74  tff(c_393, plain, (![A_113, B_114]: (k5_relat_1(k6_relat_1(A_113), B_114)=B_114 | ~r1_tarski(k1_relat_1(B_114), A_113) | ~v1_relat_1(B_114))), inference(cnfTransformation, [status(thm)], [f_100])).
% 46.32/35.74  tff(c_403, plain, (![A_113, A_55]: (k5_relat_1(k6_relat_1(A_113), k6_relat_1(A_55))=k6_relat_1(A_55) | ~r1_tarski(A_55, A_113) | ~v1_relat_1(k6_relat_1(A_55)))), inference(superposition, [status(thm), theory('equality')], [c_32, c_393])).
% 46.32/35.74  tff(c_1147, plain, (![A_161, A_162]: (k5_relat_1(k6_relat_1(A_161), k6_relat_1(A_162))=k6_relat_1(A_162) | ~r1_tarski(A_162, A_161))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_403])).
% 46.32/35.74  tff(c_1210, plain, (![A_39, A_161]: (k8_relat_1(A_39, k6_relat_1(A_161))=k6_relat_1(A_39) | ~r1_tarski(A_39, A_161) | ~v1_relat_1(k6_relat_1(A_161)))), inference(superposition, [status(thm), theory('equality')], [c_24, c_1147])).
% 46.32/35.74  tff(c_1257, plain, (![A_163, A_164]: (k7_relat_1(k6_relat_1(A_163), A_164)=k6_relat_1(A_163) | ~r1_tarski(A_163, A_164))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_267, c_1210])).
% 46.32/35.74  tff(c_1291, plain, (![A_163, A_164]: (k3_xboole_0(A_163, A_164)=k1_relat_1(k6_relat_1(A_163)) | ~r1_tarski(A_163, A_164))), inference(superposition, [status(thm), theory('equality')], [c_1257, c_317])).
% 46.32/35.74  tff(c_1346, plain, (![A_165, A_166]: (k3_xboole_0(A_165, A_166)=A_165 | ~r1_tarski(A_165, A_166))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_1291])).
% 46.32/35.74  tff(c_1408, plain, (![A_167, B_168]: (k3_xboole_0(k3_xboole_0(A_167, B_168), A_167)=k3_xboole_0(A_167, B_168))), inference(resolution, [status(thm)], [c_2, c_1346])).
% 46.32/35.74  tff(c_22654, plain, (![B_660, A_661]: (k3_xboole_0(k1_relat_1(k7_relat_1(B_660, A_661)), k1_relat_1(B_660))=k3_xboole_0(k1_relat_1(B_660), A_661) | ~v1_relat_1(B_660))), inference(superposition, [status(thm), theory('equality')], [c_46, c_1408])).
% 46.32/35.74  tff(c_22820, plain, (![A_213, A_212]: (k3_xboole_0(k1_relat_1(k7_relat_1(k6_relat_1(A_213), A_212)), k1_relat_1(k7_relat_1(k6_relat_1(A_213), A_212)))=k3_xboole_0(k1_relat_1(k7_relat_1(k6_relat_1(A_213), A_212)), A_212) | ~v1_relat_1(k7_relat_1(k6_relat_1(A_213), A_212)))), inference(superposition, [status(thm), theory('equality')], [c_2234, c_22654])).
% 46.32/35.74  tff(c_22861, plain, (![A_213, A_212]: (k3_xboole_0(k3_xboole_0(A_213, A_212), A_212)=k3_xboole_0(A_213, A_212))), inference(demodulation, [status(thm), theory('equality')], [c_386, c_340, c_317, c_317, c_317, c_22820])).
% 46.32/35.74  tff(c_515, plain, (![B_124, A_125]: (r1_tarski(k1_relat_1(k7_relat_1(B_124, A_125)), k1_relat_1(B_124)) | ~v1_relat_1(B_124))), inference(superposition, [status(thm), theory('equality')], [c_301, c_2])).
% 46.32/35.74  tff(c_40, plain, (![A_58, B_59]: (k5_relat_1(k6_relat_1(A_58), B_59)=B_59 | ~r1_tarski(k1_relat_1(B_59), A_58) | ~v1_relat_1(B_59))), inference(cnfTransformation, [status(thm)], [f_100])).
% 46.32/35.74  tff(c_156784, plain, (![B_1649, A_1650]: (k5_relat_1(k6_relat_1(k1_relat_1(B_1649)), k7_relat_1(B_1649, A_1650))=k7_relat_1(B_1649, A_1650) | ~v1_relat_1(k7_relat_1(B_1649, A_1650)) | ~v1_relat_1(B_1649))), inference(resolution, [status(thm)], [c_515, c_40])).
% 46.32/35.74  tff(c_1482, plain, (![B_40, A_169, A_39]: (k5_relat_1(B_40, k8_relat_1(A_169, k6_relat_1(A_39)))=k8_relat_1(A_169, k8_relat_1(A_39, B_40)) | ~v1_relat_1(k6_relat_1(A_39)) | ~v1_relat_1(B_40) | ~v1_relat_1(B_40))), inference(superposition, [status(thm), theory('equality')], [c_24, c_1444])).
% 46.32/35.74  tff(c_5822, plain, (![B_303, A_304, A_305]: (k5_relat_1(B_303, k7_relat_1(k6_relat_1(A_304), A_305))=k8_relat_1(A_304, k8_relat_1(A_305, B_303)) | ~v1_relat_1(B_303))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_267, c_1482])).
% 46.32/35.74  tff(c_5869, plain, (![A_304, A_305, A_65]: (k8_relat_1(A_304, k8_relat_1(A_305, k6_relat_1(A_65)))=k7_relat_1(k7_relat_1(k6_relat_1(A_304), A_305), A_65) | ~v1_relat_1(k7_relat_1(k6_relat_1(A_304), A_305)) | ~v1_relat_1(k6_relat_1(A_65)))), inference(superposition, [status(thm), theory('equality')], [c_5822, c_48])).
% 46.32/35.74  tff(c_5943, plain, (![A_304, A_305, A_65]: (k8_relat_1(A_304, k7_relat_1(k6_relat_1(A_305), A_65))=k7_relat_1(k7_relat_1(k6_relat_1(A_304), A_305), A_65))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_386, c_267, c_5869])).
% 46.32/35.74  tff(c_1479, plain, (![A_65, A_169, B_66]: (k5_relat_1(k6_relat_1(A_65), k8_relat_1(A_169, B_66))=k8_relat_1(A_169, k7_relat_1(B_66, A_65)) | ~v1_relat_1(B_66) | ~v1_relat_1(k6_relat_1(A_65)) | ~v1_relat_1(B_66))), inference(superposition, [status(thm), theory('equality')], [c_48, c_1444])).
% 46.32/35.74  tff(c_3396, plain, (![A_243, A_244, B_245]: (k5_relat_1(k6_relat_1(A_243), k8_relat_1(A_244, B_245))=k8_relat_1(A_244, k7_relat_1(B_245, A_243)) | ~v1_relat_1(B_245))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_1479])).
% 46.32/35.74  tff(c_3446, plain, (![A_243, A_39, A_96]: (k5_relat_1(k6_relat_1(A_243), k7_relat_1(k6_relat_1(A_39), A_96))=k8_relat_1(A_39, k7_relat_1(k6_relat_1(A_96), A_243)) | ~v1_relat_1(k6_relat_1(A_96)))), inference(superposition, [status(thm), theory('equality')], [c_267, c_3396])).
% 46.32/35.74  tff(c_3469, plain, (![A_243, A_39, A_96]: (k5_relat_1(k6_relat_1(A_243), k7_relat_1(k6_relat_1(A_39), A_96))=k8_relat_1(A_39, k7_relat_1(k6_relat_1(A_96), A_243)))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_3446])).
% 46.32/35.74  tff(c_40778, plain, (![A_243, A_39, A_96]: (k5_relat_1(k6_relat_1(A_243), k7_relat_1(k6_relat_1(A_39), A_96))=k7_relat_1(k7_relat_1(k6_relat_1(A_39), A_96), A_243))), inference(demodulation, [status(thm), theory('equality')], [c_5943, c_3469])).
% 46.32/35.74  tff(c_156859, plain, (![A_39, A_1650]: (k7_relat_1(k7_relat_1(k6_relat_1(A_39), A_1650), k1_relat_1(k6_relat_1(A_39)))=k7_relat_1(k6_relat_1(A_39), A_1650) | ~v1_relat_1(k7_relat_1(k6_relat_1(A_39), A_1650)) | ~v1_relat_1(k6_relat_1(A_39)))), inference(superposition, [status(thm), theory('equality')], [c_156784, c_40778])).
% 46.32/35.74  tff(c_157189, plain, (![A_1651, A_1652]: (k7_relat_1(k7_relat_1(k6_relat_1(A_1651), A_1652), A_1651)=k7_relat_1(k6_relat_1(A_1651), A_1652))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_386, c_32, c_156859])).
% 46.32/35.74  tff(c_1084, plain, (![B_158, C_159, A_160]: (k7_relat_1(k5_relat_1(B_158, C_159), A_160)=k5_relat_1(k7_relat_1(B_158, A_160), C_159) | ~v1_relat_1(C_159) | ~v1_relat_1(B_158))), inference(cnfTransformation, [status(thm)], [f_56])).
% 46.32/35.74  tff(c_1123, plain, (![A_65, A_160, B_66]: (k5_relat_1(k7_relat_1(k6_relat_1(A_65), A_160), B_66)=k7_relat_1(k7_relat_1(B_66, A_65), A_160) | ~v1_relat_1(B_66) | ~v1_relat_1(k6_relat_1(A_65)) | ~v1_relat_1(B_66))), inference(superposition, [status(thm), theory('equality')], [c_48, c_1084])).
% 46.32/35.74  tff(c_4917, plain, (![A_274, A_275, B_276]: (k5_relat_1(k7_relat_1(k6_relat_1(A_274), A_275), B_276)=k7_relat_1(k7_relat_1(B_276, A_274), A_275) | ~v1_relat_1(B_276))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_1123])).
% 46.32/35.74  tff(c_38, plain, (![B_57, A_56]: (r1_tarski(k5_relat_1(B_57, k6_relat_1(A_56)), B_57) | ~v1_relat_1(B_57))), inference(cnfTransformation, [status(thm)], [f_94])).
% 46.32/35.74  tff(c_4971, plain, (![A_56, A_274, A_275]: (r1_tarski(k7_relat_1(k7_relat_1(k6_relat_1(A_56), A_274), A_275), k7_relat_1(k6_relat_1(A_274), A_275)) | ~v1_relat_1(k7_relat_1(k6_relat_1(A_274), A_275)) | ~v1_relat_1(k6_relat_1(A_56)))), inference(superposition, [status(thm), theory('equality')], [c_4917, c_38])).
% 46.32/35.74  tff(c_5045, plain, (![A_56, A_274, A_275]: (r1_tarski(k7_relat_1(k7_relat_1(k6_relat_1(A_56), A_274), A_275), k7_relat_1(k6_relat_1(A_274), A_275)))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_386, c_4971])).
% 46.32/35.74  tff(c_157528, plain, (![A_1651, A_1652]: (r1_tarski(k7_relat_1(k6_relat_1(A_1651), A_1652), k7_relat_1(k6_relat_1(A_1652), A_1651)))), inference(superposition, [status(thm), theory('equality')], [c_157189, c_5045])).
% 46.32/35.74  tff(c_157956, plain, (![A_1653, A_1654]: (r1_tarski(k7_relat_1(k6_relat_1(A_1653), A_1654), k7_relat_1(k6_relat_1(A_1654), A_1653)))), inference(superposition, [status(thm), theory('equality')], [c_157189, c_5045])).
% 46.32/35.74  tff(c_639, plain, (![B_139, A_140]: (k5_relat_1(B_139, k6_relat_1(A_140))=B_139 | ~r1_tarski(k2_relat_1(B_139), A_140) | ~v1_relat_1(B_139))), inference(cnfTransformation, [status(thm)], [f_106])).
% 46.32/35.74  tff(c_661, plain, (![A_55, A_140]: (k5_relat_1(k6_relat_1(A_55), k6_relat_1(A_140))=k6_relat_1(A_55) | ~r1_tarski(A_55, A_140) | ~v1_relat_1(k6_relat_1(A_55)))), inference(superposition, [status(thm), theory('equality')], [c_34, c_639])).
% 46.32/35.74  tff(c_805, plain, (![A_148, A_149]: (k5_relat_1(k6_relat_1(A_148), k6_relat_1(A_149))=k6_relat_1(A_148) | ~r1_tarski(A_148, A_149))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_661])).
% 46.32/35.74  tff(c_859, plain, (![A_39, A_148]: (k8_relat_1(A_39, k6_relat_1(A_148))=k6_relat_1(A_148) | ~r1_tarski(A_148, A_39) | ~v1_relat_1(k6_relat_1(A_148)))), inference(superposition, [status(thm), theory('equality')], [c_24, c_805])).
% 46.32/35.74  tff(c_896, plain, (![A_39, A_148]: (k7_relat_1(k6_relat_1(A_39), A_148)=k6_relat_1(A_148) | ~r1_tarski(A_148, A_39))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_267, c_859])).
% 46.32/35.74  tff(c_468, plain, (![A_118, B_119]: (r1_tarski(k2_relat_1(k5_relat_1(A_118, B_119)), k2_relat_1(B_119)) | ~v1_relat_1(B_119) | ~v1_relat_1(A_118))), inference(cnfTransformation, [status(thm)], [f_74])).
% 46.32/35.74  tff(c_477, plain, (![A_39, B_40]: (r1_tarski(k2_relat_1(k8_relat_1(A_39, B_40)), k2_relat_1(k6_relat_1(A_39))) | ~v1_relat_1(k6_relat_1(A_39)) | ~v1_relat_1(B_40) | ~v1_relat_1(B_40))), inference(superposition, [status(thm), theory('equality')], [c_24, c_468])).
% 46.32/35.74  tff(c_499, plain, (![A_120, B_121]: (r1_tarski(k2_relat_1(k8_relat_1(A_120, B_121)), A_120) | ~v1_relat_1(B_121))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_34, c_477])).
% 46.32/35.74  tff(c_502, plain, (![A_39, A_96]: (r1_tarski(k2_relat_1(k7_relat_1(k6_relat_1(A_39), A_96)), A_39) | ~v1_relat_1(k6_relat_1(A_96)))), inference(superposition, [status(thm), theory('equality')], [c_267, c_499])).
% 46.32/35.74  tff(c_507, plain, (![A_39, A_96]: (r1_tarski(k2_relat_1(k7_relat_1(k6_relat_1(A_39), A_96)), A_39))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_502])).
% 46.32/35.74  tff(c_1250, plain, (![A_39, A_161]: (k7_relat_1(k6_relat_1(A_39), A_161)=k6_relat_1(A_39) | ~r1_tarski(A_39, A_161))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_267, c_1210])).
% 46.32/35.74  tff(c_5016, plain, (![A_274, A_275]: (k7_relat_1(k7_relat_1(k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(A_274), A_275))), A_274), A_275)=k7_relat_1(k6_relat_1(A_274), A_275) | ~v1_relat_1(k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(A_274), A_275)))) | ~v1_relat_1(k7_relat_1(k6_relat_1(A_274), A_275)))), inference(superposition, [status(thm), theory('equality')], [c_44, c_4917])).
% 46.32/35.74  tff(c_46461, plain, (![A_939, A_940]: (k7_relat_1(k7_relat_1(k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(A_939), A_940))), A_939), A_940)=k7_relat_1(k6_relat_1(A_939), A_940))), inference(demodulation, [status(thm), theory('equality')], [c_386, c_20, c_5016])).
% 46.32/35.74  tff(c_524, plain, (![A_55, A_102, A_125]: (r1_tarski(k1_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(A_55), A_102), A_125)), k3_xboole_0(A_55, A_102)) | ~v1_relat_1(k7_relat_1(k6_relat_1(A_55), A_102)))), inference(superposition, [status(thm), theory('equality')], [c_317, c_515])).
% 46.32/35.74  tff(c_535, plain, (![A_55, A_102, A_125]: (r1_tarski(k1_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(A_55), A_102), A_125)), k3_xboole_0(A_55, A_102)))), inference(demodulation, [status(thm), theory('equality')], [c_386, c_524])).
% 46.32/35.74  tff(c_486, plain, (![A_118, A_55]: (r1_tarski(k2_relat_1(k5_relat_1(A_118, k6_relat_1(A_55))), A_55) | ~v1_relat_1(k6_relat_1(A_55)) | ~v1_relat_1(A_118))), inference(superposition, [status(thm), theory('equality')], [c_34, c_468])).
% 46.32/35.74  tff(c_498, plain, (![A_118, A_55]: (r1_tarski(k2_relat_1(k5_relat_1(A_118, k6_relat_1(A_55))), A_55) | ~v1_relat_1(A_118))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_486])).
% 46.32/35.74  tff(c_4953, plain, (![A_55, A_274, A_275]: (r1_tarski(k2_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(A_55), A_274), A_275)), A_55) | ~v1_relat_1(k7_relat_1(k6_relat_1(A_274), A_275)) | ~v1_relat_1(k6_relat_1(A_55)))), inference(superposition, [status(thm), theory('equality')], [c_4917, c_498])).
% 46.32/35.74  tff(c_5128, plain, (![A_283, A_284, A_285]: (r1_tarski(k2_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(A_283), A_284), A_285)), A_283))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_386, c_4953])).
% 46.32/35.74  tff(c_5332, plain, (![A_288, A_289, A_290]: (r1_tarski(k2_relat_1(k7_relat_1(k6_relat_1(A_288), A_289)), A_290) | ~r1_tarski(A_288, A_290))), inference(superposition, [status(thm), theory('equality')], [c_896, c_5128])).
% 46.32/35.74  tff(c_5363, plain, (![A_148, A_290, A_39]: (r1_tarski(k2_relat_1(k6_relat_1(A_148)), A_290) | ~r1_tarski(A_39, A_290) | ~r1_tarski(A_148, A_39))), inference(superposition, [status(thm), theory('equality')], [c_896, c_5332])).
% 46.32/35.74  tff(c_5384, plain, (![A_291, A_292, A_293]: (r1_tarski(A_291, A_292) | ~r1_tarski(A_293, A_292) | ~r1_tarski(A_291, A_293))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_5363])).
% 46.32/35.74  tff(c_5451, plain, (![A_294, A_295, B_296]: (r1_tarski(A_294, A_295) | ~r1_tarski(A_294, k3_xboole_0(A_295, B_296)))), inference(resolution, [status(thm)], [c_2, c_5384])).
% 46.32/35.74  tff(c_5582, plain, (![A_55, A_102, A_125]: (r1_tarski(k1_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(A_55), A_102), A_125)), A_55))), inference(resolution, [status(thm)], [c_535, c_5451])).
% 46.32/35.74  tff(c_46644, plain, (![A_939, A_940]: (r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1(A_939), A_940)), k2_relat_1(k7_relat_1(k6_relat_1(A_939), A_940))))), inference(superposition, [status(thm), theory('equality')], [c_46461, c_5582])).
% 46.32/35.74  tff(c_46866, plain, (![A_941, A_942]: (r1_tarski(k3_xboole_0(A_941, A_942), k2_relat_1(k7_relat_1(k6_relat_1(A_941), A_942))))), inference(demodulation, [status(thm), theory('equality')], [c_317, c_46644])).
% 46.32/35.74  tff(c_66282, plain, (![B_1125, A_1126]: (r1_tarski(k1_relat_1(k7_relat_1(B_1125, A_1126)), k2_relat_1(k7_relat_1(k6_relat_1(k1_relat_1(B_1125)), A_1126))) | ~v1_relat_1(B_1125))), inference(superposition, [status(thm), theory('equality')], [c_46, c_46866])).
% 46.32/35.74  tff(c_66344, plain, (![A_39, A_161]: (r1_tarski(k1_relat_1(k6_relat_1(A_39)), k2_relat_1(k7_relat_1(k6_relat_1(k1_relat_1(k6_relat_1(A_39))), A_161))) | ~v1_relat_1(k6_relat_1(A_39)) | ~r1_tarski(A_39, A_161))), inference(superposition, [status(thm), theory('equality')], [c_1250, c_66282])).
% 46.32/35.74  tff(c_66428, plain, (![A_1127, A_1128]: (r1_tarski(A_1127, k2_relat_1(k7_relat_1(k6_relat_1(A_1127), A_1128))) | ~r1_tarski(A_1127, A_1128))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_32, c_32, c_66344])).
% 46.32/35.74  tff(c_671, plain, (![A_55, A_140]: (k5_relat_1(k6_relat_1(A_55), k6_relat_1(A_140))=k6_relat_1(A_55) | ~r1_tarski(A_55, A_140))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_661])).
% 46.32/35.74  tff(c_1156, plain, (![A_162, A_161]: (k6_relat_1(A_162)=k6_relat_1(A_161) | ~r1_tarski(A_161, A_162) | ~r1_tarski(A_162, A_161))), inference(superposition, [status(thm), theory('equality')], [c_1147, c_671])).
% 46.32/35.74  tff(c_66455, plain, (![A_1127, A_1128]: (k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(A_1127), A_1128)))=k6_relat_1(A_1127) | ~r1_tarski(k2_relat_1(k7_relat_1(k6_relat_1(A_1127), A_1128)), A_1127) | ~r1_tarski(A_1127, A_1128))), inference(resolution, [status(thm)], [c_66428, c_1156])).
% 46.32/35.74  tff(c_66533, plain, (![A_1129, A_1130]: (k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(A_1129), A_1130)))=k6_relat_1(A_1129) | ~r1_tarski(A_1129, A_1130))), inference(demodulation, [status(thm), theory('equality')], [c_507, c_66455])).
% 46.32/35.74  tff(c_67381, plain, (![A_1129, A_1130]: (k2_relat_1(k7_relat_1(k6_relat_1(A_1129), A_1130))=k1_relat_1(k6_relat_1(A_1129)) | ~r1_tarski(A_1129, A_1130))), inference(superposition, [status(thm), theory('equality')], [c_66533, c_32])).
% 46.32/35.74  tff(c_67514, plain, (![A_1131, A_1132]: (k2_relat_1(k7_relat_1(k6_relat_1(A_1131), A_1132))=A_1131 | ~r1_tarski(A_1131, A_1132))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_67381])).
% 46.32/35.74  tff(c_67762, plain, (![A_148, A_39]: (k2_relat_1(k6_relat_1(A_148))=A_39 | ~r1_tarski(A_39, A_148) | ~r1_tarski(A_148, A_39))), inference(superposition, [status(thm), theory('equality')], [c_896, c_67514])).
% 46.32/35.74  tff(c_67860, plain, (![A_39, A_148]: (A_39=A_148 | ~r1_tarski(A_39, A_148) | ~r1_tarski(A_148, A_39))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_67762])).
% 46.32/35.74  tff(c_157970, plain, (![A_1654, A_1653]: (k7_relat_1(k6_relat_1(A_1654), A_1653)=k7_relat_1(k6_relat_1(A_1653), A_1654) | ~r1_tarski(k7_relat_1(k6_relat_1(A_1654), A_1653), k7_relat_1(k6_relat_1(A_1653), A_1654)))), inference(resolution, [status(thm)], [c_157956, c_67860])).
% 46.32/35.74  tff(c_158216, plain, (![A_1656, A_1655]: (k7_relat_1(k6_relat_1(A_1656), A_1655)=k7_relat_1(k6_relat_1(A_1655), A_1656))), inference(demodulation, [status(thm), theory('equality')], [c_157528, c_157970])).
% 46.32/35.74  tff(c_1435, plain, (![B_64, A_63]: (k3_xboole_0(k1_relat_1(k7_relat_1(B_64, A_63)), k1_relat_1(B_64))=k3_xboole_0(k1_relat_1(B_64), A_63) | ~v1_relat_1(B_64))), inference(superposition, [status(thm), theory('equality')], [c_46, c_1408])).
% 46.32/35.74  tff(c_159612, plain, (![A_1655, A_1656]: (k3_xboole_0(k1_relat_1(k7_relat_1(k6_relat_1(A_1655), A_1656)), k1_relat_1(k6_relat_1(A_1656)))=k3_xboole_0(k1_relat_1(k6_relat_1(A_1656)), A_1655) | ~v1_relat_1(k6_relat_1(A_1656)))), inference(superposition, [status(thm), theory('equality')], [c_158216, c_1435])).
% 46.32/35.74  tff(c_160652, plain, (![A_1656, A_1655]: (k3_xboole_0(A_1656, A_1655)=k3_xboole_0(A_1655, A_1656))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_22861, c_317, c_32, c_32, c_159612])).
% 46.32/35.74  tff(c_36, plain, (![A_56, B_57]: (r1_tarski(k5_relat_1(k6_relat_1(A_56), B_57), B_57) | ~v1_relat_1(B_57))), inference(cnfTransformation, [status(thm)], [f_94])).
% 46.32/35.74  tff(c_153, plain, (![A_87, A_56]: (r1_tarski(k8_relat_1(A_87, k6_relat_1(A_56)), k6_relat_1(A_87)) | ~v1_relat_1(k6_relat_1(A_87)) | ~v1_relat_1(k6_relat_1(A_56)))), inference(superposition, [status(thm), theory('equality')], [c_146, c_36])).
% 46.32/35.74  tff(c_182, plain, (![A_87, A_56]: (r1_tarski(k8_relat_1(A_87, k6_relat_1(A_56)), k6_relat_1(A_87)))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_20, c_153])).
% 46.32/35.74  tff(c_364, plain, (![A_87, A_56]: (r1_tarski(k7_relat_1(k6_relat_1(A_87), A_56), k6_relat_1(A_87)))), inference(demodulation, [status(thm), theory('equality')], [c_267, c_182])).
% 46.32/35.74  tff(c_904, plain, (![A_152, A_153]: (k7_relat_1(k6_relat_1(A_152), A_153)=k6_relat_1(A_153) | ~r1_tarski(A_153, A_152))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_267, c_859])).
% 46.32/35.74  tff(c_935, plain, (![A_152, A_153]: (k3_xboole_0(A_152, A_153)=k1_relat_1(k6_relat_1(A_153)) | ~r1_tarski(A_153, A_152))), inference(superposition, [status(thm), theory('equality')], [c_904, c_317])).
% 46.32/35.74  tff(c_986, plain, (![A_154, A_155]: (k3_xboole_0(A_154, A_155)=A_155 | ~r1_tarski(A_155, A_154))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_935])).
% 46.32/35.74  tff(c_4041, plain, (![A_256, A_257]: (k3_xboole_0(k6_relat_1(A_256), k7_relat_1(k6_relat_1(A_256), A_257))=k7_relat_1(k6_relat_1(A_256), A_257))), inference(resolution, [status(thm)], [c_364, c_986])).
% 46.32/35.74  tff(c_108120, plain, (![A_1428, A_1429]: (k3_xboole_0(k6_relat_1(A_1428), k6_relat_1(A_1429))=k7_relat_1(k6_relat_1(A_1428), A_1429) | ~r1_tarski(A_1429, A_1428))), inference(superposition, [status(thm), theory('equality')], [c_896, c_4041])).
% 46.32/35.74  tff(c_341, plain, (![A_107]: (k3_xboole_0(A_107, A_107)=A_107)), inference(demodulation, [status(thm), theory('equality')], [c_32, c_337])).
% 46.32/35.74  tff(c_351, plain, (![A_107]: (r1_tarski(A_107, A_107))), inference(superposition, [status(thm), theory('equality')], [c_341, c_2])).
% 46.32/35.74  tff(c_827, plain, (![A_148, A_149]: (r1_tarski(k6_relat_1(A_148), k6_relat_1(A_149)) | ~v1_relat_1(k6_relat_1(A_149)) | ~r1_tarski(A_148, A_149))), inference(superposition, [status(thm), theory('equality')], [c_805, c_36])).
% 46.32/35.74  tff(c_879, plain, (![A_148, A_149]: (r1_tarski(k6_relat_1(A_148), k6_relat_1(A_149)) | ~r1_tarski(A_148, A_149))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_827])).
% 46.32/35.74  tff(c_13558, plain, (![A_498, A_499, A_500]: (r1_tarski(A_498, k6_relat_1(A_499)) | ~r1_tarski(A_498, k6_relat_1(A_500)) | ~r1_tarski(A_500, A_499))), inference(resolution, [status(thm)], [c_879, c_5384])).
% 46.32/35.74  tff(c_14447, plain, (![A_514, A_515, A_516]: (r1_tarski(k6_relat_1(A_514), k6_relat_1(A_515)) | ~r1_tarski(A_516, A_515) | ~r1_tarski(A_514, A_516))), inference(resolution, [status(thm)], [c_879, c_13558])).
% 46.32/35.74  tff(c_14655, plain, (![A_517, A_518, B_519]: (r1_tarski(k6_relat_1(A_517), k6_relat_1(A_518)) | ~r1_tarski(A_517, k3_xboole_0(A_518, B_519)))), inference(resolution, [status(thm)], [c_2, c_14447])).
% 46.32/35.74  tff(c_14848, plain, (![A_520, B_521]: (r1_tarski(k6_relat_1(k3_xboole_0(A_520, B_521)), k6_relat_1(A_520)))), inference(resolution, [status(thm)], [c_351, c_14655])).
% 46.32/35.74  tff(c_972, plain, (![A_152, A_153]: (k3_xboole_0(A_152, A_153)=A_153 | ~r1_tarski(A_153, A_152))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_935])).
% 46.32/35.74  tff(c_14943, plain, (![A_520, B_521]: (k3_xboole_0(k6_relat_1(A_520), k6_relat_1(k3_xboole_0(A_520, B_521)))=k6_relat_1(k3_xboole_0(A_520, B_521)))), inference(resolution, [status(thm)], [c_14848, c_972])).
% 46.32/35.74  tff(c_108328, plain, (![A_1428, B_521]: (k7_relat_1(k6_relat_1(A_1428), k3_xboole_0(A_1428, B_521))=k6_relat_1(k3_xboole_0(A_1428, B_521)) | ~r1_tarski(k3_xboole_0(A_1428, B_521), A_1428))), inference(superposition, [status(thm), theory('equality')], [c_108120, c_14943])).
% 46.32/35.74  tff(c_108955, plain, (![A_1433, B_1434]: (k7_relat_1(k6_relat_1(A_1433), k3_xboole_0(A_1433, B_1434))=k6_relat_1(k3_xboole_0(A_1433, B_1434)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_108328])).
% 46.32/35.74  tff(c_3421, plain, (![A_244, B_245, A_243]: (r1_tarski(k8_relat_1(A_244, k7_relat_1(B_245, A_243)), k8_relat_1(A_244, B_245)) | ~v1_relat_1(k8_relat_1(A_244, B_245)) | ~v1_relat_1(B_245))), inference(superposition, [status(thm), theory('equality')], [c_3396, c_36])).
% 46.32/35.74  tff(c_109126, plain, (![A_244, A_1433, B_1434]: (r1_tarski(k8_relat_1(A_244, k6_relat_1(k3_xboole_0(A_1433, B_1434))), k8_relat_1(A_244, k6_relat_1(A_1433))) | ~v1_relat_1(k8_relat_1(A_244, k6_relat_1(A_1433))) | ~v1_relat_1(k6_relat_1(A_1433)))), inference(superposition, [status(thm), theory('equality')], [c_108955, c_3421])).
% 46.32/35.74  tff(c_111480, plain, (![A_1441, A_1442, B_1443]: (r1_tarski(k7_relat_1(k6_relat_1(A_1441), k3_xboole_0(A_1442, B_1443)), k7_relat_1(k6_relat_1(A_1441), A_1442)))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_386, c_267, c_267, c_267, c_109126])).
% 46.32/35.74  tff(c_112358, plain, (![A_1448, B_1449]: (r1_tarski(k6_relat_1(k3_xboole_0(A_1448, B_1449)), k7_relat_1(k6_relat_1(k3_xboole_0(A_1448, B_1449)), A_1448)))), inference(superposition, [status(thm), theory('equality')], [c_275, c_111480])).
% 46.32/35.74  tff(c_112365, plain, (![A_1448, B_1449]: (k7_relat_1(k6_relat_1(k3_xboole_0(A_1448, B_1449)), A_1448)=k6_relat_1(k3_xboole_0(A_1448, B_1449)) | ~r1_tarski(k7_relat_1(k6_relat_1(k3_xboole_0(A_1448, B_1449)), A_1448), k6_relat_1(k3_xboole_0(A_1448, B_1449))))), inference(resolution, [status(thm)], [c_112358, c_67860])).
% 46.32/35.74  tff(c_112752, plain, (![A_1448, B_1449]: (k7_relat_1(k6_relat_1(k3_xboole_0(A_1448, B_1449)), A_1448)=k6_relat_1(k3_xboole_0(A_1448, B_1449)))), inference(demodulation, [status(thm), theory('equality')], [c_364, c_112365])).
% 46.32/35.74  tff(c_46723, plain, (![A_161, A_940]: (k7_relat_1(k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(A_161), A_940))), A_940)=k7_relat_1(k6_relat_1(A_161), A_940) | ~r1_tarski(k2_relat_1(k7_relat_1(k6_relat_1(A_161), A_940)), A_161))), inference(superposition, [status(thm), theory('equality')], [c_1250, c_46461])).
% 46.32/35.74  tff(c_88388, plain, (![A_1262, A_1263]: (k7_relat_1(k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(A_1262), A_1263))), A_1263)=k7_relat_1(k6_relat_1(A_1262), A_1263))), inference(demodulation, [status(thm), theory('equality')], [c_507, c_46723])).
% 46.32/35.74  tff(c_88988, plain, (![A_1262, A_1263]: (k3_xboole_0(k2_relat_1(k7_relat_1(k6_relat_1(A_1262), A_1263)), A_1263)=k1_relat_1(k7_relat_1(k6_relat_1(A_1262), A_1263)))), inference(superposition, [status(thm), theory('equality')], [c_88388, c_317])).
% 46.32/35.74  tff(c_89278, plain, (![A_1262, A_1263]: (k3_xboole_0(k2_relat_1(k7_relat_1(k6_relat_1(A_1262), A_1263)), A_1263)=k3_xboole_0(A_1262, A_1263))), inference(demodulation, [status(thm), theory('equality')], [c_317, c_88988])).
% 46.32/35.74  tff(c_1398, plain, (![A_39, A_96]: (k3_xboole_0(k2_relat_1(k7_relat_1(k6_relat_1(A_39), A_96)), A_39)=k2_relat_1(k7_relat_1(k6_relat_1(A_39), A_96)))), inference(resolution, [status(thm)], [c_507, c_1346])).
% 46.32/35.74  tff(c_158572, plain, (![A_1655, A_1656]: (k3_xboole_0(k2_relat_1(k7_relat_1(k6_relat_1(A_1655), A_1656)), A_1656)=k2_relat_1(k7_relat_1(k6_relat_1(A_1656), A_1655)))), inference(superposition, [status(thm), theory('equality')], [c_158216, c_1398])).
% 46.32/35.74  tff(c_160376, plain, (![A_1656, A_1655]: (k2_relat_1(k7_relat_1(k6_relat_1(A_1656), A_1655))=k3_xboole_0(A_1655, A_1656))), inference(demodulation, [status(thm), theory('equality')], [c_89278, c_158572])).
% 46.32/35.74  tff(c_46860, plain, (![A_161, A_940]: (k7_relat_1(k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(A_161), A_940))), A_940)=k7_relat_1(k6_relat_1(A_161), A_940))), inference(demodulation, [status(thm), theory('equality')], [c_507, c_46723])).
% 46.32/35.74  tff(c_173340, plain, (![A_940, A_161]: (k7_relat_1(k6_relat_1(k3_xboole_0(A_940, A_161)), A_940)=k7_relat_1(k6_relat_1(A_161), A_940))), inference(demodulation, [status(thm), theory('equality')], [c_160376, c_46860])).
% 46.32/35.74  tff(c_173374, plain, (![A_161, A_940]: (k7_relat_1(k6_relat_1(A_161), A_940)=k6_relat_1(k3_xboole_0(A_940, A_161)))), inference(demodulation, [status(thm), theory('equality')], [c_112752, c_173340])).
% 46.32/35.74  tff(c_50, plain, (k5_relat_1(k6_relat_1('#skF_2'), k6_relat_1('#skF_1'))!=k6_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_121])).
% 46.32/35.74  tff(c_242, plain, (k7_relat_1(k6_relat_1('#skF_1'), '#skF_2')!=k6_relat_1(k3_xboole_0('#skF_1', '#skF_2')) | ~v1_relat_1(k6_relat_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_222, c_50])).
% 46.32/35.74  tff(c_273, plain, (k7_relat_1(k6_relat_1('#skF_1'), '#skF_2')!=k6_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_242])).
% 46.32/35.74  tff(c_173853, plain, (k6_relat_1(k3_xboole_0('#skF_2', '#skF_1'))!=k6_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_173374, c_273])).
% 46.32/35.74  tff(c_173895, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_160652, c_173853])).
% 46.32/35.74  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 46.32/35.74  
% 46.32/35.74  Inference rules
% 46.32/35.74  ----------------------
% 46.32/35.74  #Ref     : 0
% 46.32/35.74  #Sup     : 44947
% 46.32/35.74  #Fact    : 0
% 46.32/35.74  #Define  : 0
% 46.32/35.74  #Split   : 2
% 46.32/35.74  #Chain   : 0
% 46.32/35.74  #Close   : 0
% 46.32/35.74  
% 46.32/35.74  Ordering : KBO
% 46.32/35.74  
% 46.32/35.74  Simplification rules
% 46.32/35.74  ----------------------
% 46.32/35.74  #Subsume      : 6348
% 46.32/35.74  #Demod        : 32577
% 46.32/35.74  #Tautology    : 12573
% 46.32/35.74  #SimpNegUnit  : 0
% 46.32/35.74  #BackRed      : 280
% 46.32/35.74  
% 46.32/35.74  #Partial instantiations: 0
% 46.32/35.74  #Strategies tried      : 1
% 46.32/35.74  
% 46.32/35.74  Timing (in seconds)
% 46.32/35.74  ----------------------
% 46.32/35.74  Preprocessing        : 0.38
% 46.32/35.74  Parsing              : 0.21
% 46.32/35.74  CNF conversion       : 0.03
% 46.32/35.74  Main loop            : 34.48
% 46.32/35.74  Inferencing          : 3.57
% 46.32/35.74  Reduction            : 14.69
% 46.32/35.74  Demodulation         : 12.95
% 46.32/35.74  BG Simplification    : 0.55
% 46.32/35.74  Subsumption          : 14.15
% 46.32/35.74  Abstraction          : 0.82
% 46.32/35.74  MUC search           : 0.00
% 46.32/35.74  Cooper               : 0.00
% 46.32/35.74  Total                : 34.93
% 46.32/35.74  Index Insertion      : 0.00
% 46.32/35.74  Index Deletion       : 0.00
% 46.32/35.74  Index Matching       : 0.00
% 46.32/35.74  BG Taut test         : 0.00
%------------------------------------------------------------------------------

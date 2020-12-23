%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:04:45 EST 2020

% Result     : Theorem 11.27s
% Output     : CNFRefutation 11.27s
% Verified   : 
% Statistics : Number of formulae       :  113 ( 626 expanded)
%              Number of leaves         :   46 ( 235 expanded)
%              Depth                    :   20
%              Number of atoms          :  156 (1050 expanded)
%              Number of equality atoms :   62 ( 386 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k5_xboole_0 > k5_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

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

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_37,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_126,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( r1_tarski(A,k1_relat_1(B))
         => r1_tarski(A,k10_relat_1(B,k9_relat_1(B,A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_funct_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_39,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_73,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_115,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k5_relat_1(k6_relat_1(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).

tff(f_69,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_107,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_92,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k10_relat_1(A,k2_relat_1(A)) = k1_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).

tff(f_96,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k10_relat_1(C,k2_xboole_0(A,B)) = k2_xboole_0(k10_relat_1(C,A),k10_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t175_relat_1)).

tff(f_49,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_88,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k10_relat_1(B,A),k1_relat_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t167_relat_1)).

tff(f_103,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k1_relat_1(k5_relat_1(A,B)) = k10_relat_1(A,k1_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t182_relat_1)).

tff(f_111,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k1_relat_1(k7_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_relat_1)).

tff(f_77,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k9_relat_1(A,k1_relat_1(A)) = k2_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).

tff(f_84,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B,C] :
          ( r1_tarski(B,C)
         => k9_relat_1(k7_relat_1(A,C),B) = k9_relat_1(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t162_relat_1)).

tff(f_119,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k10_relat_1(k7_relat_1(C,A),B) = k3_xboole_0(A,k10_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t139_funct_1)).

tff(c_101,plain,(
    ! [A_83,B_84] :
      ( r1_tarski(A_83,B_84)
      | k4_xboole_0(A_83,B_84) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_64,plain,(
    ~ r1_tarski('#skF_1',k10_relat_1('#skF_2',k9_relat_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_105,plain,(
    k4_xboole_0('#skF_1',k10_relat_1('#skF_2',k9_relat_1('#skF_2','#skF_1'))) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_101,c_64])).

tff(c_68,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_8,plain,(
    ! [B_4] : r1_tarski(B_4,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_162,plain,(
    ! [A_92,B_93] :
      ( k4_xboole_0(A_92,B_93) = k1_xboole_0
      | ~ r1_tarski(A_92,B_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_178,plain,(
    ! [B_4] : k4_xboole_0(B_4,B_4) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_8,c_162])).

tff(c_2,plain,(
    ! [A_1] : k3_xboole_0(A_1,A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_249,plain,(
    ! [A_101,B_102] : k5_xboole_0(A_101,k3_xboole_0(A_101,B_102)) = k4_xboole_0(A_101,B_102) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_258,plain,(
    ! [A_1] : k5_xboole_0(A_1,A_1) = k4_xboole_0(A_1,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_249])).

tff(c_261,plain,(
    ! [A_1] : k5_xboole_0(A_1,A_1) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_178,c_258])).

tff(c_40,plain,(
    ! [A_49,B_50] :
      ( v1_relat_1(k7_relat_1(A_49,B_50))
      | ~ v1_relat_1(A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_60,plain,(
    ! [A_69,B_70] :
      ( k5_relat_1(k6_relat_1(A_69),B_70) = k7_relat_1(B_70,A_69)
      | ~ v1_relat_1(B_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_38,plain,(
    ! [A_48] : v1_relat_1(k6_relat_1(A_48)) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_66,plain,(
    r1_tarski('#skF_1',k1_relat_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_106,plain,(
    ! [A_85,B_86] :
      ( k2_xboole_0(A_85,B_86) = B_86
      | ~ r1_tarski(A_85,B_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_121,plain,(
    k2_xboole_0('#skF_1',k1_relat_1('#skF_2')) = k1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_66,c_106])).

tff(c_54,plain,(
    ! [A_66] : k1_relat_1(k6_relat_1(A_66)) = A_66 ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_56,plain,(
    ! [A_66] : k2_relat_1(k6_relat_1(A_66)) = A_66 ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_226,plain,(
    ! [A_99] :
      ( k10_relat_1(A_99,k2_relat_1(A_99)) = k1_relat_1(A_99)
      | ~ v1_relat_1(A_99) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_235,plain,(
    ! [A_66] :
      ( k10_relat_1(k6_relat_1(A_66),A_66) = k1_relat_1(k6_relat_1(A_66))
      | ~ v1_relat_1(k6_relat_1(A_66)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_226])).

tff(c_239,plain,(
    ! [A_66] : k10_relat_1(k6_relat_1(A_66),A_66) = A_66 ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_54,c_235])).

tff(c_3091,plain,(
    ! [C_222,A_223,B_224] :
      ( k2_xboole_0(k10_relat_1(C_222,A_223),k10_relat_1(C_222,B_224)) = k10_relat_1(C_222,k2_xboole_0(A_223,B_224))
      | ~ v1_relat_1(C_222) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_20,plain,(
    ! [A_14,B_15] : r1_tarski(A_14,k2_xboole_0(A_14,B_15)) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_3576,plain,(
    ! [C_232,A_233,B_234] :
      ( r1_tarski(k10_relat_1(C_232,A_233),k10_relat_1(C_232,k2_xboole_0(A_233,B_234)))
      | ~ v1_relat_1(C_232) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3091,c_20])).

tff(c_3651,plain,(
    ! [A_66,B_234] :
      ( r1_tarski(A_66,k10_relat_1(k6_relat_1(A_66),k2_xboole_0(A_66,B_234)))
      | ~ v1_relat_1(k6_relat_1(A_66)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_239,c_3576])).

tff(c_3688,plain,(
    ! [A_235,B_236] : r1_tarski(A_235,k10_relat_1(k6_relat_1(A_235),k2_xboole_0(A_235,B_236))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_3651])).

tff(c_292,plain,(
    ! [B_106,A_107] :
      ( r1_tarski(k10_relat_1(B_106,A_107),k1_relat_1(B_106))
      | ~ v1_relat_1(B_106) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_309,plain,(
    ! [A_66,A_107] :
      ( r1_tarski(k10_relat_1(k6_relat_1(A_66),A_107),A_66)
      | ~ v1_relat_1(k6_relat_1(A_66)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_54,c_292])).

tff(c_318,plain,(
    ! [A_108,A_109] : r1_tarski(k10_relat_1(k6_relat_1(A_108),A_109),A_108) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_309])).

tff(c_4,plain,(
    ! [B_4,A_3] :
      ( B_4 = A_3
      | ~ r1_tarski(B_4,A_3)
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_334,plain,(
    ! [A_108,A_109] :
      ( k10_relat_1(k6_relat_1(A_108),A_109) = A_108
      | ~ r1_tarski(A_108,k10_relat_1(k6_relat_1(A_108),A_109)) ) ),
    inference(resolution,[status(thm)],[c_318,c_4])).

tff(c_3775,plain,(
    ! [A_237,B_238] : k10_relat_1(k6_relat_1(A_237),k2_xboole_0(A_237,B_238)) = A_237 ),
    inference(resolution,[status(thm)],[c_3688,c_334])).

tff(c_3876,plain,(
    k10_relat_1(k6_relat_1('#skF_1'),k1_relat_1('#skF_2')) = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_121,c_3775])).

tff(c_52,plain,(
    ! [A_63,B_65] :
      ( k10_relat_1(A_63,k1_relat_1(B_65)) = k1_relat_1(k5_relat_1(A_63,B_65))
      | ~ v1_relat_1(B_65)
      | ~ v1_relat_1(A_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_3938,plain,
    ( k1_relat_1(k5_relat_1(k6_relat_1('#skF_1'),'#skF_2')) = '#skF_1'
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1(k6_relat_1('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_3876,c_52])).

tff(c_3978,plain,(
    k1_relat_1(k5_relat_1(k6_relat_1('#skF_1'),'#skF_2')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_68,c_3938])).

tff(c_4026,plain,
    ( k1_relat_1(k7_relat_1('#skF_2','#skF_1')) = '#skF_1'
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_60,c_3978])).

tff(c_4038,plain,(
    k1_relat_1(k7_relat_1('#skF_2','#skF_1')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_4026])).

tff(c_1749,plain,(
    ! [A_184,B_185] :
      ( k10_relat_1(A_184,k1_relat_1(B_185)) = k1_relat_1(k5_relat_1(A_184,B_185))
      | ~ v1_relat_1(B_185)
      | ~ v1_relat_1(A_184) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_1791,plain,(
    ! [B_185] :
      ( k1_relat_1(k5_relat_1(k6_relat_1(k1_relat_1(B_185)),B_185)) = k1_relat_1(B_185)
      | ~ v1_relat_1(B_185)
      | ~ v1_relat_1(k6_relat_1(k1_relat_1(B_185))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1749,c_239])).

tff(c_2053,plain,(
    ! [B_193] :
      ( k1_relat_1(k5_relat_1(k6_relat_1(k1_relat_1(B_193)),B_193)) = k1_relat_1(B_193)
      | ~ v1_relat_1(B_193) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_1791])).

tff(c_10234,plain,(
    ! [B_336] :
      ( k1_relat_1(k7_relat_1(B_336,k1_relat_1(B_336))) = k1_relat_1(B_336)
      | ~ v1_relat_1(B_336)
      | ~ v1_relat_1(B_336) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_60,c_2053])).

tff(c_405,plain,(
    ! [B_117,A_118] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_117,A_118)),A_118)
      | ~ v1_relat_1(B_117) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_414,plain,(
    ! [B_117,A_118] :
      ( k1_relat_1(k7_relat_1(B_117,A_118)) = A_118
      | ~ r1_tarski(A_118,k1_relat_1(k7_relat_1(B_117,A_118)))
      | ~ v1_relat_1(B_117) ) ),
    inference(resolution,[status(thm)],[c_405,c_4])).

tff(c_10261,plain,(
    ! [B_336] :
      ( k1_relat_1(k7_relat_1(B_336,k1_relat_1(B_336))) = k1_relat_1(B_336)
      | ~ r1_tarski(k1_relat_1(B_336),k1_relat_1(B_336))
      | ~ v1_relat_1(B_336)
      | ~ v1_relat_1(B_336)
      | ~ v1_relat_1(B_336) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10234,c_414])).

tff(c_10383,plain,(
    ! [B_337] :
      ( k1_relat_1(k7_relat_1(B_337,k1_relat_1(B_337))) = k1_relat_1(B_337)
      | ~ v1_relat_1(B_337) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_10261])).

tff(c_10476,plain,
    ( k1_relat_1(k7_relat_1(k7_relat_1('#skF_2','#skF_1'),'#skF_1')) = k1_relat_1(k7_relat_1('#skF_2','#skF_1'))
    | ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_4038,c_10383])).

tff(c_10524,plain,
    ( k1_relat_1(k7_relat_1(k7_relat_1('#skF_2','#skF_1'),'#skF_1')) = '#skF_1'
    | ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4038,c_10476])).

tff(c_25499,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_10524])).

tff(c_25502,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_40,c_25499])).

tff(c_25506,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_25502])).

tff(c_25508,plain,(
    v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(splitRight,[status(thm)],[c_10524])).

tff(c_42,plain,(
    ! [A_51] :
      ( k9_relat_1(A_51,k1_relat_1(A_51)) = k2_relat_1(A_51)
      | ~ v1_relat_1(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_2329,plain,(
    ! [A_199,C_200,B_201] :
      ( k9_relat_1(k7_relat_1(A_199,C_200),B_201) = k9_relat_1(A_199,B_201)
      | ~ r1_tarski(B_201,C_200)
      | ~ v1_relat_1(A_199) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_27323,plain,(
    ! [A_508,C_509] :
      ( k9_relat_1(A_508,k1_relat_1(k7_relat_1(A_508,C_509))) = k2_relat_1(k7_relat_1(A_508,C_509))
      | ~ r1_tarski(k1_relat_1(k7_relat_1(A_508,C_509)),C_509)
      | ~ v1_relat_1(A_508)
      | ~ v1_relat_1(k7_relat_1(A_508,C_509)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_2329])).

tff(c_27337,plain,
    ( k9_relat_1('#skF_2',k1_relat_1(k7_relat_1('#skF_2','#skF_1'))) = k2_relat_1(k7_relat_1('#skF_2','#skF_1'))
    | ~ r1_tarski('#skF_1','#skF_1')
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_4038,c_27323])).

tff(c_27357,plain,(
    k2_relat_1(k7_relat_1('#skF_2','#skF_1')) = k9_relat_1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_25508,c_68,c_8,c_4038,c_27337])).

tff(c_48,plain,(
    ! [A_59] :
      ( k10_relat_1(A_59,k2_relat_1(A_59)) = k1_relat_1(A_59)
      | ~ v1_relat_1(A_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_27384,plain,
    ( k10_relat_1(k7_relat_1('#skF_2','#skF_1'),k9_relat_1('#skF_2','#skF_1')) = k1_relat_1(k7_relat_1('#skF_2','#skF_1'))
    | ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_27357,c_48])).

tff(c_27390,plain,(
    k10_relat_1(k7_relat_1('#skF_2','#skF_1'),k9_relat_1('#skF_2','#skF_1')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_25508,c_4038,c_27384])).

tff(c_1508,plain,(
    ! [A_172,C_173,B_174] :
      ( k3_xboole_0(A_172,k10_relat_1(C_173,B_174)) = k10_relat_1(k7_relat_1(C_173,A_172),B_174)
      | ~ v1_relat_1(C_173) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_14,plain,(
    ! [A_7,B_8] : k5_xboole_0(A_7,k3_xboole_0(A_7,B_8)) = k4_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_1514,plain,(
    ! [A_172,C_173,B_174] :
      ( k5_xboole_0(A_172,k10_relat_1(k7_relat_1(C_173,A_172),B_174)) = k4_xboole_0(A_172,k10_relat_1(C_173,B_174))
      | ~ v1_relat_1(C_173) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1508,c_14])).

tff(c_27919,plain,
    ( k4_xboole_0('#skF_1',k10_relat_1('#skF_2',k9_relat_1('#skF_2','#skF_1'))) = k5_xboole_0('#skF_1','#skF_1')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_27390,c_1514])).

tff(c_27964,plain,(
    k4_xboole_0('#skF_1',k10_relat_1('#skF_2',k9_relat_1('#skF_2','#skF_1'))) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_261,c_27919])).

tff(c_27966,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_105,c_27964])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 17:59:20 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 11.27/4.36  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.27/4.37  
% 11.27/4.37  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.27/4.37  %$ r1_tarski > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k5_xboole_0 > k5_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1
% 11.27/4.37  
% 11.27/4.37  %Foreground sorts:
% 11.27/4.37  
% 11.27/4.37  
% 11.27/4.37  %Background operators:
% 11.27/4.37  
% 11.27/4.37  
% 11.27/4.37  %Foreground operators:
% 11.27/4.37  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 11.27/4.37  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 11.27/4.37  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 11.27/4.37  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 11.27/4.37  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 11.27/4.37  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 11.27/4.37  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 11.27/4.37  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 11.27/4.37  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 11.27/4.37  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 11.27/4.37  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 11.27/4.37  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 11.27/4.37  tff('#skF_2', type, '#skF_2': $i).
% 11.27/4.37  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 11.27/4.37  tff('#skF_1', type, '#skF_1': $i).
% 11.27/4.37  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 11.27/4.37  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 11.27/4.37  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 11.27/4.37  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 11.27/4.37  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 11.27/4.37  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 11.27/4.37  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 11.27/4.37  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 11.27/4.37  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 11.27/4.37  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 11.27/4.37  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 11.27/4.37  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 11.27/4.37  
% 11.27/4.38  tff(f_37, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 11.27/4.38  tff(f_126, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => r1_tarski(A, k10_relat_1(B, k9_relat_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t146_funct_1)).
% 11.27/4.38  tff(f_33, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 11.27/4.38  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 11.27/4.38  tff(f_39, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 11.27/4.38  tff(f_73, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 11.27/4.38  tff(f_115, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_relat_1)).
% 11.27/4.38  tff(f_69, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 11.27/4.38  tff(f_47, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 11.27/4.38  tff(f_107, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 11.27/4.38  tff(f_92, axiom, (![A]: (v1_relat_1(A) => (k10_relat_1(A, k2_relat_1(A)) = k1_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t169_relat_1)).
% 11.27/4.38  tff(f_96, axiom, (![A, B, C]: (v1_relat_1(C) => (k10_relat_1(C, k2_xboole_0(A, B)) = k2_xboole_0(k10_relat_1(C, A), k10_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t175_relat_1)).
% 11.27/4.38  tff(f_49, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 11.27/4.38  tff(f_88, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k10_relat_1(B, A), k1_relat_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t167_relat_1)).
% 11.27/4.38  tff(f_103, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k1_relat_1(k5_relat_1(A, B)) = k10_relat_1(A, k1_relat_1(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t182_relat_1)).
% 11.27/4.38  tff(f_111, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k7_relat_1(B, A)), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t87_relat_1)).
% 11.27/4.38  tff(f_77, axiom, (![A]: (v1_relat_1(A) => (k9_relat_1(A, k1_relat_1(A)) = k2_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t146_relat_1)).
% 11.27/4.38  tff(f_84, axiom, (![A]: (v1_relat_1(A) => (![B, C]: (r1_tarski(B, C) => (k9_relat_1(k7_relat_1(A, C), B) = k9_relat_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t162_relat_1)).
% 11.27/4.38  tff(f_119, axiom, (![A, B, C]: (v1_relat_1(C) => (k10_relat_1(k7_relat_1(C, A), B) = k3_xboole_0(A, k10_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t139_funct_1)).
% 11.27/4.38  tff(c_101, plain, (![A_83, B_84]: (r1_tarski(A_83, B_84) | k4_xboole_0(A_83, B_84)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 11.27/4.38  tff(c_64, plain, (~r1_tarski('#skF_1', k10_relat_1('#skF_2', k9_relat_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_126])).
% 11.27/4.38  tff(c_105, plain, (k4_xboole_0('#skF_1', k10_relat_1('#skF_2', k9_relat_1('#skF_2', '#skF_1')))!=k1_xboole_0), inference(resolution, [status(thm)], [c_101, c_64])).
% 11.27/4.38  tff(c_68, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_126])).
% 11.27/4.38  tff(c_8, plain, (![B_4]: (r1_tarski(B_4, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 11.27/4.38  tff(c_162, plain, (![A_92, B_93]: (k4_xboole_0(A_92, B_93)=k1_xboole_0 | ~r1_tarski(A_92, B_93))), inference(cnfTransformation, [status(thm)], [f_37])).
% 11.27/4.38  tff(c_178, plain, (![B_4]: (k4_xboole_0(B_4, B_4)=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_162])).
% 11.27/4.38  tff(c_2, plain, (![A_1]: (k3_xboole_0(A_1, A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 11.27/4.38  tff(c_249, plain, (![A_101, B_102]: (k5_xboole_0(A_101, k3_xboole_0(A_101, B_102))=k4_xboole_0(A_101, B_102))), inference(cnfTransformation, [status(thm)], [f_39])).
% 11.27/4.38  tff(c_258, plain, (![A_1]: (k5_xboole_0(A_1, A_1)=k4_xboole_0(A_1, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_249])).
% 11.27/4.38  tff(c_261, plain, (![A_1]: (k5_xboole_0(A_1, A_1)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_178, c_258])).
% 11.27/4.38  tff(c_40, plain, (![A_49, B_50]: (v1_relat_1(k7_relat_1(A_49, B_50)) | ~v1_relat_1(A_49))), inference(cnfTransformation, [status(thm)], [f_73])).
% 11.27/4.38  tff(c_60, plain, (![A_69, B_70]: (k5_relat_1(k6_relat_1(A_69), B_70)=k7_relat_1(B_70, A_69) | ~v1_relat_1(B_70))), inference(cnfTransformation, [status(thm)], [f_115])).
% 11.27/4.38  tff(c_38, plain, (![A_48]: (v1_relat_1(k6_relat_1(A_48)))), inference(cnfTransformation, [status(thm)], [f_69])).
% 11.27/4.38  tff(c_66, plain, (r1_tarski('#skF_1', k1_relat_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_126])).
% 11.27/4.38  tff(c_106, plain, (![A_85, B_86]: (k2_xboole_0(A_85, B_86)=B_86 | ~r1_tarski(A_85, B_86))), inference(cnfTransformation, [status(thm)], [f_47])).
% 11.27/4.38  tff(c_121, plain, (k2_xboole_0('#skF_1', k1_relat_1('#skF_2'))=k1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_66, c_106])).
% 11.27/4.38  tff(c_54, plain, (![A_66]: (k1_relat_1(k6_relat_1(A_66))=A_66)), inference(cnfTransformation, [status(thm)], [f_107])).
% 11.27/4.38  tff(c_56, plain, (![A_66]: (k2_relat_1(k6_relat_1(A_66))=A_66)), inference(cnfTransformation, [status(thm)], [f_107])).
% 11.27/4.38  tff(c_226, plain, (![A_99]: (k10_relat_1(A_99, k2_relat_1(A_99))=k1_relat_1(A_99) | ~v1_relat_1(A_99))), inference(cnfTransformation, [status(thm)], [f_92])).
% 11.27/4.38  tff(c_235, plain, (![A_66]: (k10_relat_1(k6_relat_1(A_66), A_66)=k1_relat_1(k6_relat_1(A_66)) | ~v1_relat_1(k6_relat_1(A_66)))), inference(superposition, [status(thm), theory('equality')], [c_56, c_226])).
% 11.27/4.38  tff(c_239, plain, (![A_66]: (k10_relat_1(k6_relat_1(A_66), A_66)=A_66)), inference(demodulation, [status(thm), theory('equality')], [c_38, c_54, c_235])).
% 11.27/4.38  tff(c_3091, plain, (![C_222, A_223, B_224]: (k2_xboole_0(k10_relat_1(C_222, A_223), k10_relat_1(C_222, B_224))=k10_relat_1(C_222, k2_xboole_0(A_223, B_224)) | ~v1_relat_1(C_222))), inference(cnfTransformation, [status(thm)], [f_96])).
% 11.27/4.38  tff(c_20, plain, (![A_14, B_15]: (r1_tarski(A_14, k2_xboole_0(A_14, B_15)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 11.27/4.38  tff(c_3576, plain, (![C_232, A_233, B_234]: (r1_tarski(k10_relat_1(C_232, A_233), k10_relat_1(C_232, k2_xboole_0(A_233, B_234))) | ~v1_relat_1(C_232))), inference(superposition, [status(thm), theory('equality')], [c_3091, c_20])).
% 11.27/4.38  tff(c_3651, plain, (![A_66, B_234]: (r1_tarski(A_66, k10_relat_1(k6_relat_1(A_66), k2_xboole_0(A_66, B_234))) | ~v1_relat_1(k6_relat_1(A_66)))), inference(superposition, [status(thm), theory('equality')], [c_239, c_3576])).
% 11.27/4.38  tff(c_3688, plain, (![A_235, B_236]: (r1_tarski(A_235, k10_relat_1(k6_relat_1(A_235), k2_xboole_0(A_235, B_236))))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_3651])).
% 11.27/4.38  tff(c_292, plain, (![B_106, A_107]: (r1_tarski(k10_relat_1(B_106, A_107), k1_relat_1(B_106)) | ~v1_relat_1(B_106))), inference(cnfTransformation, [status(thm)], [f_88])).
% 11.27/4.38  tff(c_309, plain, (![A_66, A_107]: (r1_tarski(k10_relat_1(k6_relat_1(A_66), A_107), A_66) | ~v1_relat_1(k6_relat_1(A_66)))), inference(superposition, [status(thm), theory('equality')], [c_54, c_292])).
% 11.27/4.38  tff(c_318, plain, (![A_108, A_109]: (r1_tarski(k10_relat_1(k6_relat_1(A_108), A_109), A_108))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_309])).
% 11.27/4.38  tff(c_4, plain, (![B_4, A_3]: (B_4=A_3 | ~r1_tarski(B_4, A_3) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 11.27/4.38  tff(c_334, plain, (![A_108, A_109]: (k10_relat_1(k6_relat_1(A_108), A_109)=A_108 | ~r1_tarski(A_108, k10_relat_1(k6_relat_1(A_108), A_109)))), inference(resolution, [status(thm)], [c_318, c_4])).
% 11.27/4.38  tff(c_3775, plain, (![A_237, B_238]: (k10_relat_1(k6_relat_1(A_237), k2_xboole_0(A_237, B_238))=A_237)), inference(resolution, [status(thm)], [c_3688, c_334])).
% 11.27/4.38  tff(c_3876, plain, (k10_relat_1(k6_relat_1('#skF_1'), k1_relat_1('#skF_2'))='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_121, c_3775])).
% 11.27/4.38  tff(c_52, plain, (![A_63, B_65]: (k10_relat_1(A_63, k1_relat_1(B_65))=k1_relat_1(k5_relat_1(A_63, B_65)) | ~v1_relat_1(B_65) | ~v1_relat_1(A_63))), inference(cnfTransformation, [status(thm)], [f_103])).
% 11.27/4.38  tff(c_3938, plain, (k1_relat_1(k5_relat_1(k6_relat_1('#skF_1'), '#skF_2'))='#skF_1' | ~v1_relat_1('#skF_2') | ~v1_relat_1(k6_relat_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_3876, c_52])).
% 11.27/4.38  tff(c_3978, plain, (k1_relat_1(k5_relat_1(k6_relat_1('#skF_1'), '#skF_2'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_38, c_68, c_3938])).
% 11.27/4.38  tff(c_4026, plain, (k1_relat_1(k7_relat_1('#skF_2', '#skF_1'))='#skF_1' | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_60, c_3978])).
% 11.27/4.38  tff(c_4038, plain, (k1_relat_1(k7_relat_1('#skF_2', '#skF_1'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_68, c_4026])).
% 11.27/4.38  tff(c_1749, plain, (![A_184, B_185]: (k10_relat_1(A_184, k1_relat_1(B_185))=k1_relat_1(k5_relat_1(A_184, B_185)) | ~v1_relat_1(B_185) | ~v1_relat_1(A_184))), inference(cnfTransformation, [status(thm)], [f_103])).
% 11.27/4.38  tff(c_1791, plain, (![B_185]: (k1_relat_1(k5_relat_1(k6_relat_1(k1_relat_1(B_185)), B_185))=k1_relat_1(B_185) | ~v1_relat_1(B_185) | ~v1_relat_1(k6_relat_1(k1_relat_1(B_185))))), inference(superposition, [status(thm), theory('equality')], [c_1749, c_239])).
% 11.27/4.38  tff(c_2053, plain, (![B_193]: (k1_relat_1(k5_relat_1(k6_relat_1(k1_relat_1(B_193)), B_193))=k1_relat_1(B_193) | ~v1_relat_1(B_193))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_1791])).
% 11.27/4.38  tff(c_10234, plain, (![B_336]: (k1_relat_1(k7_relat_1(B_336, k1_relat_1(B_336)))=k1_relat_1(B_336) | ~v1_relat_1(B_336) | ~v1_relat_1(B_336))), inference(superposition, [status(thm), theory('equality')], [c_60, c_2053])).
% 11.27/4.38  tff(c_405, plain, (![B_117, A_118]: (r1_tarski(k1_relat_1(k7_relat_1(B_117, A_118)), A_118) | ~v1_relat_1(B_117))), inference(cnfTransformation, [status(thm)], [f_111])).
% 11.27/4.38  tff(c_414, plain, (![B_117, A_118]: (k1_relat_1(k7_relat_1(B_117, A_118))=A_118 | ~r1_tarski(A_118, k1_relat_1(k7_relat_1(B_117, A_118))) | ~v1_relat_1(B_117))), inference(resolution, [status(thm)], [c_405, c_4])).
% 11.27/4.38  tff(c_10261, plain, (![B_336]: (k1_relat_1(k7_relat_1(B_336, k1_relat_1(B_336)))=k1_relat_1(B_336) | ~r1_tarski(k1_relat_1(B_336), k1_relat_1(B_336)) | ~v1_relat_1(B_336) | ~v1_relat_1(B_336) | ~v1_relat_1(B_336))), inference(superposition, [status(thm), theory('equality')], [c_10234, c_414])).
% 11.27/4.38  tff(c_10383, plain, (![B_337]: (k1_relat_1(k7_relat_1(B_337, k1_relat_1(B_337)))=k1_relat_1(B_337) | ~v1_relat_1(B_337))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_10261])).
% 11.27/4.38  tff(c_10476, plain, (k1_relat_1(k7_relat_1(k7_relat_1('#skF_2', '#skF_1'), '#skF_1'))=k1_relat_1(k7_relat_1('#skF_2', '#skF_1')) | ~v1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_4038, c_10383])).
% 11.27/4.38  tff(c_10524, plain, (k1_relat_1(k7_relat_1(k7_relat_1('#skF_2', '#skF_1'), '#skF_1'))='#skF_1' | ~v1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_4038, c_10476])).
% 11.27/4.38  tff(c_25499, plain, (~v1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(splitLeft, [status(thm)], [c_10524])).
% 11.27/4.38  tff(c_25502, plain, (~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_40, c_25499])).
% 11.27/4.38  tff(c_25506, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_68, c_25502])).
% 11.27/4.38  tff(c_25508, plain, (v1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(splitRight, [status(thm)], [c_10524])).
% 11.27/4.38  tff(c_42, plain, (![A_51]: (k9_relat_1(A_51, k1_relat_1(A_51))=k2_relat_1(A_51) | ~v1_relat_1(A_51))), inference(cnfTransformation, [status(thm)], [f_77])).
% 11.27/4.38  tff(c_2329, plain, (![A_199, C_200, B_201]: (k9_relat_1(k7_relat_1(A_199, C_200), B_201)=k9_relat_1(A_199, B_201) | ~r1_tarski(B_201, C_200) | ~v1_relat_1(A_199))), inference(cnfTransformation, [status(thm)], [f_84])).
% 11.27/4.38  tff(c_27323, plain, (![A_508, C_509]: (k9_relat_1(A_508, k1_relat_1(k7_relat_1(A_508, C_509)))=k2_relat_1(k7_relat_1(A_508, C_509)) | ~r1_tarski(k1_relat_1(k7_relat_1(A_508, C_509)), C_509) | ~v1_relat_1(A_508) | ~v1_relat_1(k7_relat_1(A_508, C_509)))), inference(superposition, [status(thm), theory('equality')], [c_42, c_2329])).
% 11.27/4.38  tff(c_27337, plain, (k9_relat_1('#skF_2', k1_relat_1(k7_relat_1('#skF_2', '#skF_1')))=k2_relat_1(k7_relat_1('#skF_2', '#skF_1')) | ~r1_tarski('#skF_1', '#skF_1') | ~v1_relat_1('#skF_2') | ~v1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_4038, c_27323])).
% 11.27/4.38  tff(c_27357, plain, (k2_relat_1(k7_relat_1('#skF_2', '#skF_1'))=k9_relat_1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_25508, c_68, c_8, c_4038, c_27337])).
% 11.27/4.39  tff(c_48, plain, (![A_59]: (k10_relat_1(A_59, k2_relat_1(A_59))=k1_relat_1(A_59) | ~v1_relat_1(A_59))), inference(cnfTransformation, [status(thm)], [f_92])).
% 11.27/4.39  tff(c_27384, plain, (k10_relat_1(k7_relat_1('#skF_2', '#skF_1'), k9_relat_1('#skF_2', '#skF_1'))=k1_relat_1(k7_relat_1('#skF_2', '#skF_1')) | ~v1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_27357, c_48])).
% 11.27/4.39  tff(c_27390, plain, (k10_relat_1(k7_relat_1('#skF_2', '#skF_1'), k9_relat_1('#skF_2', '#skF_1'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_25508, c_4038, c_27384])).
% 11.27/4.39  tff(c_1508, plain, (![A_172, C_173, B_174]: (k3_xboole_0(A_172, k10_relat_1(C_173, B_174))=k10_relat_1(k7_relat_1(C_173, A_172), B_174) | ~v1_relat_1(C_173))), inference(cnfTransformation, [status(thm)], [f_119])).
% 11.27/4.39  tff(c_14, plain, (![A_7, B_8]: (k5_xboole_0(A_7, k3_xboole_0(A_7, B_8))=k4_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_39])).
% 11.27/4.39  tff(c_1514, plain, (![A_172, C_173, B_174]: (k5_xboole_0(A_172, k10_relat_1(k7_relat_1(C_173, A_172), B_174))=k4_xboole_0(A_172, k10_relat_1(C_173, B_174)) | ~v1_relat_1(C_173))), inference(superposition, [status(thm), theory('equality')], [c_1508, c_14])).
% 11.27/4.39  tff(c_27919, plain, (k4_xboole_0('#skF_1', k10_relat_1('#skF_2', k9_relat_1('#skF_2', '#skF_1')))=k5_xboole_0('#skF_1', '#skF_1') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_27390, c_1514])).
% 11.27/4.39  tff(c_27964, plain, (k4_xboole_0('#skF_1', k10_relat_1('#skF_2', k9_relat_1('#skF_2', '#skF_1')))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_68, c_261, c_27919])).
% 11.27/4.39  tff(c_27966, plain, $false, inference(negUnitSimplification, [status(thm)], [c_105, c_27964])).
% 11.27/4.39  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.27/4.39  
% 11.27/4.39  Inference rules
% 11.27/4.39  ----------------------
% 11.27/4.39  #Ref     : 0
% 11.27/4.39  #Sup     : 6632
% 11.27/4.39  #Fact    : 0
% 11.27/4.39  #Define  : 0
% 11.27/4.39  #Split   : 3
% 11.27/4.39  #Chain   : 0
% 11.27/4.39  #Close   : 0
% 11.27/4.39  
% 11.27/4.39  Ordering : KBO
% 11.27/4.39  
% 11.27/4.39  Simplification rules
% 11.27/4.39  ----------------------
% 11.27/4.39  #Subsume      : 954
% 11.27/4.39  #Demod        : 5573
% 11.27/4.39  #Tautology    : 3417
% 11.27/4.39  #SimpNegUnit  : 1
% 11.27/4.39  #BackRed      : 7
% 11.27/4.39  
% 11.27/4.39  #Partial instantiations: 0
% 11.27/4.39  #Strategies tried      : 1
% 11.27/4.39  
% 11.27/4.39  Timing (in seconds)
% 11.27/4.39  ----------------------
% 11.43/4.39  Preprocessing        : 0.33
% 11.43/4.39  Parsing              : 0.17
% 11.43/4.39  CNF conversion       : 0.02
% 11.43/4.39  Main loop            : 3.28
% 11.43/4.39  Inferencing          : 0.80
% 11.43/4.39  Reduction            : 1.41
% 11.43/4.39  Demodulation         : 1.16
% 11.43/4.39  BG Simplification    : 0.10
% 11.43/4.39  Subsumption          : 0.80
% 11.43/4.39  Abstraction          : 0.15
% 11.43/4.39  MUC search           : 0.00
% 11.43/4.39  Cooper               : 0.00
% 11.43/4.39  Total                : 3.65
% 11.43/4.39  Index Insertion      : 0.00
% 11.43/4.39  Index Deletion       : 0.00
% 11.43/4.39  Index Matching       : 0.00
% 11.43/4.39  BG Taut test         : 0.00
%------------------------------------------------------------------------------

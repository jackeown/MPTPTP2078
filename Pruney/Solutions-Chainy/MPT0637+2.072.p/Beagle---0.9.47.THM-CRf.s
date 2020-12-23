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
% DateTime   : Thu Dec  3 10:03:33 EST 2020

% Result     : Theorem 5.09s
% Output     : CNFRefutation 5.40s
% Verified   : 
% Statistics : Number of formulae       :  105 ( 298 expanded)
%              Number of leaves         :   38 ( 121 expanded)
%              Depth                    :   15
%              Number of atoms          :  164 ( 560 expanded)
%              Number of equality atoms :   61 ( 155 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r1_tarski > v1_relat_1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k8_relat_1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k6_relat_1 > k4_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1

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

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k4_relat_1,type,(
    k4_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_119,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v4_relat_1(k6_relat_1(A),A)
      & v5_relat_1(k6_relat_1(A),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc24_relat_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k8_relat_1(A,B) = k5_relat_1(B,k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_relat_1)).

tff(f_109,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k5_relat_1(k6_relat_1(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_relat_1(B) )
     => v1_relat_1(k5_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).

tff(f_93,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_113,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k7_relat_1(A,k1_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_relat_1)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k7_relat_1(k7_relat_1(C,A),B) = k7_relat_1(C,k3_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_relat_1)).

tff(f_105,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k1_relat_1(k7_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_relat_1)).

tff(f_65,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k7_relat_1(k8_relat_1(A,C),B) = k8_relat_1(A,k7_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t140_relat_1)).

tff(f_101,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k5_relat_1(B,k6_relat_1(A)),B)
        & r1_tarski(k5_relat_1(k6_relat_1(A),B),B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_relat_1)).

tff(f_82,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(A,B)
           => ( r1_tarski(k1_relat_1(A),k1_relat_1(B))
              & r1_tarski(k2_relat_1(A),k2_relat_1(B)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_relat_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k2_relat_1(B),A)
       => k8_relat_1(A,B) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_relat_1)).

tff(f_95,axiom,(
    ! [A] : k4_relat_1(k6_relat_1(A)) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_relat_1)).

tff(f_89,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k4_relat_1(k5_relat_1(A,B)) = k5_relat_1(k4_relat_1(B),k4_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t54_relat_1)).

tff(f_122,negated_conjecture,(
    ~ ! [A,B] : k5_relat_1(k6_relat_1(B),k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_funct_1)).

tff(c_48,plain,(
    ! [A_49] : v1_relat_1(k6_relat_1(A_49)) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_203,plain,(
    ! [B_82,A_83] :
      ( k5_relat_1(B_82,k6_relat_1(A_83)) = k8_relat_1(A_83,B_82)
      | ~ v1_relat_1(B_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_44,plain,(
    ! [A_46,B_47] :
      ( k5_relat_1(k6_relat_1(A_46),B_47) = k7_relat_1(B_47,A_46)
      | ~ v1_relat_1(B_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_210,plain,(
    ! [A_83,A_46] :
      ( k8_relat_1(A_83,k6_relat_1(A_46)) = k7_relat_1(k6_relat_1(A_83),A_46)
      | ~ v1_relat_1(k6_relat_1(A_83))
      | ~ v1_relat_1(k6_relat_1(A_46)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_203,c_44])).

tff(c_308,plain,(
    ! [A_96,A_97] : k8_relat_1(A_96,k6_relat_1(A_97)) = k7_relat_1(k6_relat_1(A_96),A_97) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_48,c_210])).

tff(c_12,plain,(
    ! [A_17,B_18] :
      ( v1_relat_1(k5_relat_1(A_17,B_18))
      | ~ v1_relat_1(B_18)
      | ~ v1_relat_1(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_220,plain,(
    ! [A_83,B_82] :
      ( v1_relat_1(k8_relat_1(A_83,B_82))
      | ~ v1_relat_1(k6_relat_1(A_83))
      | ~ v1_relat_1(B_82)
      | ~ v1_relat_1(B_82) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_203,c_12])).

tff(c_237,plain,(
    ! [A_83,B_82] :
      ( v1_relat_1(k8_relat_1(A_83,B_82))
      | ~ v1_relat_1(B_82) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_220])).

tff(c_322,plain,(
    ! [A_96,A_97] :
      ( v1_relat_1(k7_relat_1(k6_relat_1(A_96),A_97))
      | ~ v1_relat_1(k6_relat_1(A_97)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_308,c_237])).

tff(c_338,plain,(
    ! [A_96,A_97] : v1_relat_1(k7_relat_1(k6_relat_1(A_96),A_97)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_322])).

tff(c_32,plain,(
    ! [A_40] : k1_relat_1(k6_relat_1(A_40)) = A_40 ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_103,plain,(
    ! [A_60] :
      ( k7_relat_1(A_60,k1_relat_1(A_60)) = A_60
      | ~ v1_relat_1(A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_112,plain,(
    ! [A_40] :
      ( k7_relat_1(k6_relat_1(A_40),A_40) = k6_relat_1(A_40)
      | ~ v1_relat_1(k6_relat_1(A_40)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_103])).

tff(c_116,plain,(
    ! [A_40] : k7_relat_1(k6_relat_1(A_40),A_40) = k6_relat_1(A_40) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_112])).

tff(c_487,plain,(
    ! [C_116,A_117,B_118] :
      ( k7_relat_1(k7_relat_1(C_116,A_117),B_118) = k7_relat_1(C_116,k3_xboole_0(A_117,B_118))
      | ~ v1_relat_1(C_116) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_42,plain,(
    ! [B_45,A_44] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_45,A_44)),A_44)
      | ~ v1_relat_1(B_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_2972,plain,(
    ! [C_219,A_220,B_221] :
      ( r1_tarski(k1_relat_1(k7_relat_1(C_219,k3_xboole_0(A_220,B_221))),B_221)
      | ~ v1_relat_1(k7_relat_1(C_219,A_220))
      | ~ v1_relat_1(C_219) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_487,c_42])).

tff(c_3020,plain,(
    ! [A_220,B_221] :
      ( r1_tarski(k1_relat_1(k6_relat_1(k3_xboole_0(A_220,B_221))),B_221)
      | ~ v1_relat_1(k7_relat_1(k6_relat_1(k3_xboole_0(A_220,B_221)),A_220))
      | ~ v1_relat_1(k6_relat_1(k3_xboole_0(A_220,B_221))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_116,c_2972])).

tff(c_3037,plain,(
    ! [A_220,B_221] : r1_tarski(k3_xboole_0(A_220,B_221),B_221) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_338,c_32,c_3020])).

tff(c_233,plain,(
    ! [A_83,A_46] : k8_relat_1(A_83,k6_relat_1(A_46)) = k7_relat_1(k6_relat_1(A_83),A_46) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_48,c_210])).

tff(c_605,plain,(
    ! [A_125,C_126,B_127] :
      ( k8_relat_1(A_125,k7_relat_1(C_126,B_127)) = k7_relat_1(k8_relat_1(A_125,C_126),B_127)
      | ~ v1_relat_1(C_126) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_637,plain,(
    ! [A_125,A_40] :
      ( k7_relat_1(k8_relat_1(A_125,k6_relat_1(A_40)),A_40) = k8_relat_1(A_125,k6_relat_1(A_40))
      | ~ v1_relat_1(k6_relat_1(A_40)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_116,c_605])).

tff(c_648,plain,(
    ! [A_125,A_40] : k7_relat_1(k7_relat_1(k6_relat_1(A_125),A_40),A_40) = k7_relat_1(k6_relat_1(A_125),A_40) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_233,c_233,c_637])).

tff(c_14,plain,(
    ! [C_21,A_19,B_20] :
      ( k7_relat_1(k7_relat_1(C_21,A_19),B_20) = k7_relat_1(C_21,k3_xboole_0(A_19,B_20))
      | ~ v1_relat_1(C_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_22,plain,(
    ! [A_29,C_31,B_30] :
      ( k8_relat_1(A_29,k7_relat_1(C_31,B_30)) = k7_relat_1(k8_relat_1(A_29,C_31),B_30)
      | ~ v1_relat_1(C_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_146,plain,(
    ! [A_73,B_74] :
      ( k5_relat_1(k6_relat_1(A_73),B_74) = k7_relat_1(B_74,A_73)
      | ~ v1_relat_1(B_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_40,plain,(
    ! [B_43,A_42] :
      ( r1_tarski(k5_relat_1(B_43,k6_relat_1(A_42)),B_43)
      | ~ v1_relat_1(B_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_156,plain,(
    ! [A_42,A_73] :
      ( r1_tarski(k7_relat_1(k6_relat_1(A_42),A_73),k6_relat_1(A_73))
      | ~ v1_relat_1(k6_relat_1(A_73))
      | ~ v1_relat_1(k6_relat_1(A_42)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_146,c_40])).

tff(c_168,plain,(
    ! [A_42,A_73] : r1_tarski(k7_relat_1(k6_relat_1(A_42),A_73),k6_relat_1(A_73)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_48,c_156])).

tff(c_34,plain,(
    ! [A_40] : k2_relat_1(k6_relat_1(A_40)) = A_40 ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_691,plain,(
    ! [A_132,B_133] :
      ( r1_tarski(k2_relat_1(A_132),k2_relat_1(B_133))
      | ~ r1_tarski(A_132,B_133)
      | ~ v1_relat_1(B_133)
      | ~ v1_relat_1(A_132) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_700,plain,(
    ! [A_132,A_40] :
      ( r1_tarski(k2_relat_1(A_132),A_40)
      | ~ r1_tarski(A_132,k6_relat_1(A_40))
      | ~ v1_relat_1(k6_relat_1(A_40))
      | ~ v1_relat_1(A_132) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_691])).

tff(c_717,plain,(
    ! [A_136,A_137] :
      ( r1_tarski(k2_relat_1(A_136),A_137)
      | ~ r1_tarski(A_136,k6_relat_1(A_137))
      | ~ v1_relat_1(A_136) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_700])).

tff(c_20,plain,(
    ! [A_27,B_28] :
      ( k8_relat_1(A_27,B_28) = B_28
      | ~ r1_tarski(k2_relat_1(B_28),A_27)
      | ~ v1_relat_1(B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_766,plain,(
    ! [A_145,A_146] :
      ( k8_relat_1(A_145,A_146) = A_146
      | ~ r1_tarski(A_146,k6_relat_1(A_145))
      | ~ v1_relat_1(A_146) ) ),
    inference(resolution,[status(thm)],[c_717,c_20])).

tff(c_797,plain,(
    ! [A_73,A_42] :
      ( k8_relat_1(A_73,k7_relat_1(k6_relat_1(A_42),A_73)) = k7_relat_1(k6_relat_1(A_42),A_73)
      | ~ v1_relat_1(k7_relat_1(k6_relat_1(A_42),A_73)) ) ),
    inference(resolution,[status(thm)],[c_168,c_766])).

tff(c_1495,plain,(
    ! [A_165,A_166] : k8_relat_1(A_165,k7_relat_1(k6_relat_1(A_166),A_165)) = k7_relat_1(k6_relat_1(A_166),A_165) ),
    inference(demodulation,[status(thm),theory(equality)],[c_338,c_797])).

tff(c_1522,plain,(
    ! [B_30,A_166] :
      ( k7_relat_1(k8_relat_1(B_30,k6_relat_1(A_166)),B_30) = k7_relat_1(k6_relat_1(A_166),B_30)
      | ~ v1_relat_1(k6_relat_1(A_166)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_1495])).

tff(c_1661,plain,(
    ! [B_171,A_172] : k7_relat_1(k7_relat_1(k6_relat_1(B_171),A_172),B_171) = k7_relat_1(k6_relat_1(A_172),B_171) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_233,c_1522])).

tff(c_1710,plain,(
    ! [B_20,A_19] :
      ( k7_relat_1(k6_relat_1(B_20),k3_xboole_0(A_19,B_20)) = k7_relat_1(k6_relat_1(A_19),B_20)
      | ~ v1_relat_1(k6_relat_1(B_20)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_1661])).

tff(c_1814,plain,(
    ! [B_177,A_178] : k7_relat_1(k6_relat_1(B_177),k3_xboole_0(A_178,B_177)) = k7_relat_1(k6_relat_1(A_178),B_177) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_1710])).

tff(c_1551,plain,(
    ! [B_30,A_166] : k7_relat_1(k7_relat_1(k6_relat_1(B_30),A_166),B_30) = k7_relat_1(k6_relat_1(A_166),B_30) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_233,c_1522])).

tff(c_1826,plain,(
    ! [A_178,B_177] : k7_relat_1(k7_relat_1(k6_relat_1(A_178),B_177),B_177) = k7_relat_1(k6_relat_1(k3_xboole_0(A_178,B_177)),B_177) ),
    inference(superposition,[status(thm),theory(equality)],[c_1814,c_1551])).

tff(c_1893,plain,(
    ! [A_178,B_177] : k7_relat_1(k6_relat_1(k3_xboole_0(A_178,B_177)),B_177) = k7_relat_1(k6_relat_1(A_178),B_177) ),
    inference(demodulation,[status(thm),theory(equality)],[c_648,c_1826])).

tff(c_36,plain,(
    ! [A_41] : k4_relat_1(k6_relat_1(A_41)) = k6_relat_1(A_41) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_245,plain,(
    ! [A_88,B_89] :
      ( k8_relat_1(A_88,B_89) = B_89
      | ~ r1_tarski(k2_relat_1(B_89),A_88)
      | ~ v1_relat_1(B_89) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_252,plain,(
    ! [A_88,A_40] :
      ( k8_relat_1(A_88,k6_relat_1(A_40)) = k6_relat_1(A_40)
      | ~ r1_tarski(A_40,A_88)
      | ~ v1_relat_1(k6_relat_1(A_40)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_245])).

tff(c_255,plain,(
    ! [A_88,A_40] :
      ( k8_relat_1(A_88,k6_relat_1(A_40)) = k6_relat_1(A_40)
      | ~ r1_tarski(A_40,A_88) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_252])).

tff(c_402,plain,(
    ! [A_88,A_40] :
      ( k7_relat_1(k6_relat_1(A_88),A_40) = k6_relat_1(A_40)
      | ~ r1_tarski(A_40,A_88) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_233,c_255])).

tff(c_18,plain,(
    ! [B_26,A_25] :
      ( k5_relat_1(B_26,k6_relat_1(A_25)) = k8_relat_1(A_25,B_26)
      | ~ v1_relat_1(B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_1361,plain,(
    ! [B_160,A_161] :
      ( k5_relat_1(k4_relat_1(B_160),k4_relat_1(A_161)) = k4_relat_1(k5_relat_1(A_161,B_160))
      | ~ v1_relat_1(B_160)
      | ~ v1_relat_1(A_161) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_1373,plain,(
    ! [A_41,A_161] :
      ( k5_relat_1(k6_relat_1(A_41),k4_relat_1(A_161)) = k4_relat_1(k5_relat_1(A_161,k6_relat_1(A_41)))
      | ~ v1_relat_1(k6_relat_1(A_41))
      | ~ v1_relat_1(A_161) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_1361])).

tff(c_2011,plain,(
    ! [A_181,A_182] :
      ( k5_relat_1(k6_relat_1(A_181),k4_relat_1(A_182)) = k4_relat_1(k5_relat_1(A_182,k6_relat_1(A_181)))
      | ~ v1_relat_1(A_182) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_1373])).

tff(c_2033,plain,(
    ! [A_41,A_181] :
      ( k4_relat_1(k5_relat_1(k6_relat_1(A_41),k6_relat_1(A_181))) = k5_relat_1(k6_relat_1(A_181),k6_relat_1(A_41))
      | ~ v1_relat_1(k6_relat_1(A_41)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_2011])).

tff(c_2701,plain,(
    ! [A_207,A_208] : k4_relat_1(k5_relat_1(k6_relat_1(A_207),k6_relat_1(A_208))) = k5_relat_1(k6_relat_1(A_208),k6_relat_1(A_207)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_2033])).

tff(c_2723,plain,(
    ! [A_25,A_207] :
      ( k5_relat_1(k6_relat_1(A_25),k6_relat_1(A_207)) = k4_relat_1(k8_relat_1(A_25,k6_relat_1(A_207)))
      | ~ v1_relat_1(k6_relat_1(A_207)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_2701])).

tff(c_2736,plain,(
    ! [A_209,A_210] : k5_relat_1(k6_relat_1(A_209),k6_relat_1(A_210)) = k4_relat_1(k7_relat_1(k6_relat_1(A_209),A_210)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_233,c_2723])).

tff(c_2765,plain,(
    ! [A_46,A_210] :
      ( k4_relat_1(k7_relat_1(k6_relat_1(A_46),A_210)) = k7_relat_1(k6_relat_1(A_210),A_46)
      | ~ v1_relat_1(k6_relat_1(A_210)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_2736])).

tff(c_2907,plain,(
    ! [A_217,A_218] : k4_relat_1(k7_relat_1(k6_relat_1(A_217),A_218)) = k7_relat_1(k6_relat_1(A_218),A_217) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_2765])).

tff(c_2944,plain,(
    ! [A_40,A_88] :
      ( k7_relat_1(k6_relat_1(A_40),A_88) = k4_relat_1(k6_relat_1(A_40))
      | ~ r1_tarski(A_40,A_88) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_402,c_2907])).

tff(c_3554,plain,(
    ! [A_239,A_240] :
      ( k7_relat_1(k6_relat_1(A_239),A_240) = k6_relat_1(A_239)
      | ~ r1_tarski(A_239,A_240) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_2944])).

tff(c_3690,plain,(
    ! [A_178,B_177] :
      ( k7_relat_1(k6_relat_1(A_178),B_177) = k6_relat_1(k3_xboole_0(A_178,B_177))
      | ~ r1_tarski(k3_xboole_0(A_178,B_177),B_177) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1893,c_3554])).

tff(c_3758,plain,(
    ! [A_178,B_177] : k7_relat_1(k6_relat_1(A_178),B_177) = k6_relat_1(k3_xboole_0(A_178,B_177)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3037,c_3690])).

tff(c_54,plain,(
    k5_relat_1(k6_relat_1('#skF_2'),k6_relat_1('#skF_1')) != k6_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_162,plain,
    ( k7_relat_1(k6_relat_1('#skF_1'),'#skF_2') != k6_relat_1(k3_xboole_0('#skF_1','#skF_2'))
    | ~ v1_relat_1(k6_relat_1('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_146,c_54])).

tff(c_172,plain,(
    k7_relat_1(k6_relat_1('#skF_1'),'#skF_2') != k6_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_162])).

tff(c_4326,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3758,c_172])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:05:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.09/1.97  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.09/1.98  
% 5.09/1.98  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.09/1.98  %$ v5_relat_1 > v4_relat_1 > r1_tarski > v1_relat_1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k8_relat_1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k6_relat_1 > k4_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1
% 5.09/1.98  
% 5.09/1.98  %Foreground sorts:
% 5.09/1.98  
% 5.09/1.98  
% 5.09/1.98  %Background operators:
% 5.09/1.98  
% 5.09/1.98  
% 5.09/1.98  %Foreground operators:
% 5.09/1.98  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 5.09/1.98  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.09/1.98  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 5.09/1.98  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 5.09/1.98  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 5.09/1.98  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.09/1.98  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 5.09/1.98  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.09/1.98  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 5.09/1.98  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 5.09/1.98  tff('#skF_2', type, '#skF_2': $i).
% 5.09/1.98  tff('#skF_1', type, '#skF_1': $i).
% 5.09/1.98  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 5.09/1.98  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 5.09/1.98  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.09/1.98  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.09/1.98  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 5.09/1.98  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.09/1.98  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 5.09/1.98  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.09/1.98  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.09/1.98  tff(k4_relat_1, type, k4_relat_1: $i > $i).
% 5.09/1.98  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 5.09/1.98  
% 5.40/2.00  tff(f_119, axiom, (![A]: ((v1_relat_1(k6_relat_1(A)) & v4_relat_1(k6_relat_1(A), A)) & v5_relat_1(k6_relat_1(A), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc24_relat_1)).
% 5.40/2.00  tff(f_55, axiom, (![A, B]: (v1_relat_1(B) => (k8_relat_1(A, B) = k5_relat_1(B, k6_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t123_relat_1)).
% 5.40/2.00  tff(f_109, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_relat_1)).
% 5.40/2.00  tff(f_41, axiom, (![A, B]: ((v1_relat_1(A) & v1_relat_1(B)) => v1_relat_1(k5_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k5_relat_1)).
% 5.40/2.00  tff(f_93, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 5.40/2.00  tff(f_113, axiom, (![A]: (v1_relat_1(A) => (k7_relat_1(A, k1_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_relat_1)).
% 5.40/2.00  tff(f_45, axiom, (![A, B, C]: (v1_relat_1(C) => (k7_relat_1(k7_relat_1(C, A), B) = k7_relat_1(C, k3_xboole_0(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_relat_1)).
% 5.40/2.00  tff(f_105, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k7_relat_1(B, A)), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t87_relat_1)).
% 5.40/2.00  tff(f_65, axiom, (![A, B, C]: (v1_relat_1(C) => (k7_relat_1(k8_relat_1(A, C), B) = k8_relat_1(A, k7_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t140_relat_1)).
% 5.40/2.00  tff(f_101, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k5_relat_1(B, k6_relat_1(A)), B) & r1_tarski(k5_relat_1(k6_relat_1(A), B), B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t76_relat_1)).
% 5.40/2.00  tff(f_82, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(A, B) => (r1_tarski(k1_relat_1(A), k1_relat_1(B)) & r1_tarski(k2_relat_1(A), k2_relat_1(B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_relat_1)).
% 5.40/2.00  tff(f_61, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k8_relat_1(A, B) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t125_relat_1)).
% 5.40/2.00  tff(f_95, axiom, (![A]: (k4_relat_1(k6_relat_1(A)) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_relat_1)).
% 5.40/2.00  tff(f_89, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k4_relat_1(k5_relat_1(A, B)) = k5_relat_1(k4_relat_1(B), k4_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t54_relat_1)).
% 5.40/2.00  tff(f_122, negated_conjecture, ~(![A, B]: (k5_relat_1(k6_relat_1(B), k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_funct_1)).
% 5.40/2.00  tff(c_48, plain, (![A_49]: (v1_relat_1(k6_relat_1(A_49)))), inference(cnfTransformation, [status(thm)], [f_119])).
% 5.40/2.00  tff(c_203, plain, (![B_82, A_83]: (k5_relat_1(B_82, k6_relat_1(A_83))=k8_relat_1(A_83, B_82) | ~v1_relat_1(B_82))), inference(cnfTransformation, [status(thm)], [f_55])).
% 5.40/2.00  tff(c_44, plain, (![A_46, B_47]: (k5_relat_1(k6_relat_1(A_46), B_47)=k7_relat_1(B_47, A_46) | ~v1_relat_1(B_47))), inference(cnfTransformation, [status(thm)], [f_109])).
% 5.40/2.00  tff(c_210, plain, (![A_83, A_46]: (k8_relat_1(A_83, k6_relat_1(A_46))=k7_relat_1(k6_relat_1(A_83), A_46) | ~v1_relat_1(k6_relat_1(A_83)) | ~v1_relat_1(k6_relat_1(A_46)))), inference(superposition, [status(thm), theory('equality')], [c_203, c_44])).
% 5.40/2.00  tff(c_308, plain, (![A_96, A_97]: (k8_relat_1(A_96, k6_relat_1(A_97))=k7_relat_1(k6_relat_1(A_96), A_97))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_48, c_210])).
% 5.40/2.00  tff(c_12, plain, (![A_17, B_18]: (v1_relat_1(k5_relat_1(A_17, B_18)) | ~v1_relat_1(B_18) | ~v1_relat_1(A_17))), inference(cnfTransformation, [status(thm)], [f_41])).
% 5.40/2.00  tff(c_220, plain, (![A_83, B_82]: (v1_relat_1(k8_relat_1(A_83, B_82)) | ~v1_relat_1(k6_relat_1(A_83)) | ~v1_relat_1(B_82) | ~v1_relat_1(B_82))), inference(superposition, [status(thm), theory('equality')], [c_203, c_12])).
% 5.40/2.00  tff(c_237, plain, (![A_83, B_82]: (v1_relat_1(k8_relat_1(A_83, B_82)) | ~v1_relat_1(B_82))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_220])).
% 5.40/2.00  tff(c_322, plain, (![A_96, A_97]: (v1_relat_1(k7_relat_1(k6_relat_1(A_96), A_97)) | ~v1_relat_1(k6_relat_1(A_97)))), inference(superposition, [status(thm), theory('equality')], [c_308, c_237])).
% 5.40/2.00  tff(c_338, plain, (![A_96, A_97]: (v1_relat_1(k7_relat_1(k6_relat_1(A_96), A_97)))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_322])).
% 5.40/2.00  tff(c_32, plain, (![A_40]: (k1_relat_1(k6_relat_1(A_40))=A_40)), inference(cnfTransformation, [status(thm)], [f_93])).
% 5.40/2.00  tff(c_103, plain, (![A_60]: (k7_relat_1(A_60, k1_relat_1(A_60))=A_60 | ~v1_relat_1(A_60))), inference(cnfTransformation, [status(thm)], [f_113])).
% 5.40/2.00  tff(c_112, plain, (![A_40]: (k7_relat_1(k6_relat_1(A_40), A_40)=k6_relat_1(A_40) | ~v1_relat_1(k6_relat_1(A_40)))), inference(superposition, [status(thm), theory('equality')], [c_32, c_103])).
% 5.40/2.00  tff(c_116, plain, (![A_40]: (k7_relat_1(k6_relat_1(A_40), A_40)=k6_relat_1(A_40))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_112])).
% 5.40/2.00  tff(c_487, plain, (![C_116, A_117, B_118]: (k7_relat_1(k7_relat_1(C_116, A_117), B_118)=k7_relat_1(C_116, k3_xboole_0(A_117, B_118)) | ~v1_relat_1(C_116))), inference(cnfTransformation, [status(thm)], [f_45])).
% 5.40/2.00  tff(c_42, plain, (![B_45, A_44]: (r1_tarski(k1_relat_1(k7_relat_1(B_45, A_44)), A_44) | ~v1_relat_1(B_45))), inference(cnfTransformation, [status(thm)], [f_105])).
% 5.40/2.00  tff(c_2972, plain, (![C_219, A_220, B_221]: (r1_tarski(k1_relat_1(k7_relat_1(C_219, k3_xboole_0(A_220, B_221))), B_221) | ~v1_relat_1(k7_relat_1(C_219, A_220)) | ~v1_relat_1(C_219))), inference(superposition, [status(thm), theory('equality')], [c_487, c_42])).
% 5.40/2.00  tff(c_3020, plain, (![A_220, B_221]: (r1_tarski(k1_relat_1(k6_relat_1(k3_xboole_0(A_220, B_221))), B_221) | ~v1_relat_1(k7_relat_1(k6_relat_1(k3_xboole_0(A_220, B_221)), A_220)) | ~v1_relat_1(k6_relat_1(k3_xboole_0(A_220, B_221))))), inference(superposition, [status(thm), theory('equality')], [c_116, c_2972])).
% 5.40/2.00  tff(c_3037, plain, (![A_220, B_221]: (r1_tarski(k3_xboole_0(A_220, B_221), B_221))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_338, c_32, c_3020])).
% 5.40/2.00  tff(c_233, plain, (![A_83, A_46]: (k8_relat_1(A_83, k6_relat_1(A_46))=k7_relat_1(k6_relat_1(A_83), A_46))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_48, c_210])).
% 5.40/2.00  tff(c_605, plain, (![A_125, C_126, B_127]: (k8_relat_1(A_125, k7_relat_1(C_126, B_127))=k7_relat_1(k8_relat_1(A_125, C_126), B_127) | ~v1_relat_1(C_126))), inference(cnfTransformation, [status(thm)], [f_65])).
% 5.40/2.00  tff(c_637, plain, (![A_125, A_40]: (k7_relat_1(k8_relat_1(A_125, k6_relat_1(A_40)), A_40)=k8_relat_1(A_125, k6_relat_1(A_40)) | ~v1_relat_1(k6_relat_1(A_40)))), inference(superposition, [status(thm), theory('equality')], [c_116, c_605])).
% 5.40/2.00  tff(c_648, plain, (![A_125, A_40]: (k7_relat_1(k7_relat_1(k6_relat_1(A_125), A_40), A_40)=k7_relat_1(k6_relat_1(A_125), A_40))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_233, c_233, c_637])).
% 5.40/2.00  tff(c_14, plain, (![C_21, A_19, B_20]: (k7_relat_1(k7_relat_1(C_21, A_19), B_20)=k7_relat_1(C_21, k3_xboole_0(A_19, B_20)) | ~v1_relat_1(C_21))), inference(cnfTransformation, [status(thm)], [f_45])).
% 5.40/2.00  tff(c_22, plain, (![A_29, C_31, B_30]: (k8_relat_1(A_29, k7_relat_1(C_31, B_30))=k7_relat_1(k8_relat_1(A_29, C_31), B_30) | ~v1_relat_1(C_31))), inference(cnfTransformation, [status(thm)], [f_65])).
% 5.40/2.00  tff(c_146, plain, (![A_73, B_74]: (k5_relat_1(k6_relat_1(A_73), B_74)=k7_relat_1(B_74, A_73) | ~v1_relat_1(B_74))), inference(cnfTransformation, [status(thm)], [f_109])).
% 5.40/2.00  tff(c_40, plain, (![B_43, A_42]: (r1_tarski(k5_relat_1(B_43, k6_relat_1(A_42)), B_43) | ~v1_relat_1(B_43))), inference(cnfTransformation, [status(thm)], [f_101])).
% 5.40/2.00  tff(c_156, plain, (![A_42, A_73]: (r1_tarski(k7_relat_1(k6_relat_1(A_42), A_73), k6_relat_1(A_73)) | ~v1_relat_1(k6_relat_1(A_73)) | ~v1_relat_1(k6_relat_1(A_42)))), inference(superposition, [status(thm), theory('equality')], [c_146, c_40])).
% 5.40/2.00  tff(c_168, plain, (![A_42, A_73]: (r1_tarski(k7_relat_1(k6_relat_1(A_42), A_73), k6_relat_1(A_73)))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_48, c_156])).
% 5.40/2.00  tff(c_34, plain, (![A_40]: (k2_relat_1(k6_relat_1(A_40))=A_40)), inference(cnfTransformation, [status(thm)], [f_93])).
% 5.40/2.00  tff(c_691, plain, (![A_132, B_133]: (r1_tarski(k2_relat_1(A_132), k2_relat_1(B_133)) | ~r1_tarski(A_132, B_133) | ~v1_relat_1(B_133) | ~v1_relat_1(A_132))), inference(cnfTransformation, [status(thm)], [f_82])).
% 5.40/2.00  tff(c_700, plain, (![A_132, A_40]: (r1_tarski(k2_relat_1(A_132), A_40) | ~r1_tarski(A_132, k6_relat_1(A_40)) | ~v1_relat_1(k6_relat_1(A_40)) | ~v1_relat_1(A_132))), inference(superposition, [status(thm), theory('equality')], [c_34, c_691])).
% 5.40/2.00  tff(c_717, plain, (![A_136, A_137]: (r1_tarski(k2_relat_1(A_136), A_137) | ~r1_tarski(A_136, k6_relat_1(A_137)) | ~v1_relat_1(A_136))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_700])).
% 5.40/2.00  tff(c_20, plain, (![A_27, B_28]: (k8_relat_1(A_27, B_28)=B_28 | ~r1_tarski(k2_relat_1(B_28), A_27) | ~v1_relat_1(B_28))), inference(cnfTransformation, [status(thm)], [f_61])).
% 5.40/2.00  tff(c_766, plain, (![A_145, A_146]: (k8_relat_1(A_145, A_146)=A_146 | ~r1_tarski(A_146, k6_relat_1(A_145)) | ~v1_relat_1(A_146))), inference(resolution, [status(thm)], [c_717, c_20])).
% 5.40/2.00  tff(c_797, plain, (![A_73, A_42]: (k8_relat_1(A_73, k7_relat_1(k6_relat_1(A_42), A_73))=k7_relat_1(k6_relat_1(A_42), A_73) | ~v1_relat_1(k7_relat_1(k6_relat_1(A_42), A_73)))), inference(resolution, [status(thm)], [c_168, c_766])).
% 5.40/2.00  tff(c_1495, plain, (![A_165, A_166]: (k8_relat_1(A_165, k7_relat_1(k6_relat_1(A_166), A_165))=k7_relat_1(k6_relat_1(A_166), A_165))), inference(demodulation, [status(thm), theory('equality')], [c_338, c_797])).
% 5.40/2.00  tff(c_1522, plain, (![B_30, A_166]: (k7_relat_1(k8_relat_1(B_30, k6_relat_1(A_166)), B_30)=k7_relat_1(k6_relat_1(A_166), B_30) | ~v1_relat_1(k6_relat_1(A_166)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_1495])).
% 5.40/2.00  tff(c_1661, plain, (![B_171, A_172]: (k7_relat_1(k7_relat_1(k6_relat_1(B_171), A_172), B_171)=k7_relat_1(k6_relat_1(A_172), B_171))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_233, c_1522])).
% 5.40/2.00  tff(c_1710, plain, (![B_20, A_19]: (k7_relat_1(k6_relat_1(B_20), k3_xboole_0(A_19, B_20))=k7_relat_1(k6_relat_1(A_19), B_20) | ~v1_relat_1(k6_relat_1(B_20)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_1661])).
% 5.40/2.00  tff(c_1814, plain, (![B_177, A_178]: (k7_relat_1(k6_relat_1(B_177), k3_xboole_0(A_178, B_177))=k7_relat_1(k6_relat_1(A_178), B_177))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_1710])).
% 5.40/2.00  tff(c_1551, plain, (![B_30, A_166]: (k7_relat_1(k7_relat_1(k6_relat_1(B_30), A_166), B_30)=k7_relat_1(k6_relat_1(A_166), B_30))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_233, c_1522])).
% 5.40/2.00  tff(c_1826, plain, (![A_178, B_177]: (k7_relat_1(k7_relat_1(k6_relat_1(A_178), B_177), B_177)=k7_relat_1(k6_relat_1(k3_xboole_0(A_178, B_177)), B_177))), inference(superposition, [status(thm), theory('equality')], [c_1814, c_1551])).
% 5.40/2.00  tff(c_1893, plain, (![A_178, B_177]: (k7_relat_1(k6_relat_1(k3_xboole_0(A_178, B_177)), B_177)=k7_relat_1(k6_relat_1(A_178), B_177))), inference(demodulation, [status(thm), theory('equality')], [c_648, c_1826])).
% 5.40/2.00  tff(c_36, plain, (![A_41]: (k4_relat_1(k6_relat_1(A_41))=k6_relat_1(A_41))), inference(cnfTransformation, [status(thm)], [f_95])).
% 5.40/2.00  tff(c_245, plain, (![A_88, B_89]: (k8_relat_1(A_88, B_89)=B_89 | ~r1_tarski(k2_relat_1(B_89), A_88) | ~v1_relat_1(B_89))), inference(cnfTransformation, [status(thm)], [f_61])).
% 5.40/2.00  tff(c_252, plain, (![A_88, A_40]: (k8_relat_1(A_88, k6_relat_1(A_40))=k6_relat_1(A_40) | ~r1_tarski(A_40, A_88) | ~v1_relat_1(k6_relat_1(A_40)))), inference(superposition, [status(thm), theory('equality')], [c_34, c_245])).
% 5.40/2.00  tff(c_255, plain, (![A_88, A_40]: (k8_relat_1(A_88, k6_relat_1(A_40))=k6_relat_1(A_40) | ~r1_tarski(A_40, A_88))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_252])).
% 5.40/2.00  tff(c_402, plain, (![A_88, A_40]: (k7_relat_1(k6_relat_1(A_88), A_40)=k6_relat_1(A_40) | ~r1_tarski(A_40, A_88))), inference(demodulation, [status(thm), theory('equality')], [c_233, c_255])).
% 5.40/2.00  tff(c_18, plain, (![B_26, A_25]: (k5_relat_1(B_26, k6_relat_1(A_25))=k8_relat_1(A_25, B_26) | ~v1_relat_1(B_26))), inference(cnfTransformation, [status(thm)], [f_55])).
% 5.40/2.00  tff(c_1361, plain, (![B_160, A_161]: (k5_relat_1(k4_relat_1(B_160), k4_relat_1(A_161))=k4_relat_1(k5_relat_1(A_161, B_160)) | ~v1_relat_1(B_160) | ~v1_relat_1(A_161))), inference(cnfTransformation, [status(thm)], [f_89])).
% 5.40/2.00  tff(c_1373, plain, (![A_41, A_161]: (k5_relat_1(k6_relat_1(A_41), k4_relat_1(A_161))=k4_relat_1(k5_relat_1(A_161, k6_relat_1(A_41))) | ~v1_relat_1(k6_relat_1(A_41)) | ~v1_relat_1(A_161))), inference(superposition, [status(thm), theory('equality')], [c_36, c_1361])).
% 5.40/2.00  tff(c_2011, plain, (![A_181, A_182]: (k5_relat_1(k6_relat_1(A_181), k4_relat_1(A_182))=k4_relat_1(k5_relat_1(A_182, k6_relat_1(A_181))) | ~v1_relat_1(A_182))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_1373])).
% 5.40/2.00  tff(c_2033, plain, (![A_41, A_181]: (k4_relat_1(k5_relat_1(k6_relat_1(A_41), k6_relat_1(A_181)))=k5_relat_1(k6_relat_1(A_181), k6_relat_1(A_41)) | ~v1_relat_1(k6_relat_1(A_41)))), inference(superposition, [status(thm), theory('equality')], [c_36, c_2011])).
% 5.40/2.00  tff(c_2701, plain, (![A_207, A_208]: (k4_relat_1(k5_relat_1(k6_relat_1(A_207), k6_relat_1(A_208)))=k5_relat_1(k6_relat_1(A_208), k6_relat_1(A_207)))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_2033])).
% 5.40/2.00  tff(c_2723, plain, (![A_25, A_207]: (k5_relat_1(k6_relat_1(A_25), k6_relat_1(A_207))=k4_relat_1(k8_relat_1(A_25, k6_relat_1(A_207))) | ~v1_relat_1(k6_relat_1(A_207)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_2701])).
% 5.40/2.00  tff(c_2736, plain, (![A_209, A_210]: (k5_relat_1(k6_relat_1(A_209), k6_relat_1(A_210))=k4_relat_1(k7_relat_1(k6_relat_1(A_209), A_210)))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_233, c_2723])).
% 5.40/2.00  tff(c_2765, plain, (![A_46, A_210]: (k4_relat_1(k7_relat_1(k6_relat_1(A_46), A_210))=k7_relat_1(k6_relat_1(A_210), A_46) | ~v1_relat_1(k6_relat_1(A_210)))), inference(superposition, [status(thm), theory('equality')], [c_44, c_2736])).
% 5.40/2.00  tff(c_2907, plain, (![A_217, A_218]: (k4_relat_1(k7_relat_1(k6_relat_1(A_217), A_218))=k7_relat_1(k6_relat_1(A_218), A_217))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_2765])).
% 5.40/2.00  tff(c_2944, plain, (![A_40, A_88]: (k7_relat_1(k6_relat_1(A_40), A_88)=k4_relat_1(k6_relat_1(A_40)) | ~r1_tarski(A_40, A_88))), inference(superposition, [status(thm), theory('equality')], [c_402, c_2907])).
% 5.40/2.00  tff(c_3554, plain, (![A_239, A_240]: (k7_relat_1(k6_relat_1(A_239), A_240)=k6_relat_1(A_239) | ~r1_tarski(A_239, A_240))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_2944])).
% 5.40/2.00  tff(c_3690, plain, (![A_178, B_177]: (k7_relat_1(k6_relat_1(A_178), B_177)=k6_relat_1(k3_xboole_0(A_178, B_177)) | ~r1_tarski(k3_xboole_0(A_178, B_177), B_177))), inference(superposition, [status(thm), theory('equality')], [c_1893, c_3554])).
% 5.40/2.00  tff(c_3758, plain, (![A_178, B_177]: (k7_relat_1(k6_relat_1(A_178), B_177)=k6_relat_1(k3_xboole_0(A_178, B_177)))), inference(demodulation, [status(thm), theory('equality')], [c_3037, c_3690])).
% 5.40/2.00  tff(c_54, plain, (k5_relat_1(k6_relat_1('#skF_2'), k6_relat_1('#skF_1'))!=k6_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_122])).
% 5.40/2.00  tff(c_162, plain, (k7_relat_1(k6_relat_1('#skF_1'), '#skF_2')!=k6_relat_1(k3_xboole_0('#skF_1', '#skF_2')) | ~v1_relat_1(k6_relat_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_146, c_54])).
% 5.40/2.00  tff(c_172, plain, (k7_relat_1(k6_relat_1('#skF_1'), '#skF_2')!=k6_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_162])).
% 5.40/2.00  tff(c_4326, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3758, c_172])).
% 5.40/2.00  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.40/2.00  
% 5.40/2.00  Inference rules
% 5.40/2.00  ----------------------
% 5.40/2.00  #Ref     : 0
% 5.40/2.00  #Sup     : 909
% 5.40/2.00  #Fact    : 0
% 5.40/2.00  #Define  : 0
% 5.40/2.00  #Split   : 2
% 5.40/2.00  #Chain   : 0
% 5.40/2.00  #Close   : 0
% 5.40/2.00  
% 5.40/2.00  Ordering : KBO
% 5.40/2.00  
% 5.40/2.00  Simplification rules
% 5.40/2.00  ----------------------
% 5.40/2.00  #Subsume      : 70
% 5.40/2.00  #Demod        : 1164
% 5.40/2.00  #Tautology    : 477
% 5.40/2.00  #SimpNegUnit  : 0
% 5.40/2.00  #BackRed      : 44
% 5.40/2.00  
% 5.40/2.00  #Partial instantiations: 0
% 5.40/2.00  #Strategies tried      : 1
% 5.40/2.00  
% 5.40/2.00  Timing (in seconds)
% 5.40/2.00  ----------------------
% 5.40/2.01  Preprocessing        : 0.34
% 5.40/2.01  Parsing              : 0.18
% 5.40/2.01  CNF conversion       : 0.02
% 5.40/2.01  Main loop            : 0.89
% 5.40/2.01  Inferencing          : 0.30
% 5.40/2.01  Reduction            : 0.36
% 5.40/2.01  Demodulation         : 0.28
% 5.40/2.01  BG Simplification    : 0.04
% 5.40/2.01  Subsumption          : 0.14
% 5.40/2.01  Abstraction          : 0.05
% 5.40/2.01  MUC search           : 0.00
% 5.40/2.01  Cooper               : 0.00
% 5.40/2.01  Total                : 1.28
% 5.40/2.01  Index Insertion      : 0.00
% 5.40/2.01  Index Deletion       : 0.00
% 5.40/2.01  Index Matching       : 0.00
% 5.40/2.01  BG Taut test         : 0.00
%------------------------------------------------------------------------------

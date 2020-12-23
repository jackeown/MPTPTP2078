%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:03:34 EST 2020

% Result     : Theorem 4.67s
% Output     : CNFRefutation 4.80s
% Verified   : 
% Statistics : Number of formulae       :   91 (1142 expanded)
%              Number of leaves         :   33 ( 430 expanded)
%              Depth                    :   19
%              Number of atoms          :  129 (2165 expanded)
%              Number of equality atoms :   55 ( 732 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r1_tarski > v1_relat_1 > k2_enumset1 > k1_enumset1 > k8_relat_1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k6_relat_1 > k4_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1

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

tff(f_93,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_117,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v4_relat_1(k6_relat_1(A),A)
      & v5_relat_1(k6_relat_1(A),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc24_relat_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k8_relat_1(A,B) = k5_relat_1(B,k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_relat_1)).

tff(f_107,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k5_relat_1(k6_relat_1(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).

tff(f_95,axiom,(
    ! [A] : k4_relat_1(k6_relat_1(A)) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_relat_1)).

tff(f_79,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k4_relat_1(k5_relat_1(A,B)) = k5_relat_1(k4_relat_1(B),k4_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_relat_1)).

tff(f_111,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k7_relat_1(A,k1_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_relat_1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k7_relat_1(k7_relat_1(C,A),B) = k7_relat_1(C,k3_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_relat_1)).

tff(f_103,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k7_relat_1(B,A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_relat_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_relat_1(B) )
     => v1_relat_1(k5_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k2_relat_1(B),A)
       => k8_relat_1(A,B) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t125_relat_1)).

tff(f_120,negated_conjecture,(
    ~ ! [A,B] : k5_relat_1(k6_relat_1(B),k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_funct_1)).

tff(c_28,plain,(
    ! [A_36] : k1_relat_1(k6_relat_1(A_36)) = A_36 ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_42,plain,(
    ! [A_44] : v1_relat_1(k6_relat_1(A_44)) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_14,plain,(
    ! [B_17,A_16] :
      ( k5_relat_1(B_17,k6_relat_1(A_16)) = k8_relat_1(A_16,B_17)
      | ~ v1_relat_1(B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_218,plain,(
    ! [A_70,B_71] :
      ( k5_relat_1(k6_relat_1(A_70),B_71) = k7_relat_1(B_71,A_70)
      | ~ v1_relat_1(B_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_246,plain,(
    ! [A_16,A_70] :
      ( k8_relat_1(A_16,k6_relat_1(A_70)) = k7_relat_1(k6_relat_1(A_16),A_70)
      | ~ v1_relat_1(k6_relat_1(A_16))
      | ~ v1_relat_1(k6_relat_1(A_70)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_218])).

tff(c_267,plain,(
    ! [A_16,A_70] : k8_relat_1(A_16,k6_relat_1(A_70)) = k7_relat_1(k6_relat_1(A_16),A_70) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_42,c_246])).

tff(c_32,plain,(
    ! [A_37] : k4_relat_1(k6_relat_1(A_37)) = k6_relat_1(A_37) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_1033,plain,(
    ! [B_128,A_129] :
      ( k5_relat_1(k4_relat_1(B_128),k4_relat_1(A_129)) = k4_relat_1(k5_relat_1(A_129,B_128))
      | ~ v1_relat_1(B_128)
      | ~ v1_relat_1(A_129) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_1048,plain,(
    ! [B_128,A_37] :
      ( k5_relat_1(k4_relat_1(B_128),k6_relat_1(A_37)) = k4_relat_1(k5_relat_1(k6_relat_1(A_37),B_128))
      | ~ v1_relat_1(B_128)
      | ~ v1_relat_1(k6_relat_1(A_37)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_1033])).

tff(c_1426,plain,(
    ! [B_145,A_146] :
      ( k5_relat_1(k4_relat_1(B_145),k6_relat_1(A_146)) = k4_relat_1(k5_relat_1(k6_relat_1(A_146),B_145))
      | ~ v1_relat_1(B_145) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_1048])).

tff(c_1456,plain,(
    ! [A_146,A_37] :
      ( k4_relat_1(k5_relat_1(k6_relat_1(A_146),k6_relat_1(A_37))) = k5_relat_1(k6_relat_1(A_37),k6_relat_1(A_146))
      | ~ v1_relat_1(k6_relat_1(A_37)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_1426])).

tff(c_1508,plain,(
    ! [A_151,A_152] : k4_relat_1(k5_relat_1(k6_relat_1(A_151),k6_relat_1(A_152))) = k5_relat_1(k6_relat_1(A_152),k6_relat_1(A_151)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_1456])).

tff(c_1534,plain,(
    ! [A_16,A_151] :
      ( k5_relat_1(k6_relat_1(A_16),k6_relat_1(A_151)) = k4_relat_1(k8_relat_1(A_16,k6_relat_1(A_151)))
      | ~ v1_relat_1(k6_relat_1(A_151)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_1508])).

tff(c_1616,plain,(
    ! [A_157,A_158] : k5_relat_1(k6_relat_1(A_157),k6_relat_1(A_158)) = k4_relat_1(k7_relat_1(k6_relat_1(A_157),A_158)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_267,c_1534])).

tff(c_1653,plain,(
    ! [A_157,A_16] :
      ( k4_relat_1(k7_relat_1(k6_relat_1(A_157),A_16)) = k8_relat_1(A_16,k6_relat_1(A_157))
      | ~ v1_relat_1(k6_relat_1(A_157)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_1616])).

tff(c_1679,plain,(
    ! [A_157,A_16] : k4_relat_1(k7_relat_1(k6_relat_1(A_157),A_16)) = k7_relat_1(k6_relat_1(A_16),A_157) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_267,c_1653])).

tff(c_40,plain,(
    ! [A_43] :
      ( k7_relat_1(A_43,k1_relat_1(A_43)) = A_43
      | ~ v1_relat_1(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_451,plain,(
    ! [C_92,A_93,B_94] :
      ( k7_relat_1(k7_relat_1(C_92,A_93),B_94) = k7_relat_1(C_92,k3_xboole_0(A_93,B_94))
      | ~ v1_relat_1(C_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_2062,plain,(
    ! [A_169,B_170] :
      ( k7_relat_1(A_169,k3_xboole_0(k1_relat_1(A_169),B_170)) = k7_relat_1(A_169,B_170)
      | ~ v1_relat_1(A_169)
      | ~ v1_relat_1(A_169) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_451])).

tff(c_2069,plain,(
    ! [A_157,B_170] :
      ( k7_relat_1(k6_relat_1(k3_xboole_0(k1_relat_1(k6_relat_1(A_157)),B_170)),A_157) = k4_relat_1(k7_relat_1(k6_relat_1(A_157),B_170))
      | ~ v1_relat_1(k6_relat_1(A_157))
      | ~ v1_relat_1(k6_relat_1(A_157)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2062,c_1679])).

tff(c_2302,plain,(
    ! [A_173,B_174] : k7_relat_1(k6_relat_1(k3_xboole_0(A_173,B_174)),A_173) = k7_relat_1(k6_relat_1(B_174),A_173) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_42,c_1679,c_28,c_2069])).

tff(c_36,plain,(
    ! [B_40,A_39] :
      ( r1_tarski(k7_relat_1(B_40,A_39),B_40)
      | ~ v1_relat_1(B_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_2352,plain,(
    ! [B_174,A_173] :
      ( r1_tarski(k7_relat_1(k6_relat_1(B_174),A_173),k6_relat_1(k3_xboole_0(A_173,B_174)))
      | ~ v1_relat_1(k6_relat_1(k3_xboole_0(A_173,B_174))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2302,c_36])).

tff(c_2381,plain,(
    ! [B_174,A_173] : r1_tarski(k7_relat_1(k6_relat_1(B_174),A_173),k6_relat_1(k3_xboole_0(A_173,B_174))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_2352])).

tff(c_282,plain,(
    ! [A_74,A_75] : k8_relat_1(A_74,k6_relat_1(A_75)) = k7_relat_1(k6_relat_1(A_74),A_75) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_42,c_246])).

tff(c_165,plain,(
    ! [B_65,A_66] :
      ( k5_relat_1(B_65,k6_relat_1(A_66)) = k8_relat_1(A_66,B_65)
      | ~ v1_relat_1(B_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_8,plain,(
    ! [A_8,B_9] :
      ( v1_relat_1(k5_relat_1(A_8,B_9))
      | ~ v1_relat_1(B_9)
      | ~ v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_175,plain,(
    ! [A_66,B_65] :
      ( v1_relat_1(k8_relat_1(A_66,B_65))
      | ~ v1_relat_1(k6_relat_1(A_66))
      | ~ v1_relat_1(B_65)
      | ~ v1_relat_1(B_65) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_165,c_8])).

tff(c_196,plain,(
    ! [A_66,B_65] :
      ( v1_relat_1(k8_relat_1(A_66,B_65))
      | ~ v1_relat_1(B_65) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_175])).

tff(c_292,plain,(
    ! [A_74,A_75] :
      ( v1_relat_1(k7_relat_1(k6_relat_1(A_74),A_75))
      | ~ v1_relat_1(k6_relat_1(A_75)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_282,c_196])).

tff(c_302,plain,(
    ! [A_74,A_75] : v1_relat_1(k7_relat_1(k6_relat_1(A_74),A_75)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_292])).

tff(c_2153,plain,(
    ! [A_157,B_170] : k7_relat_1(k6_relat_1(k3_xboole_0(A_157,B_170)),A_157) = k7_relat_1(k6_relat_1(B_170),A_157) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_42,c_1679,c_28,c_2069])).

tff(c_98,plain,(
    ! [A_57] :
      ( k7_relat_1(A_57,k1_relat_1(A_57)) = A_57
      | ~ v1_relat_1(A_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_110,plain,(
    ! [A_36] :
      ( k7_relat_1(k6_relat_1(A_36),A_36) = k6_relat_1(A_36)
      | ~ v1_relat_1(k6_relat_1(A_36)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_98])).

tff(c_114,plain,(
    ! [A_36] : k7_relat_1(k6_relat_1(A_36),A_36) = k6_relat_1(A_36) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_110])).

tff(c_2888,plain,(
    ! [C_201,A_202,B_203] :
      ( r1_tarski(k7_relat_1(C_201,k3_xboole_0(A_202,B_203)),k7_relat_1(C_201,A_202))
      | ~ v1_relat_1(k7_relat_1(C_201,A_202))
      | ~ v1_relat_1(C_201) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_451,c_36])).

tff(c_2954,plain,(
    ! [A_202,B_203] :
      ( r1_tarski(k6_relat_1(k3_xboole_0(A_202,B_203)),k7_relat_1(k6_relat_1(k3_xboole_0(A_202,B_203)),A_202))
      | ~ v1_relat_1(k7_relat_1(k6_relat_1(k3_xboole_0(A_202,B_203)),A_202))
      | ~ v1_relat_1(k6_relat_1(k3_xboole_0(A_202,B_203))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_114,c_2888])).

tff(c_2987,plain,(
    ! [A_204,B_205] : r1_tarski(k6_relat_1(k3_xboole_0(A_204,B_205)),k7_relat_1(k6_relat_1(B_205),A_204)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_302,c_2153,c_2954])).

tff(c_30,plain,(
    ! [A_36] : k2_relat_1(k6_relat_1(A_36)) = A_36 ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_354,plain,(
    ! [A_82,B_83] :
      ( k8_relat_1(A_82,B_83) = B_83
      | ~ r1_tarski(k2_relat_1(B_83),A_82)
      | ~ v1_relat_1(B_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_361,plain,(
    ! [A_82,A_36] :
      ( k8_relat_1(A_82,k6_relat_1(A_36)) = k6_relat_1(A_36)
      | ~ r1_tarski(A_36,A_82)
      | ~ v1_relat_1(k6_relat_1(A_36)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_354])).

tff(c_364,plain,(
    ! [A_82,A_36] :
      ( k7_relat_1(k6_relat_1(A_82),A_36) = k6_relat_1(A_36)
      | ~ r1_tarski(A_36,A_82) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_267,c_361])).

tff(c_1715,plain,(
    ! [A_161,A_162] : k4_relat_1(k7_relat_1(k6_relat_1(A_161),A_162)) = k7_relat_1(k6_relat_1(A_162),A_161) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_267,c_1653])).

tff(c_1745,plain,(
    ! [A_36,A_82] :
      ( k7_relat_1(k6_relat_1(A_36),A_82) = k4_relat_1(k6_relat_1(A_36))
      | ~ r1_tarski(A_36,A_82) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_364,c_1715])).

tff(c_2178,plain,(
    ! [A_171,A_172] :
      ( k7_relat_1(k6_relat_1(A_171),A_172) = k6_relat_1(A_171)
      | ~ r1_tarski(A_171,A_172) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_1745])).

tff(c_2225,plain,(
    ! [A_172,A_171] :
      ( k6_relat_1(A_172) = k6_relat_1(A_171)
      | ~ r1_tarski(A_172,A_171)
      | ~ r1_tarski(A_171,A_172) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2178,c_364])).

tff(c_2989,plain,(
    ! [B_205,A_204] :
      ( k6_relat_1(k7_relat_1(k6_relat_1(B_205),A_204)) = k6_relat_1(k6_relat_1(k3_xboole_0(A_204,B_205)))
      | ~ r1_tarski(k7_relat_1(k6_relat_1(B_205),A_204),k6_relat_1(k3_xboole_0(A_204,B_205))) ) ),
    inference(resolution,[status(thm)],[c_2987,c_2225])).

tff(c_3203,plain,(
    ! [B_218,A_219] : k6_relat_1(k7_relat_1(k6_relat_1(B_218),A_219)) = k6_relat_1(k6_relat_1(k3_xboole_0(A_219,B_218))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2381,c_2989])).

tff(c_3344,plain,(
    ! [A_219,B_218] : k1_relat_1(k6_relat_1(k6_relat_1(k3_xboole_0(A_219,B_218)))) = k7_relat_1(k6_relat_1(B_218),A_219) ),
    inference(superposition,[status(thm),theory(equality)],[c_3203,c_28])).

tff(c_3403,plain,(
    ! [B_218,A_219] : k7_relat_1(k6_relat_1(B_218),A_219) = k6_relat_1(k3_xboole_0(A_219,B_218)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_3344])).

tff(c_4524,plain,(
    ! [A_251,A_252] : k4_relat_1(k6_relat_1(k3_xboole_0(A_251,A_252))) = k6_relat_1(k3_xboole_0(A_252,A_251)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3403,c_3403,c_1679])).

tff(c_4542,plain,(
    ! [A_252,A_251] : k6_relat_1(k3_xboole_0(A_252,A_251)) = k6_relat_1(k3_xboole_0(A_251,A_252)) ),
    inference(superposition,[status(thm),theory(equality)],[c_4524,c_32])).

tff(c_48,plain,(
    k5_relat_1(k6_relat_1('#skF_2'),k6_relat_1('#skF_1')) != k6_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_182,plain,
    ( k8_relat_1('#skF_1',k6_relat_1('#skF_2')) != k6_relat_1(k3_xboole_0('#skF_1','#skF_2'))
    | ~ v1_relat_1(k6_relat_1('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_165,c_48])).

tff(c_198,plain,(
    k8_relat_1('#skF_1',k6_relat_1('#skF_2')) != k6_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_182])).

tff(c_281,plain,(
    k7_relat_1(k6_relat_1('#skF_1'),'#skF_2') != k6_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_267,c_198])).

tff(c_3540,plain,(
    k6_relat_1(k3_xboole_0('#skF_2','#skF_1')) != k6_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3403,c_281])).

tff(c_4581,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4542,c_3540])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 17:28:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.67/1.84  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.67/1.85  
% 4.67/1.85  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.67/1.85  %$ v5_relat_1 > v4_relat_1 > r1_tarski > v1_relat_1 > k2_enumset1 > k1_enumset1 > k8_relat_1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k6_relat_1 > k4_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1
% 4.67/1.85  
% 4.67/1.85  %Foreground sorts:
% 4.67/1.85  
% 4.67/1.85  
% 4.67/1.85  %Background operators:
% 4.67/1.85  
% 4.67/1.85  
% 4.67/1.85  %Foreground operators:
% 4.67/1.85  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 4.67/1.85  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.67/1.85  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 4.67/1.85  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 4.67/1.85  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.67/1.85  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.67/1.85  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.67/1.85  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.67/1.85  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.67/1.85  tff('#skF_2', type, '#skF_2': $i).
% 4.67/1.85  tff('#skF_1', type, '#skF_1': $i).
% 4.67/1.85  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 4.67/1.85  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.67/1.85  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.67/1.85  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 4.67/1.85  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.67/1.85  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 4.67/1.85  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.67/1.85  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.67/1.85  tff(k4_relat_1, type, k4_relat_1: $i > $i).
% 4.67/1.85  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 4.67/1.85  
% 4.80/1.87  tff(f_93, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 4.80/1.87  tff(f_117, axiom, (![A]: ((v1_relat_1(k6_relat_1(A)) & v4_relat_1(k6_relat_1(A), A)) & v5_relat_1(k6_relat_1(A), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc24_relat_1)).
% 4.80/1.87  tff(f_51, axiom, (![A, B]: (v1_relat_1(B) => (k8_relat_1(A, B) = k5_relat_1(B, k6_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t123_relat_1)).
% 4.80/1.87  tff(f_107, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_relat_1)).
% 4.80/1.87  tff(f_95, axiom, (![A]: (k4_relat_1(k6_relat_1(A)) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_relat_1)).
% 4.80/1.87  tff(f_79, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k4_relat_1(k5_relat_1(A, B)) = k5_relat_1(k4_relat_1(B), k4_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t54_relat_1)).
% 4.80/1.87  tff(f_111, axiom, (![A]: (v1_relat_1(A) => (k7_relat_1(A, k1_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_relat_1)).
% 4.80/1.87  tff(f_41, axiom, (![A, B, C]: (v1_relat_1(C) => (k7_relat_1(k7_relat_1(C, A), B) = k7_relat_1(C, k3_xboole_0(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_relat_1)).
% 4.80/1.87  tff(f_103, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k7_relat_1(B, A), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t88_relat_1)).
% 4.80/1.87  tff(f_37, axiom, (![A, B]: ((v1_relat_1(A) & v1_relat_1(B)) => v1_relat_1(k5_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k5_relat_1)).
% 4.80/1.87  tff(f_57, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k8_relat_1(A, B) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t125_relat_1)).
% 4.80/1.87  tff(f_120, negated_conjecture, ~(![A, B]: (k5_relat_1(k6_relat_1(B), k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_funct_1)).
% 4.80/1.87  tff(c_28, plain, (![A_36]: (k1_relat_1(k6_relat_1(A_36))=A_36)), inference(cnfTransformation, [status(thm)], [f_93])).
% 4.80/1.87  tff(c_42, plain, (![A_44]: (v1_relat_1(k6_relat_1(A_44)))), inference(cnfTransformation, [status(thm)], [f_117])).
% 4.80/1.87  tff(c_14, plain, (![B_17, A_16]: (k5_relat_1(B_17, k6_relat_1(A_16))=k8_relat_1(A_16, B_17) | ~v1_relat_1(B_17))), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.80/1.87  tff(c_218, plain, (![A_70, B_71]: (k5_relat_1(k6_relat_1(A_70), B_71)=k7_relat_1(B_71, A_70) | ~v1_relat_1(B_71))), inference(cnfTransformation, [status(thm)], [f_107])).
% 4.80/1.87  tff(c_246, plain, (![A_16, A_70]: (k8_relat_1(A_16, k6_relat_1(A_70))=k7_relat_1(k6_relat_1(A_16), A_70) | ~v1_relat_1(k6_relat_1(A_16)) | ~v1_relat_1(k6_relat_1(A_70)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_218])).
% 4.80/1.87  tff(c_267, plain, (![A_16, A_70]: (k8_relat_1(A_16, k6_relat_1(A_70))=k7_relat_1(k6_relat_1(A_16), A_70))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_42, c_246])).
% 4.80/1.87  tff(c_32, plain, (![A_37]: (k4_relat_1(k6_relat_1(A_37))=k6_relat_1(A_37))), inference(cnfTransformation, [status(thm)], [f_95])).
% 4.80/1.87  tff(c_1033, plain, (![B_128, A_129]: (k5_relat_1(k4_relat_1(B_128), k4_relat_1(A_129))=k4_relat_1(k5_relat_1(A_129, B_128)) | ~v1_relat_1(B_128) | ~v1_relat_1(A_129))), inference(cnfTransformation, [status(thm)], [f_79])).
% 4.80/1.87  tff(c_1048, plain, (![B_128, A_37]: (k5_relat_1(k4_relat_1(B_128), k6_relat_1(A_37))=k4_relat_1(k5_relat_1(k6_relat_1(A_37), B_128)) | ~v1_relat_1(B_128) | ~v1_relat_1(k6_relat_1(A_37)))), inference(superposition, [status(thm), theory('equality')], [c_32, c_1033])).
% 4.80/1.87  tff(c_1426, plain, (![B_145, A_146]: (k5_relat_1(k4_relat_1(B_145), k6_relat_1(A_146))=k4_relat_1(k5_relat_1(k6_relat_1(A_146), B_145)) | ~v1_relat_1(B_145))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_1048])).
% 4.80/1.87  tff(c_1456, plain, (![A_146, A_37]: (k4_relat_1(k5_relat_1(k6_relat_1(A_146), k6_relat_1(A_37)))=k5_relat_1(k6_relat_1(A_37), k6_relat_1(A_146)) | ~v1_relat_1(k6_relat_1(A_37)))), inference(superposition, [status(thm), theory('equality')], [c_32, c_1426])).
% 4.80/1.87  tff(c_1508, plain, (![A_151, A_152]: (k4_relat_1(k5_relat_1(k6_relat_1(A_151), k6_relat_1(A_152)))=k5_relat_1(k6_relat_1(A_152), k6_relat_1(A_151)))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_1456])).
% 4.80/1.87  tff(c_1534, plain, (![A_16, A_151]: (k5_relat_1(k6_relat_1(A_16), k6_relat_1(A_151))=k4_relat_1(k8_relat_1(A_16, k6_relat_1(A_151))) | ~v1_relat_1(k6_relat_1(A_151)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_1508])).
% 4.80/1.87  tff(c_1616, plain, (![A_157, A_158]: (k5_relat_1(k6_relat_1(A_157), k6_relat_1(A_158))=k4_relat_1(k7_relat_1(k6_relat_1(A_157), A_158)))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_267, c_1534])).
% 4.80/1.87  tff(c_1653, plain, (![A_157, A_16]: (k4_relat_1(k7_relat_1(k6_relat_1(A_157), A_16))=k8_relat_1(A_16, k6_relat_1(A_157)) | ~v1_relat_1(k6_relat_1(A_157)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_1616])).
% 4.80/1.87  tff(c_1679, plain, (![A_157, A_16]: (k4_relat_1(k7_relat_1(k6_relat_1(A_157), A_16))=k7_relat_1(k6_relat_1(A_16), A_157))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_267, c_1653])).
% 4.80/1.87  tff(c_40, plain, (![A_43]: (k7_relat_1(A_43, k1_relat_1(A_43))=A_43 | ~v1_relat_1(A_43))), inference(cnfTransformation, [status(thm)], [f_111])).
% 4.80/1.87  tff(c_451, plain, (![C_92, A_93, B_94]: (k7_relat_1(k7_relat_1(C_92, A_93), B_94)=k7_relat_1(C_92, k3_xboole_0(A_93, B_94)) | ~v1_relat_1(C_92))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.80/1.87  tff(c_2062, plain, (![A_169, B_170]: (k7_relat_1(A_169, k3_xboole_0(k1_relat_1(A_169), B_170))=k7_relat_1(A_169, B_170) | ~v1_relat_1(A_169) | ~v1_relat_1(A_169))), inference(superposition, [status(thm), theory('equality')], [c_40, c_451])).
% 4.80/1.87  tff(c_2069, plain, (![A_157, B_170]: (k7_relat_1(k6_relat_1(k3_xboole_0(k1_relat_1(k6_relat_1(A_157)), B_170)), A_157)=k4_relat_1(k7_relat_1(k6_relat_1(A_157), B_170)) | ~v1_relat_1(k6_relat_1(A_157)) | ~v1_relat_1(k6_relat_1(A_157)))), inference(superposition, [status(thm), theory('equality')], [c_2062, c_1679])).
% 4.80/1.87  tff(c_2302, plain, (![A_173, B_174]: (k7_relat_1(k6_relat_1(k3_xboole_0(A_173, B_174)), A_173)=k7_relat_1(k6_relat_1(B_174), A_173))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_42, c_1679, c_28, c_2069])).
% 4.80/1.87  tff(c_36, plain, (![B_40, A_39]: (r1_tarski(k7_relat_1(B_40, A_39), B_40) | ~v1_relat_1(B_40))), inference(cnfTransformation, [status(thm)], [f_103])).
% 4.80/1.87  tff(c_2352, plain, (![B_174, A_173]: (r1_tarski(k7_relat_1(k6_relat_1(B_174), A_173), k6_relat_1(k3_xboole_0(A_173, B_174))) | ~v1_relat_1(k6_relat_1(k3_xboole_0(A_173, B_174))))), inference(superposition, [status(thm), theory('equality')], [c_2302, c_36])).
% 4.80/1.87  tff(c_2381, plain, (![B_174, A_173]: (r1_tarski(k7_relat_1(k6_relat_1(B_174), A_173), k6_relat_1(k3_xboole_0(A_173, B_174))))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_2352])).
% 4.80/1.87  tff(c_282, plain, (![A_74, A_75]: (k8_relat_1(A_74, k6_relat_1(A_75))=k7_relat_1(k6_relat_1(A_74), A_75))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_42, c_246])).
% 4.80/1.87  tff(c_165, plain, (![B_65, A_66]: (k5_relat_1(B_65, k6_relat_1(A_66))=k8_relat_1(A_66, B_65) | ~v1_relat_1(B_65))), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.80/1.87  tff(c_8, plain, (![A_8, B_9]: (v1_relat_1(k5_relat_1(A_8, B_9)) | ~v1_relat_1(B_9) | ~v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.80/1.87  tff(c_175, plain, (![A_66, B_65]: (v1_relat_1(k8_relat_1(A_66, B_65)) | ~v1_relat_1(k6_relat_1(A_66)) | ~v1_relat_1(B_65) | ~v1_relat_1(B_65))), inference(superposition, [status(thm), theory('equality')], [c_165, c_8])).
% 4.80/1.87  tff(c_196, plain, (![A_66, B_65]: (v1_relat_1(k8_relat_1(A_66, B_65)) | ~v1_relat_1(B_65))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_175])).
% 4.80/1.87  tff(c_292, plain, (![A_74, A_75]: (v1_relat_1(k7_relat_1(k6_relat_1(A_74), A_75)) | ~v1_relat_1(k6_relat_1(A_75)))), inference(superposition, [status(thm), theory('equality')], [c_282, c_196])).
% 4.80/1.87  tff(c_302, plain, (![A_74, A_75]: (v1_relat_1(k7_relat_1(k6_relat_1(A_74), A_75)))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_292])).
% 4.80/1.87  tff(c_2153, plain, (![A_157, B_170]: (k7_relat_1(k6_relat_1(k3_xboole_0(A_157, B_170)), A_157)=k7_relat_1(k6_relat_1(B_170), A_157))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_42, c_1679, c_28, c_2069])).
% 4.80/1.87  tff(c_98, plain, (![A_57]: (k7_relat_1(A_57, k1_relat_1(A_57))=A_57 | ~v1_relat_1(A_57))), inference(cnfTransformation, [status(thm)], [f_111])).
% 4.80/1.87  tff(c_110, plain, (![A_36]: (k7_relat_1(k6_relat_1(A_36), A_36)=k6_relat_1(A_36) | ~v1_relat_1(k6_relat_1(A_36)))), inference(superposition, [status(thm), theory('equality')], [c_28, c_98])).
% 4.80/1.87  tff(c_114, plain, (![A_36]: (k7_relat_1(k6_relat_1(A_36), A_36)=k6_relat_1(A_36))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_110])).
% 4.80/1.87  tff(c_2888, plain, (![C_201, A_202, B_203]: (r1_tarski(k7_relat_1(C_201, k3_xboole_0(A_202, B_203)), k7_relat_1(C_201, A_202)) | ~v1_relat_1(k7_relat_1(C_201, A_202)) | ~v1_relat_1(C_201))), inference(superposition, [status(thm), theory('equality')], [c_451, c_36])).
% 4.80/1.87  tff(c_2954, plain, (![A_202, B_203]: (r1_tarski(k6_relat_1(k3_xboole_0(A_202, B_203)), k7_relat_1(k6_relat_1(k3_xboole_0(A_202, B_203)), A_202)) | ~v1_relat_1(k7_relat_1(k6_relat_1(k3_xboole_0(A_202, B_203)), A_202)) | ~v1_relat_1(k6_relat_1(k3_xboole_0(A_202, B_203))))), inference(superposition, [status(thm), theory('equality')], [c_114, c_2888])).
% 4.80/1.87  tff(c_2987, plain, (![A_204, B_205]: (r1_tarski(k6_relat_1(k3_xboole_0(A_204, B_205)), k7_relat_1(k6_relat_1(B_205), A_204)))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_302, c_2153, c_2954])).
% 4.80/1.87  tff(c_30, plain, (![A_36]: (k2_relat_1(k6_relat_1(A_36))=A_36)), inference(cnfTransformation, [status(thm)], [f_93])).
% 4.80/1.87  tff(c_354, plain, (![A_82, B_83]: (k8_relat_1(A_82, B_83)=B_83 | ~r1_tarski(k2_relat_1(B_83), A_82) | ~v1_relat_1(B_83))), inference(cnfTransformation, [status(thm)], [f_57])).
% 4.80/1.87  tff(c_361, plain, (![A_82, A_36]: (k8_relat_1(A_82, k6_relat_1(A_36))=k6_relat_1(A_36) | ~r1_tarski(A_36, A_82) | ~v1_relat_1(k6_relat_1(A_36)))), inference(superposition, [status(thm), theory('equality')], [c_30, c_354])).
% 4.80/1.87  tff(c_364, plain, (![A_82, A_36]: (k7_relat_1(k6_relat_1(A_82), A_36)=k6_relat_1(A_36) | ~r1_tarski(A_36, A_82))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_267, c_361])).
% 4.80/1.87  tff(c_1715, plain, (![A_161, A_162]: (k4_relat_1(k7_relat_1(k6_relat_1(A_161), A_162))=k7_relat_1(k6_relat_1(A_162), A_161))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_267, c_1653])).
% 4.80/1.87  tff(c_1745, plain, (![A_36, A_82]: (k7_relat_1(k6_relat_1(A_36), A_82)=k4_relat_1(k6_relat_1(A_36)) | ~r1_tarski(A_36, A_82))), inference(superposition, [status(thm), theory('equality')], [c_364, c_1715])).
% 4.80/1.87  tff(c_2178, plain, (![A_171, A_172]: (k7_relat_1(k6_relat_1(A_171), A_172)=k6_relat_1(A_171) | ~r1_tarski(A_171, A_172))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_1745])).
% 4.80/1.87  tff(c_2225, plain, (![A_172, A_171]: (k6_relat_1(A_172)=k6_relat_1(A_171) | ~r1_tarski(A_172, A_171) | ~r1_tarski(A_171, A_172))), inference(superposition, [status(thm), theory('equality')], [c_2178, c_364])).
% 4.80/1.87  tff(c_2989, plain, (![B_205, A_204]: (k6_relat_1(k7_relat_1(k6_relat_1(B_205), A_204))=k6_relat_1(k6_relat_1(k3_xboole_0(A_204, B_205))) | ~r1_tarski(k7_relat_1(k6_relat_1(B_205), A_204), k6_relat_1(k3_xboole_0(A_204, B_205))))), inference(resolution, [status(thm)], [c_2987, c_2225])).
% 4.80/1.87  tff(c_3203, plain, (![B_218, A_219]: (k6_relat_1(k7_relat_1(k6_relat_1(B_218), A_219))=k6_relat_1(k6_relat_1(k3_xboole_0(A_219, B_218))))), inference(demodulation, [status(thm), theory('equality')], [c_2381, c_2989])).
% 4.80/1.87  tff(c_3344, plain, (![A_219, B_218]: (k1_relat_1(k6_relat_1(k6_relat_1(k3_xboole_0(A_219, B_218))))=k7_relat_1(k6_relat_1(B_218), A_219))), inference(superposition, [status(thm), theory('equality')], [c_3203, c_28])).
% 4.80/1.87  tff(c_3403, plain, (![B_218, A_219]: (k7_relat_1(k6_relat_1(B_218), A_219)=k6_relat_1(k3_xboole_0(A_219, B_218)))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_3344])).
% 4.80/1.87  tff(c_4524, plain, (![A_251, A_252]: (k4_relat_1(k6_relat_1(k3_xboole_0(A_251, A_252)))=k6_relat_1(k3_xboole_0(A_252, A_251)))), inference(demodulation, [status(thm), theory('equality')], [c_3403, c_3403, c_1679])).
% 4.80/1.87  tff(c_4542, plain, (![A_252, A_251]: (k6_relat_1(k3_xboole_0(A_252, A_251))=k6_relat_1(k3_xboole_0(A_251, A_252)))), inference(superposition, [status(thm), theory('equality')], [c_4524, c_32])).
% 4.80/1.87  tff(c_48, plain, (k5_relat_1(k6_relat_1('#skF_2'), k6_relat_1('#skF_1'))!=k6_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_120])).
% 4.80/1.87  tff(c_182, plain, (k8_relat_1('#skF_1', k6_relat_1('#skF_2'))!=k6_relat_1(k3_xboole_0('#skF_1', '#skF_2')) | ~v1_relat_1(k6_relat_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_165, c_48])).
% 4.80/1.87  tff(c_198, plain, (k8_relat_1('#skF_1', k6_relat_1('#skF_2'))!=k6_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_182])).
% 4.80/1.87  tff(c_281, plain, (k7_relat_1(k6_relat_1('#skF_1'), '#skF_2')!=k6_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_267, c_198])).
% 4.80/1.87  tff(c_3540, plain, (k6_relat_1(k3_xboole_0('#skF_2', '#skF_1'))!=k6_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_3403, c_281])).
% 4.80/1.87  tff(c_4581, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4542, c_3540])).
% 4.80/1.87  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.80/1.87  
% 4.80/1.87  Inference rules
% 4.80/1.87  ----------------------
% 4.80/1.87  #Ref     : 0
% 4.80/1.87  #Sup     : 1019
% 4.80/1.87  #Fact    : 0
% 4.80/1.87  #Define  : 0
% 4.80/1.87  #Split   : 2
% 4.80/1.87  #Chain   : 0
% 4.80/1.87  #Close   : 0
% 4.80/1.87  
% 4.80/1.87  Ordering : KBO
% 4.80/1.87  
% 4.80/1.87  Simplification rules
% 4.80/1.87  ----------------------
% 4.80/1.87  #Subsume      : 85
% 4.80/1.87  #Demod        : 1185
% 4.80/1.87  #Tautology    : 461
% 4.80/1.87  #SimpNegUnit  : 0
% 4.80/1.87  #BackRed      : 31
% 4.80/1.87  
% 4.80/1.87  #Partial instantiations: 0
% 4.80/1.87  #Strategies tried      : 1
% 4.80/1.87  
% 4.80/1.87  Timing (in seconds)
% 4.80/1.87  ----------------------
% 4.80/1.87  Preprocessing        : 0.32
% 4.80/1.87  Parsing              : 0.17
% 4.80/1.87  CNF conversion       : 0.02
% 4.80/1.87  Main loop            : 0.78
% 4.80/1.87  Inferencing          : 0.28
% 4.80/1.87  Reduction            : 0.29
% 4.80/1.87  Demodulation         : 0.22
% 4.80/1.87  BG Simplification    : 0.04
% 4.80/1.87  Subsumption          : 0.12
% 4.80/1.87  Abstraction          : 0.05
% 4.80/1.87  MUC search           : 0.00
% 4.80/1.87  Cooper               : 0.00
% 4.80/1.87  Total                : 1.13
% 4.80/1.87  Index Insertion      : 0.00
% 4.80/1.87  Index Deletion       : 0.00
% 4.80/1.87  Index Matching       : 0.00
% 4.80/1.87  BG Taut test         : 0.00
%------------------------------------------------------------------------------

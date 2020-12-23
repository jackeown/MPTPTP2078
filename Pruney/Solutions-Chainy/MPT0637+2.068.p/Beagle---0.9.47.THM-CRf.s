%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:03:33 EST 2020

% Result     : Theorem 31.37s
% Output     : CNFRefutation 31.37s
% Verified   : 
% Statistics : Number of formulae       :  158 (2331 expanded)
%              Number of leaves         :   39 ( 822 expanded)
%              Depth                    :   21
%              Number of atoms          :  286 (3823 expanded)
%              Number of equality atoms :  101 (1515 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k6_relat_1 > k4_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
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

tff(f_51,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_86,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_58,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k2_relat_1(k5_relat_1(A,B)) = k9_relat_1(B,k2_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t160_relat_1)).

tff(f_65,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => r1_tarski(k2_relat_1(k5_relat_1(A,B)),k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_relat_1)).

tff(f_94,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k5_relat_1(k6_relat_1(A),B) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_relat_1)).

tff(f_112,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k5_relat_1(k6_relat_1(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).

tff(f_108,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k1_relat_1(k7_relat_1(B,A)) = k3_xboole_0(k1_relat_1(B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_relat_1)).

tff(f_27,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_88,axiom,(
    ! [A] : k4_relat_1(k6_relat_1(A)) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_relat_1)).

tff(f_72,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k4_relat_1(k5_relat_1(A,B)) = k5_relat_1(k4_relat_1(B),k4_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t54_relat_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_relat_1(B) )
     => v1_relat_1(k5_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).

tff(f_104,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k5_relat_1(A,k6_relat_1(k2_relat_1(A))) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_relat_1)).

tff(f_100,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k2_relat_1(B),A)
       => k5_relat_1(B,k6_relat_1(A)) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_relat_1)).

tff(f_82,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ! [C] :
              ( v1_relat_1(C)
             => k5_relat_1(k5_relat_1(A,B),C) = k5_relat_1(A,k5_relat_1(B,C)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_relat_1)).

tff(f_115,negated_conjecture,(
    ~ ! [A,B] : k5_relat_1(k6_relat_1(B),k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_funct_1)).

tff(c_22,plain,(
    ! [A_36] : v1_relat_1(k6_relat_1(A_36)) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_34,plain,(
    ! [A_53] : k2_relat_1(k6_relat_1(A_53)) = A_53 ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_811,plain,(
    ! [B_128,A_129] :
      ( k9_relat_1(B_128,k2_relat_1(A_129)) = k2_relat_1(k5_relat_1(A_129,B_128))
      | ~ v1_relat_1(B_128)
      | ~ v1_relat_1(A_129) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_820,plain,(
    ! [A_53,B_128] :
      ( k2_relat_1(k5_relat_1(k6_relat_1(A_53),B_128)) = k9_relat_1(B_128,A_53)
      | ~ v1_relat_1(B_128)
      | ~ v1_relat_1(k6_relat_1(A_53)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_811])).

tff(c_1083,plain,(
    ! [A_143,B_144] :
      ( k2_relat_1(k5_relat_1(k6_relat_1(A_143),B_144)) = k9_relat_1(B_144,A_143)
      | ~ v1_relat_1(B_144) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_820])).

tff(c_287,plain,(
    ! [A_96,B_97] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_96,B_97)),k2_relat_1(B_97))
      | ~ v1_relat_1(B_97)
      | ~ v1_relat_1(A_96) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_299,plain,(
    ! [A_96,A_53] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_96,k6_relat_1(A_53))),A_53)
      | ~ v1_relat_1(k6_relat_1(A_53))
      | ~ v1_relat_1(A_96) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_287])).

tff(c_307,plain,(
    ! [A_96,A_53] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_96,k6_relat_1(A_53))),A_53)
      | ~ v1_relat_1(A_96) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_299])).

tff(c_1096,plain,(
    ! [A_53,A_143] :
      ( r1_tarski(k9_relat_1(k6_relat_1(A_53),A_143),A_53)
      | ~ v1_relat_1(k6_relat_1(A_143))
      | ~ v1_relat_1(k6_relat_1(A_53)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1083,c_307])).

tff(c_1167,plain,(
    ! [A_146,A_147] : r1_tarski(k9_relat_1(k6_relat_1(A_146),A_147),A_146) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_22,c_1096])).

tff(c_32,plain,(
    ! [A_53] : k1_relat_1(k6_relat_1(A_53)) = A_53 ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_340,plain,(
    ! [A_104,B_105] :
      ( k5_relat_1(k6_relat_1(A_104),B_105) = B_105
      | ~ r1_tarski(k1_relat_1(B_105),A_104)
      | ~ v1_relat_1(B_105) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_353,plain,(
    ! [A_104,A_53] :
      ( k5_relat_1(k6_relat_1(A_104),k6_relat_1(A_53)) = k6_relat_1(A_53)
      | ~ r1_tarski(A_53,A_104)
      | ~ v1_relat_1(k6_relat_1(A_53)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_340])).

tff(c_506,plain,(
    ! [A_113,A_114] :
      ( k5_relat_1(k6_relat_1(A_113),k6_relat_1(A_114)) = k6_relat_1(A_114)
      | ~ r1_tarski(A_114,A_113) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_353])).

tff(c_46,plain,(
    ! [A_62,B_63] :
      ( k5_relat_1(k6_relat_1(A_62),B_63) = k7_relat_1(B_63,A_62)
      | ~ v1_relat_1(B_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_522,plain,(
    ! [A_114,A_113] :
      ( k7_relat_1(k6_relat_1(A_114),A_113) = k6_relat_1(A_114)
      | ~ v1_relat_1(k6_relat_1(A_114))
      | ~ r1_tarski(A_114,A_113) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_506,c_46])).

tff(c_583,plain,(
    ! [A_115,A_116] :
      ( k7_relat_1(k6_relat_1(A_115),A_116) = k6_relat_1(A_115)
      | ~ r1_tarski(A_115,A_116) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_522])).

tff(c_214,plain,(
    ! [B_88,A_89] :
      ( k3_xboole_0(k1_relat_1(B_88),A_89) = k1_relat_1(k7_relat_1(B_88,A_89))
      | ~ v1_relat_1(B_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_226,plain,(
    ! [A_53,A_89] :
      ( k1_relat_1(k7_relat_1(k6_relat_1(A_53),A_89)) = k3_xboole_0(A_53,A_89)
      | ~ v1_relat_1(k6_relat_1(A_53)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_214])).

tff(c_230,plain,(
    ! [A_53,A_89] : k1_relat_1(k7_relat_1(k6_relat_1(A_53),A_89)) = k3_xboole_0(A_53,A_89) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_226])).

tff(c_606,plain,(
    ! [A_115,A_116] :
      ( k3_xboole_0(A_115,A_116) = k1_relat_1(k6_relat_1(A_115))
      | ~ r1_tarski(A_115,A_116) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_583,c_230])).

tff(c_638,plain,(
    ! [A_115,A_116] :
      ( k3_xboole_0(A_115,A_116) = A_115
      | ~ r1_tarski(A_115,A_116) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_606])).

tff(c_1182,plain,(
    ! [A_146,A_147] : k3_xboole_0(k9_relat_1(k6_relat_1(A_146),A_147),A_146) = k9_relat_1(k6_relat_1(A_146),A_147) ),
    inference(resolution,[status(thm)],[c_1167,c_638])).

tff(c_2,plain,(
    ! [A_1,B_2] : r1_tarski(k3_xboole_0(A_1,B_2),A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_651,plain,(
    ! [A_117,A_118] :
      ( k3_xboole_0(A_117,A_118) = A_117
      | ~ r1_tarski(A_117,A_118) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_606])).

tff(c_680,plain,(
    ! [A_1,B_2] : k3_xboole_0(k3_xboole_0(A_1,B_2),A_1) = k3_xboole_0(A_1,B_2) ),
    inference(resolution,[status(thm)],[c_2,c_651])).

tff(c_36,plain,(
    ! [A_54] : k4_relat_1(k6_relat_1(A_54)) = k6_relat_1(A_54) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_1186,plain,(
    ! [B_148,A_149] :
      ( k5_relat_1(k4_relat_1(B_148),k4_relat_1(A_149)) = k4_relat_1(k5_relat_1(A_149,B_148))
      | ~ v1_relat_1(B_148)
      | ~ v1_relat_1(A_149) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_1201,plain,(
    ! [A_54,A_149] :
      ( k5_relat_1(k6_relat_1(A_54),k4_relat_1(A_149)) = k4_relat_1(k5_relat_1(A_149,k6_relat_1(A_54)))
      | ~ v1_relat_1(k6_relat_1(A_54))
      | ~ v1_relat_1(A_149) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_1186])).

tff(c_1702,plain,(
    ! [A_184,A_185] :
      ( k5_relat_1(k6_relat_1(A_184),k4_relat_1(A_185)) = k4_relat_1(k5_relat_1(A_185,k6_relat_1(A_184)))
      | ~ v1_relat_1(A_185) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_1201])).

tff(c_1738,plain,(
    ! [A_54,A_184] :
      ( k4_relat_1(k5_relat_1(k6_relat_1(A_54),k6_relat_1(A_184))) = k5_relat_1(k6_relat_1(A_184),k6_relat_1(A_54))
      | ~ v1_relat_1(k6_relat_1(A_54)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_1702])).

tff(c_2124,plain,(
    ! [A_199,A_200] : k4_relat_1(k5_relat_1(k6_relat_1(A_199),k6_relat_1(A_200))) = k5_relat_1(k6_relat_1(A_200),k6_relat_1(A_199)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_1738])).

tff(c_20,plain,(
    ! [A_34,B_35] :
      ( v1_relat_1(k5_relat_1(A_34,B_35))
      | ~ v1_relat_1(B_35)
      | ~ v1_relat_1(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_1724,plain,(
    ! [A_185,A_184] :
      ( v1_relat_1(k4_relat_1(k5_relat_1(A_185,k6_relat_1(A_184))))
      | ~ v1_relat_1(k4_relat_1(A_185))
      | ~ v1_relat_1(k6_relat_1(A_184))
      | ~ v1_relat_1(A_185) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1702,c_20])).

tff(c_1745,plain,(
    ! [A_185,A_184] :
      ( v1_relat_1(k4_relat_1(k5_relat_1(A_185,k6_relat_1(A_184))))
      | ~ v1_relat_1(k4_relat_1(A_185))
      | ~ v1_relat_1(A_185) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_1724])).

tff(c_2130,plain,(
    ! [A_200,A_199] :
      ( v1_relat_1(k5_relat_1(k6_relat_1(A_200),k6_relat_1(A_199)))
      | ~ v1_relat_1(k4_relat_1(k6_relat_1(A_199)))
      | ~ v1_relat_1(k6_relat_1(A_199)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2124,c_1745])).

tff(c_2227,plain,(
    ! [A_203,A_204] : v1_relat_1(k5_relat_1(k6_relat_1(A_203),k6_relat_1(A_204))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_22,c_36,c_2130])).

tff(c_2239,plain,(
    ! [A_204,A_62] :
      ( v1_relat_1(k7_relat_1(k6_relat_1(A_204),A_62))
      | ~ v1_relat_1(k6_relat_1(A_204)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_2227])).

tff(c_2251,plain,(
    ! [A_204,A_62] : v1_relat_1(k7_relat_1(k6_relat_1(A_204),A_62)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_2239])).

tff(c_2156,plain,(
    ! [A_200,A_62] :
      ( k5_relat_1(k6_relat_1(A_200),k6_relat_1(A_62)) = k4_relat_1(k7_relat_1(k6_relat_1(A_200),A_62))
      | ~ v1_relat_1(k6_relat_1(A_200)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_2124])).

tff(c_2277,plain,(
    ! [A_207,A_208] : k5_relat_1(k6_relat_1(A_207),k6_relat_1(A_208)) = k4_relat_1(k7_relat_1(k6_relat_1(A_207),A_208)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_2156])).

tff(c_2328,plain,(
    ! [A_62,A_208] :
      ( k4_relat_1(k7_relat_1(k6_relat_1(A_62),A_208)) = k7_relat_1(k6_relat_1(A_208),A_62)
      | ~ v1_relat_1(k6_relat_1(A_208)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_2277])).

tff(c_2362,plain,(
    ! [A_62,A_208] : k4_relat_1(k7_relat_1(k6_relat_1(A_62),A_208)) = k7_relat_1(k6_relat_1(A_208),A_62) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_2328])).

tff(c_2173,plain,(
    ! [A_200,A_62] : k5_relat_1(k6_relat_1(A_200),k6_relat_1(A_62)) = k4_relat_1(k7_relat_1(k6_relat_1(A_200),A_62)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_2156])).

tff(c_2433,plain,(
    ! [A_200,A_62] : k5_relat_1(k6_relat_1(A_200),k6_relat_1(A_62)) = k7_relat_1(k6_relat_1(A_62),A_200) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2362,c_2173])).

tff(c_2577,plain,(
    ! [A_217,A_218] : k5_relat_1(k6_relat_1(A_217),k6_relat_1(A_218)) = k7_relat_1(k6_relat_1(A_218),A_217) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2362,c_2173])).

tff(c_824,plain,(
    ! [A_53,B_128] :
      ( k2_relat_1(k5_relat_1(k6_relat_1(A_53),B_128)) = k9_relat_1(B_128,A_53)
      | ~ v1_relat_1(B_128) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_820])).

tff(c_2597,plain,(
    ! [A_218,A_217] :
      ( k2_relat_1(k7_relat_1(k6_relat_1(A_218),A_217)) = k9_relat_1(k6_relat_1(A_218),A_217)
      | ~ v1_relat_1(k6_relat_1(A_218)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2577,c_824])).

tff(c_2650,plain,(
    ! [A_218,A_217] : k2_relat_1(k7_relat_1(k6_relat_1(A_218),A_217)) = k9_relat_1(k6_relat_1(A_218),A_217) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_2597])).

tff(c_145,plain,(
    ! [A_80,B_81] :
      ( k5_relat_1(k6_relat_1(A_80),B_81) = k7_relat_1(B_81,A_80)
      | ~ v1_relat_1(B_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_42,plain,(
    ! [A_59] :
      ( k5_relat_1(A_59,k6_relat_1(k2_relat_1(A_59))) = A_59
      | ~ v1_relat_1(A_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_159,plain,(
    ! [A_80] :
      ( k7_relat_1(k6_relat_1(k2_relat_1(k6_relat_1(A_80))),A_80) = k6_relat_1(A_80)
      | ~ v1_relat_1(k6_relat_1(A_80))
      | ~ v1_relat_1(k6_relat_1(k2_relat_1(k6_relat_1(A_80)))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_145,c_42])).

tff(c_179,plain,(
    ! [A_80] : k7_relat_1(k6_relat_1(A_80),A_80) = k6_relat_1(A_80) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_22,c_34,c_159])).

tff(c_231,plain,(
    ! [A_90,A_91] : k1_relat_1(k7_relat_1(k6_relat_1(A_90),A_91)) = k3_xboole_0(A_90,A_91) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_226])).

tff(c_243,plain,(
    ! [A_80] : k3_xboole_0(A_80,A_80) = k1_relat_1(k6_relat_1(A_80)) ),
    inference(superposition,[status(thm),theory(equality)],[c_179,c_231])).

tff(c_247,plain,(
    ! [A_92] : k3_xboole_0(A_92,A_92) = A_92 ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_243])).

tff(c_257,plain,(
    ! [A_92] : r1_tarski(A_92,A_92) ),
    inference(superposition,[status(thm),theory(equality)],[c_247,c_2])).

tff(c_355,plain,(
    ! [B_105] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(B_105)),B_105) = B_105
      | ~ v1_relat_1(B_105) ) ),
    inference(resolution,[status(thm)],[c_257,c_340])).

tff(c_26,plain,(
    ! [A_40,B_42] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_40,B_42)),k2_relat_1(B_42))
      | ~ v1_relat_1(B_42)
      | ~ v1_relat_1(A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_5788,plain,(
    ! [A_293,B_294] :
      ( r1_tarski(k2_relat_1(k4_relat_1(k5_relat_1(A_293,B_294))),k2_relat_1(k4_relat_1(A_293)))
      | ~ v1_relat_1(k4_relat_1(A_293))
      | ~ v1_relat_1(k4_relat_1(B_294))
      | ~ v1_relat_1(B_294)
      | ~ v1_relat_1(A_293) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1186,c_26])).

tff(c_5836,plain,(
    ! [B_105] :
      ( r1_tarski(k2_relat_1(k4_relat_1(B_105)),k2_relat_1(k4_relat_1(k6_relat_1(k1_relat_1(B_105)))))
      | ~ v1_relat_1(k4_relat_1(k6_relat_1(k1_relat_1(B_105))))
      | ~ v1_relat_1(k4_relat_1(B_105))
      | ~ v1_relat_1(B_105)
      | ~ v1_relat_1(k6_relat_1(k1_relat_1(B_105)))
      | ~ v1_relat_1(B_105) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_355,c_5788])).

tff(c_5879,plain,(
    ! [B_295] :
      ( r1_tarski(k2_relat_1(k4_relat_1(B_295)),k1_relat_1(B_295))
      | ~ v1_relat_1(k4_relat_1(B_295))
      | ~ v1_relat_1(B_295) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_22,c_36,c_34,c_36,c_5836])).

tff(c_5897,plain,(
    ! [A_208,A_62] :
      ( r1_tarski(k2_relat_1(k7_relat_1(k6_relat_1(A_208),A_62)),k1_relat_1(k7_relat_1(k6_relat_1(A_62),A_208)))
      | ~ v1_relat_1(k4_relat_1(k7_relat_1(k6_relat_1(A_62),A_208)))
      | ~ v1_relat_1(k7_relat_1(k6_relat_1(A_62),A_208)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2362,c_5879])).

tff(c_5917,plain,(
    ! [A_208,A_62] : r1_tarski(k9_relat_1(k6_relat_1(A_208),A_62),k3_xboole_0(A_62,A_208)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2251,c_2251,c_2362,c_2650,c_230,c_5897])).

tff(c_731,plain,(
    ! [B_123,A_124] :
      ( k5_relat_1(B_123,k6_relat_1(A_124)) = B_123
      | ~ r1_tarski(k2_relat_1(B_123),A_124)
      | ~ v1_relat_1(B_123) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_750,plain,(
    ! [A_53,A_124] :
      ( k5_relat_1(k6_relat_1(A_53),k6_relat_1(A_124)) = k6_relat_1(A_53)
      | ~ r1_tarski(A_53,A_124)
      | ~ v1_relat_1(k6_relat_1(A_53)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_731])).

tff(c_757,plain,(
    ! [A_53,A_124] :
      ( k5_relat_1(k6_relat_1(A_53),k6_relat_1(A_124)) = k6_relat_1(A_53)
      | ~ r1_tarski(A_53,A_124) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_750])).

tff(c_1114,plain,(
    ! [A_124,A_53] :
      ( k9_relat_1(k6_relat_1(A_124),A_53) = k2_relat_1(k6_relat_1(A_53))
      | ~ v1_relat_1(k6_relat_1(A_124))
      | ~ r1_tarski(A_53,A_124) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_757,c_1083])).

tff(c_1138,plain,(
    ! [A_124,A_53] :
      ( k9_relat_1(k6_relat_1(A_124),A_53) = A_53
      | ~ r1_tarski(A_53,A_124) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_34,c_1114])).

tff(c_827,plain,(
    ! [A_130,A_131] :
      ( k5_relat_1(k6_relat_1(A_130),k6_relat_1(A_131)) = k6_relat_1(A_130)
      | ~ r1_tarski(A_130,A_131) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_750])).

tff(c_846,plain,(
    ! [A_131,A_130] :
      ( k7_relat_1(k6_relat_1(A_131),A_130) = k6_relat_1(A_130)
      | ~ v1_relat_1(k6_relat_1(A_131))
      | ~ r1_tarski(A_130,A_131) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_827,c_46])).

tff(c_890,plain,(
    ! [A_131,A_130] :
      ( k7_relat_1(k6_relat_1(A_131),A_130) = k6_relat_1(A_130)
      | ~ r1_tarski(A_130,A_131) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_846])).

tff(c_1398,plain,(
    ! [A_167,B_168,C_169] :
      ( k5_relat_1(k5_relat_1(A_167,B_168),C_169) = k5_relat_1(A_167,k5_relat_1(B_168,C_169))
      | ~ v1_relat_1(C_169)
      | ~ v1_relat_1(B_168)
      | ~ v1_relat_1(A_167) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_1439,plain,(
    ! [A_62,B_63,C_169] :
      ( k5_relat_1(k6_relat_1(A_62),k5_relat_1(B_63,C_169)) = k5_relat_1(k7_relat_1(B_63,A_62),C_169)
      | ~ v1_relat_1(C_169)
      | ~ v1_relat_1(B_63)
      | ~ v1_relat_1(k6_relat_1(A_62))
      | ~ v1_relat_1(B_63) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_1398])).

tff(c_3324,plain,(
    ! [A_243,B_244,C_245] :
      ( k5_relat_1(k6_relat_1(A_243),k5_relat_1(B_244,C_245)) = k5_relat_1(k7_relat_1(B_244,A_243),C_245)
      | ~ v1_relat_1(C_245)
      | ~ v1_relat_1(B_244) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_1439])).

tff(c_3401,plain,(
    ! [A_62,A_243,B_63] :
      ( k5_relat_1(k7_relat_1(k6_relat_1(A_62),A_243),B_63) = k5_relat_1(k6_relat_1(A_243),k7_relat_1(B_63,A_62))
      | ~ v1_relat_1(B_63)
      | ~ v1_relat_1(k6_relat_1(A_62))
      | ~ v1_relat_1(B_63) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_3324])).

tff(c_22317,plain,(
    ! [A_500,A_501,B_502] :
      ( k5_relat_1(k7_relat_1(k6_relat_1(A_500),A_501),B_502) = k5_relat_1(k6_relat_1(A_501),k7_relat_1(B_502,A_500))
      | ~ v1_relat_1(B_502) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_3401])).

tff(c_22399,plain,(
    ! [A_501,A_53,A_500] :
      ( r1_tarski(k2_relat_1(k5_relat_1(k6_relat_1(A_501),k7_relat_1(k6_relat_1(A_53),A_500))),A_53)
      | ~ v1_relat_1(k7_relat_1(k6_relat_1(A_500),A_501))
      | ~ v1_relat_1(k6_relat_1(A_53)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22317,c_307])).

tff(c_23044,plain,(
    ! [A_521,A_522,A_523] : r1_tarski(k2_relat_1(k5_relat_1(k6_relat_1(A_521),k7_relat_1(k6_relat_1(A_522),A_523))),A_522) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_2251,c_22399])).

tff(c_23103,plain,(
    ! [A_521,A_130,A_131] :
      ( r1_tarski(k2_relat_1(k5_relat_1(k6_relat_1(A_521),k6_relat_1(A_130))),A_131)
      | ~ r1_tarski(A_130,A_131) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_890,c_23044])).

tff(c_23230,plain,(
    ! [A_527,A_528,A_529] :
      ( r1_tarski(k9_relat_1(k6_relat_1(A_527),A_528),A_529)
      | ~ r1_tarski(A_527,A_529) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2650,c_2433,c_23103])).

tff(c_23771,plain,(
    ! [A_541,A_542,A_543] :
      ( r1_tarski(A_541,A_542)
      | ~ r1_tarski(A_543,A_542)
      | ~ r1_tarski(A_541,A_543) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1138,c_23230])).

tff(c_24325,plain,(
    ! [A_550,A_551,B_552] :
      ( r1_tarski(A_550,A_551)
      | ~ r1_tarski(A_550,k3_xboole_0(A_551,B_552)) ) ),
    inference(resolution,[status(thm)],[c_2,c_23771])).

tff(c_24597,plain,(
    ! [A_208,A_62] : r1_tarski(k9_relat_1(k6_relat_1(A_208),A_62),A_62) ),
    inference(resolution,[status(thm)],[c_5917,c_24325])).

tff(c_1449,plain,(
    ! [A_167,B_168] :
      ( k5_relat_1(A_167,k5_relat_1(B_168,k6_relat_1(k2_relat_1(k5_relat_1(A_167,B_168))))) = k5_relat_1(A_167,B_168)
      | ~ v1_relat_1(k6_relat_1(k2_relat_1(k5_relat_1(A_167,B_168))))
      | ~ v1_relat_1(B_168)
      | ~ v1_relat_1(A_167)
      | ~ v1_relat_1(k5_relat_1(A_167,B_168)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_1398])).

tff(c_6858,plain,(
    ! [A_308,B_309] :
      ( k5_relat_1(A_308,k5_relat_1(B_309,k6_relat_1(k2_relat_1(k5_relat_1(A_308,B_309))))) = k5_relat_1(A_308,B_309)
      | ~ v1_relat_1(B_309)
      | ~ v1_relat_1(A_308)
      | ~ v1_relat_1(k5_relat_1(A_308,B_309)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_1449])).

tff(c_6995,plain,(
    ! [A_308,A_62] :
      ( k5_relat_1(A_308,k7_relat_1(k6_relat_1(k2_relat_1(k5_relat_1(A_308,k6_relat_1(A_62)))),A_62)) = k5_relat_1(A_308,k6_relat_1(A_62))
      | ~ v1_relat_1(k6_relat_1(A_62))
      | ~ v1_relat_1(A_308)
      | ~ v1_relat_1(k5_relat_1(A_308,k6_relat_1(A_62)))
      | ~ v1_relat_1(k6_relat_1(k2_relat_1(k5_relat_1(A_308,k6_relat_1(A_62))))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_6858])).

tff(c_119770,plain,(
    ! [A_1381,A_1382] :
      ( k5_relat_1(A_1381,k7_relat_1(k6_relat_1(k2_relat_1(k5_relat_1(A_1381,k6_relat_1(A_1382)))),A_1382)) = k5_relat_1(A_1381,k6_relat_1(A_1382))
      | ~ v1_relat_1(A_1381)
      | ~ v1_relat_1(k5_relat_1(A_1381,k6_relat_1(A_1382))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_22,c_6995])).

tff(c_350,plain,(
    ! [A_104,A_53,A_89] :
      ( k5_relat_1(k6_relat_1(A_104),k7_relat_1(k6_relat_1(A_53),A_89)) = k7_relat_1(k6_relat_1(A_53),A_89)
      | ~ r1_tarski(k3_xboole_0(A_53,A_89),A_104)
      | ~ v1_relat_1(k7_relat_1(k6_relat_1(A_53),A_89)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_230,c_340])).

tff(c_105576,plain,(
    ! [A_104,A_53,A_89] :
      ( k5_relat_1(k6_relat_1(A_104),k7_relat_1(k6_relat_1(A_53),A_89)) = k7_relat_1(k6_relat_1(A_53),A_89)
      | ~ r1_tarski(k3_xboole_0(A_53,A_89),A_104) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2251,c_350])).

tff(c_119808,plain,(
    ! [A_104,A_1382] :
      ( k7_relat_1(k6_relat_1(k2_relat_1(k5_relat_1(k6_relat_1(A_104),k6_relat_1(A_1382)))),A_1382) = k5_relat_1(k6_relat_1(A_104),k6_relat_1(A_1382))
      | ~ r1_tarski(k3_xboole_0(k2_relat_1(k5_relat_1(k6_relat_1(A_104),k6_relat_1(A_1382))),A_1382),A_104)
      | ~ v1_relat_1(k6_relat_1(A_104))
      | ~ v1_relat_1(k5_relat_1(k6_relat_1(A_104),k6_relat_1(A_1382))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_119770,c_105576])).

tff(c_120393,plain,(
    ! [A_1383,A_1384] : k7_relat_1(k6_relat_1(k9_relat_1(k6_relat_1(A_1383),A_1384)),A_1383) = k7_relat_1(k6_relat_1(A_1383),A_1384) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2251,c_2433,c_22,c_24597,c_1182,c_2650,c_2433,c_2650,c_2433,c_2433,c_119808])).

tff(c_44,plain,(
    ! [B_61,A_60] :
      ( k3_xboole_0(k1_relat_1(B_61),A_60) = k1_relat_1(k7_relat_1(B_61,A_60))
      | ~ v1_relat_1(B_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_246,plain,(
    ! [A_80] : k3_xboole_0(A_80,A_80) = A_80 ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_243])).

tff(c_97,plain,(
    ! [A_76] :
      ( k5_relat_1(A_76,k6_relat_1(k2_relat_1(A_76))) = A_76
      | ~ v1_relat_1(A_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_109,plain,(
    ! [A_53] :
      ( k5_relat_1(k6_relat_1(A_53),k6_relat_1(A_53)) = k6_relat_1(A_53)
      | ~ v1_relat_1(k6_relat_1(A_53)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_97])).

tff(c_115,plain,(
    ! [A_53] : k5_relat_1(k6_relat_1(A_53),k6_relat_1(A_53)) = k6_relat_1(A_53) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_109])).

tff(c_1442,plain,(
    ! [A_53,C_169] :
      ( k5_relat_1(k6_relat_1(A_53),k5_relat_1(k6_relat_1(A_53),C_169)) = k5_relat_1(k6_relat_1(A_53),C_169)
      | ~ v1_relat_1(C_169)
      | ~ v1_relat_1(k6_relat_1(A_53))
      | ~ v1_relat_1(k6_relat_1(A_53)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_115,c_1398])).

tff(c_14203,plain,(
    ! [A_418,C_419] :
      ( k5_relat_1(k6_relat_1(A_418),k5_relat_1(k6_relat_1(A_418),C_419)) = k5_relat_1(k6_relat_1(A_418),C_419)
      | ~ v1_relat_1(C_419) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_22,c_1442])).

tff(c_14319,plain,(
    ! [A_200,A_62] :
      ( k5_relat_1(k6_relat_1(A_200),k7_relat_1(k6_relat_1(A_62),A_200)) = k5_relat_1(k6_relat_1(A_200),k6_relat_1(A_62))
      | ~ v1_relat_1(k6_relat_1(A_62)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2433,c_14203])).

tff(c_14565,plain,(
    ! [A_424,A_425] : k5_relat_1(k6_relat_1(A_424),k7_relat_1(k6_relat_1(A_425),A_424)) = k7_relat_1(k6_relat_1(A_425),A_424) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_2433,c_14319])).

tff(c_14623,plain,(
    ! [A_425,A_424] :
      ( k7_relat_1(k7_relat_1(k6_relat_1(A_425),A_424),A_424) = k7_relat_1(k6_relat_1(A_425),A_424)
      | ~ v1_relat_1(k7_relat_1(k6_relat_1(A_425),A_424)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14565,c_46])).

tff(c_14722,plain,(
    ! [A_426,A_427] : k7_relat_1(k7_relat_1(k6_relat_1(A_426),A_427),A_427) = k7_relat_1(k6_relat_1(A_426),A_427) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2251,c_14623])).

tff(c_682,plain,(
    ! [A_119,B_120] : k3_xboole_0(k3_xboole_0(A_119,B_120),A_119) = k3_xboole_0(A_119,B_120) ),
    inference(resolution,[status(thm)],[c_2,c_651])).

tff(c_703,plain,(
    ! [B_61,A_60] :
      ( k3_xboole_0(k1_relat_1(k7_relat_1(B_61,A_60)),k1_relat_1(B_61)) = k3_xboole_0(k1_relat_1(B_61),A_60)
      | ~ v1_relat_1(B_61) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_682])).

tff(c_14734,plain,(
    ! [A_426,A_427] :
      ( k3_xboole_0(k1_relat_1(k7_relat_1(k6_relat_1(A_426),A_427)),k1_relat_1(k7_relat_1(k6_relat_1(A_426),A_427))) = k3_xboole_0(k1_relat_1(k7_relat_1(k6_relat_1(A_426),A_427)),A_427)
      | ~ v1_relat_1(k7_relat_1(k6_relat_1(A_426),A_427)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14722,c_703])).

tff(c_14849,plain,(
    ! [A_428,A_429] : k3_xboole_0(k3_xboole_0(A_428,A_429),A_429) = k3_xboole_0(A_428,A_429) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2251,c_246,c_230,c_230,c_230,c_14734])).

tff(c_15056,plain,(
    ! [B_61,A_60] :
      ( k3_xboole_0(k1_relat_1(k7_relat_1(B_61,A_60)),A_60) = k3_xboole_0(k1_relat_1(B_61),A_60)
      | ~ v1_relat_1(B_61) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_14849])).

tff(c_120710,plain,(
    ! [A_1383,A_1384] :
      ( k3_xboole_0(k1_relat_1(k6_relat_1(k9_relat_1(k6_relat_1(A_1383),A_1384))),A_1383) = k3_xboole_0(k1_relat_1(k7_relat_1(k6_relat_1(A_1383),A_1384)),A_1383)
      | ~ v1_relat_1(k6_relat_1(k9_relat_1(k6_relat_1(A_1383),A_1384))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_120393,c_15056])).

tff(c_121061,plain,(
    ! [A_1383,A_1384] : k9_relat_1(k6_relat_1(A_1383),A_1384) = k3_xboole_0(A_1383,A_1384) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_1182,c_680,c_230,c_32,c_120710])).

tff(c_1133,plain,(
    ! [A_53,A_143] : r1_tarski(k9_relat_1(k6_relat_1(A_53),A_143),A_53) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_22,c_1096])).

tff(c_564,plain,(
    ! [A_114,A_113] :
      ( k7_relat_1(k6_relat_1(A_114),A_113) = k6_relat_1(A_114)
      | ~ r1_tarski(A_114,A_113) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_522])).

tff(c_120769,plain,(
    ! [A_1383,A_1384] :
      ( k6_relat_1(k9_relat_1(k6_relat_1(A_1383),A_1384)) = k7_relat_1(k6_relat_1(A_1383),A_1384)
      | ~ r1_tarski(k9_relat_1(k6_relat_1(A_1383),A_1384),A_1383) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_120393,c_564])).

tff(c_121090,plain,(
    ! [A_1383,A_1384] : k6_relat_1(k9_relat_1(k6_relat_1(A_1383),A_1384)) = k7_relat_1(k6_relat_1(A_1383),A_1384) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1133,c_120769])).

tff(c_134900,plain,(
    ! [A_1383,A_1384] : k7_relat_1(k6_relat_1(A_1383),A_1384) = k6_relat_1(k3_xboole_0(A_1383,A_1384)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_121061,c_121090])).

tff(c_48,plain,(
    k5_relat_1(k6_relat_1('#skF_2'),k6_relat_1('#skF_1')) != k6_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_155,plain,
    ( k7_relat_1(k6_relat_1('#skF_1'),'#skF_2') != k6_relat_1(k3_xboole_0('#skF_1','#skF_2'))
    | ~ v1_relat_1(k6_relat_1('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_145,c_48])).

tff(c_177,plain,(
    k7_relat_1(k6_relat_1('#skF_1'),'#skF_2') != k6_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_155])).

tff(c_135005,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_134900,c_177])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:28:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 31.37/21.88  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 31.37/21.90  
% 31.37/21.90  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 31.37/21.90  %$ r1_tarski > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k6_relat_1 > k4_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1
% 31.37/21.90  
% 31.37/21.90  %Foreground sorts:
% 31.37/21.90  
% 31.37/21.90  
% 31.37/21.90  %Background operators:
% 31.37/21.90  
% 31.37/21.90  
% 31.37/21.90  %Foreground operators:
% 31.37/21.90  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 31.37/21.90  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 31.37/21.90  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 31.37/21.90  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 31.37/21.90  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 31.37/21.90  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 31.37/21.90  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 31.37/21.90  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 31.37/21.90  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 31.37/21.90  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 31.37/21.90  tff('#skF_2', type, '#skF_2': $i).
% 31.37/21.90  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 31.37/21.90  tff('#skF_1', type, '#skF_1': $i).
% 31.37/21.90  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 31.37/21.90  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 31.37/21.90  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 31.37/21.90  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 31.37/21.90  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 31.37/21.90  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 31.37/21.90  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 31.37/21.90  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 31.37/21.90  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 31.37/21.90  tff(k4_relat_1, type, k4_relat_1: $i > $i).
% 31.37/21.90  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 31.37/21.90  
% 31.37/21.92  tff(f_51, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 31.37/21.92  tff(f_86, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 31.37/21.92  tff(f_58, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k2_relat_1(k5_relat_1(A, B)) = k9_relat_1(B, k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t160_relat_1)).
% 31.37/21.92  tff(f_65, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k2_relat_1(k5_relat_1(A, B)), k2_relat_1(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t45_relat_1)).
% 31.37/21.92  tff(f_94, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k5_relat_1(k6_relat_1(A), B) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t77_relat_1)).
% 31.37/21.92  tff(f_112, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_relat_1)).
% 31.37/21.92  tff(f_108, axiom, (![A, B]: (v1_relat_1(B) => (k1_relat_1(k7_relat_1(B, A)) = k3_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t90_relat_1)).
% 31.37/21.92  tff(f_27, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 31.37/21.92  tff(f_88, axiom, (![A]: (k4_relat_1(k6_relat_1(A)) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_relat_1)).
% 31.37/21.92  tff(f_72, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k4_relat_1(k5_relat_1(A, B)) = k5_relat_1(k4_relat_1(B), k4_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t54_relat_1)).
% 31.37/21.92  tff(f_49, axiom, (![A, B]: ((v1_relat_1(A) & v1_relat_1(B)) => v1_relat_1(k5_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k5_relat_1)).
% 31.37/21.92  tff(f_104, axiom, (![A]: (v1_relat_1(A) => (k5_relat_1(A, k6_relat_1(k2_relat_1(A))) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t80_relat_1)).
% 31.37/21.92  tff(f_100, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k5_relat_1(B, k6_relat_1(A)) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_relat_1)).
% 31.37/21.92  tff(f_82, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (k5_relat_1(k5_relat_1(A, B), C) = k5_relat_1(A, k5_relat_1(B, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_relat_1)).
% 31.37/21.92  tff(f_115, negated_conjecture, ~(![A, B]: (k5_relat_1(k6_relat_1(B), k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_funct_1)).
% 31.37/21.92  tff(c_22, plain, (![A_36]: (v1_relat_1(k6_relat_1(A_36)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 31.37/21.92  tff(c_34, plain, (![A_53]: (k2_relat_1(k6_relat_1(A_53))=A_53)), inference(cnfTransformation, [status(thm)], [f_86])).
% 31.37/21.92  tff(c_811, plain, (![B_128, A_129]: (k9_relat_1(B_128, k2_relat_1(A_129))=k2_relat_1(k5_relat_1(A_129, B_128)) | ~v1_relat_1(B_128) | ~v1_relat_1(A_129))), inference(cnfTransformation, [status(thm)], [f_58])).
% 31.37/21.92  tff(c_820, plain, (![A_53, B_128]: (k2_relat_1(k5_relat_1(k6_relat_1(A_53), B_128))=k9_relat_1(B_128, A_53) | ~v1_relat_1(B_128) | ~v1_relat_1(k6_relat_1(A_53)))), inference(superposition, [status(thm), theory('equality')], [c_34, c_811])).
% 31.37/21.92  tff(c_1083, plain, (![A_143, B_144]: (k2_relat_1(k5_relat_1(k6_relat_1(A_143), B_144))=k9_relat_1(B_144, A_143) | ~v1_relat_1(B_144))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_820])).
% 31.37/21.92  tff(c_287, plain, (![A_96, B_97]: (r1_tarski(k2_relat_1(k5_relat_1(A_96, B_97)), k2_relat_1(B_97)) | ~v1_relat_1(B_97) | ~v1_relat_1(A_96))), inference(cnfTransformation, [status(thm)], [f_65])).
% 31.37/21.92  tff(c_299, plain, (![A_96, A_53]: (r1_tarski(k2_relat_1(k5_relat_1(A_96, k6_relat_1(A_53))), A_53) | ~v1_relat_1(k6_relat_1(A_53)) | ~v1_relat_1(A_96))), inference(superposition, [status(thm), theory('equality')], [c_34, c_287])).
% 31.37/21.92  tff(c_307, plain, (![A_96, A_53]: (r1_tarski(k2_relat_1(k5_relat_1(A_96, k6_relat_1(A_53))), A_53) | ~v1_relat_1(A_96))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_299])).
% 31.37/21.92  tff(c_1096, plain, (![A_53, A_143]: (r1_tarski(k9_relat_1(k6_relat_1(A_53), A_143), A_53) | ~v1_relat_1(k6_relat_1(A_143)) | ~v1_relat_1(k6_relat_1(A_53)))), inference(superposition, [status(thm), theory('equality')], [c_1083, c_307])).
% 31.37/21.92  tff(c_1167, plain, (![A_146, A_147]: (r1_tarski(k9_relat_1(k6_relat_1(A_146), A_147), A_146))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_22, c_1096])).
% 31.37/21.92  tff(c_32, plain, (![A_53]: (k1_relat_1(k6_relat_1(A_53))=A_53)), inference(cnfTransformation, [status(thm)], [f_86])).
% 31.37/21.92  tff(c_340, plain, (![A_104, B_105]: (k5_relat_1(k6_relat_1(A_104), B_105)=B_105 | ~r1_tarski(k1_relat_1(B_105), A_104) | ~v1_relat_1(B_105))), inference(cnfTransformation, [status(thm)], [f_94])).
% 31.37/21.92  tff(c_353, plain, (![A_104, A_53]: (k5_relat_1(k6_relat_1(A_104), k6_relat_1(A_53))=k6_relat_1(A_53) | ~r1_tarski(A_53, A_104) | ~v1_relat_1(k6_relat_1(A_53)))), inference(superposition, [status(thm), theory('equality')], [c_32, c_340])).
% 31.37/21.92  tff(c_506, plain, (![A_113, A_114]: (k5_relat_1(k6_relat_1(A_113), k6_relat_1(A_114))=k6_relat_1(A_114) | ~r1_tarski(A_114, A_113))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_353])).
% 31.37/21.92  tff(c_46, plain, (![A_62, B_63]: (k5_relat_1(k6_relat_1(A_62), B_63)=k7_relat_1(B_63, A_62) | ~v1_relat_1(B_63))), inference(cnfTransformation, [status(thm)], [f_112])).
% 31.37/21.92  tff(c_522, plain, (![A_114, A_113]: (k7_relat_1(k6_relat_1(A_114), A_113)=k6_relat_1(A_114) | ~v1_relat_1(k6_relat_1(A_114)) | ~r1_tarski(A_114, A_113))), inference(superposition, [status(thm), theory('equality')], [c_506, c_46])).
% 31.37/21.92  tff(c_583, plain, (![A_115, A_116]: (k7_relat_1(k6_relat_1(A_115), A_116)=k6_relat_1(A_115) | ~r1_tarski(A_115, A_116))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_522])).
% 31.37/21.92  tff(c_214, plain, (![B_88, A_89]: (k3_xboole_0(k1_relat_1(B_88), A_89)=k1_relat_1(k7_relat_1(B_88, A_89)) | ~v1_relat_1(B_88))), inference(cnfTransformation, [status(thm)], [f_108])).
% 31.37/21.92  tff(c_226, plain, (![A_53, A_89]: (k1_relat_1(k7_relat_1(k6_relat_1(A_53), A_89))=k3_xboole_0(A_53, A_89) | ~v1_relat_1(k6_relat_1(A_53)))), inference(superposition, [status(thm), theory('equality')], [c_32, c_214])).
% 31.37/21.92  tff(c_230, plain, (![A_53, A_89]: (k1_relat_1(k7_relat_1(k6_relat_1(A_53), A_89))=k3_xboole_0(A_53, A_89))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_226])).
% 31.37/21.92  tff(c_606, plain, (![A_115, A_116]: (k3_xboole_0(A_115, A_116)=k1_relat_1(k6_relat_1(A_115)) | ~r1_tarski(A_115, A_116))), inference(superposition, [status(thm), theory('equality')], [c_583, c_230])).
% 31.37/21.92  tff(c_638, plain, (![A_115, A_116]: (k3_xboole_0(A_115, A_116)=A_115 | ~r1_tarski(A_115, A_116))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_606])).
% 31.37/21.92  tff(c_1182, plain, (![A_146, A_147]: (k3_xboole_0(k9_relat_1(k6_relat_1(A_146), A_147), A_146)=k9_relat_1(k6_relat_1(A_146), A_147))), inference(resolution, [status(thm)], [c_1167, c_638])).
% 31.37/21.92  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(k3_xboole_0(A_1, B_2), A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 31.37/21.92  tff(c_651, plain, (![A_117, A_118]: (k3_xboole_0(A_117, A_118)=A_117 | ~r1_tarski(A_117, A_118))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_606])).
% 31.37/21.92  tff(c_680, plain, (![A_1, B_2]: (k3_xboole_0(k3_xboole_0(A_1, B_2), A_1)=k3_xboole_0(A_1, B_2))), inference(resolution, [status(thm)], [c_2, c_651])).
% 31.37/21.92  tff(c_36, plain, (![A_54]: (k4_relat_1(k6_relat_1(A_54))=k6_relat_1(A_54))), inference(cnfTransformation, [status(thm)], [f_88])).
% 31.37/21.92  tff(c_1186, plain, (![B_148, A_149]: (k5_relat_1(k4_relat_1(B_148), k4_relat_1(A_149))=k4_relat_1(k5_relat_1(A_149, B_148)) | ~v1_relat_1(B_148) | ~v1_relat_1(A_149))), inference(cnfTransformation, [status(thm)], [f_72])).
% 31.37/21.92  tff(c_1201, plain, (![A_54, A_149]: (k5_relat_1(k6_relat_1(A_54), k4_relat_1(A_149))=k4_relat_1(k5_relat_1(A_149, k6_relat_1(A_54))) | ~v1_relat_1(k6_relat_1(A_54)) | ~v1_relat_1(A_149))), inference(superposition, [status(thm), theory('equality')], [c_36, c_1186])).
% 31.37/21.92  tff(c_1702, plain, (![A_184, A_185]: (k5_relat_1(k6_relat_1(A_184), k4_relat_1(A_185))=k4_relat_1(k5_relat_1(A_185, k6_relat_1(A_184))) | ~v1_relat_1(A_185))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_1201])).
% 31.37/21.92  tff(c_1738, plain, (![A_54, A_184]: (k4_relat_1(k5_relat_1(k6_relat_1(A_54), k6_relat_1(A_184)))=k5_relat_1(k6_relat_1(A_184), k6_relat_1(A_54)) | ~v1_relat_1(k6_relat_1(A_54)))), inference(superposition, [status(thm), theory('equality')], [c_36, c_1702])).
% 31.37/21.92  tff(c_2124, plain, (![A_199, A_200]: (k4_relat_1(k5_relat_1(k6_relat_1(A_199), k6_relat_1(A_200)))=k5_relat_1(k6_relat_1(A_200), k6_relat_1(A_199)))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_1738])).
% 31.37/21.92  tff(c_20, plain, (![A_34, B_35]: (v1_relat_1(k5_relat_1(A_34, B_35)) | ~v1_relat_1(B_35) | ~v1_relat_1(A_34))), inference(cnfTransformation, [status(thm)], [f_49])).
% 31.37/21.92  tff(c_1724, plain, (![A_185, A_184]: (v1_relat_1(k4_relat_1(k5_relat_1(A_185, k6_relat_1(A_184)))) | ~v1_relat_1(k4_relat_1(A_185)) | ~v1_relat_1(k6_relat_1(A_184)) | ~v1_relat_1(A_185))), inference(superposition, [status(thm), theory('equality')], [c_1702, c_20])).
% 31.37/21.92  tff(c_1745, plain, (![A_185, A_184]: (v1_relat_1(k4_relat_1(k5_relat_1(A_185, k6_relat_1(A_184)))) | ~v1_relat_1(k4_relat_1(A_185)) | ~v1_relat_1(A_185))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_1724])).
% 31.37/21.92  tff(c_2130, plain, (![A_200, A_199]: (v1_relat_1(k5_relat_1(k6_relat_1(A_200), k6_relat_1(A_199))) | ~v1_relat_1(k4_relat_1(k6_relat_1(A_199))) | ~v1_relat_1(k6_relat_1(A_199)))), inference(superposition, [status(thm), theory('equality')], [c_2124, c_1745])).
% 31.37/21.92  tff(c_2227, plain, (![A_203, A_204]: (v1_relat_1(k5_relat_1(k6_relat_1(A_203), k6_relat_1(A_204))))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_22, c_36, c_2130])).
% 31.37/21.92  tff(c_2239, plain, (![A_204, A_62]: (v1_relat_1(k7_relat_1(k6_relat_1(A_204), A_62)) | ~v1_relat_1(k6_relat_1(A_204)))), inference(superposition, [status(thm), theory('equality')], [c_46, c_2227])).
% 31.37/21.92  tff(c_2251, plain, (![A_204, A_62]: (v1_relat_1(k7_relat_1(k6_relat_1(A_204), A_62)))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_2239])).
% 31.37/21.92  tff(c_2156, plain, (![A_200, A_62]: (k5_relat_1(k6_relat_1(A_200), k6_relat_1(A_62))=k4_relat_1(k7_relat_1(k6_relat_1(A_200), A_62)) | ~v1_relat_1(k6_relat_1(A_200)))), inference(superposition, [status(thm), theory('equality')], [c_46, c_2124])).
% 31.37/21.92  tff(c_2277, plain, (![A_207, A_208]: (k5_relat_1(k6_relat_1(A_207), k6_relat_1(A_208))=k4_relat_1(k7_relat_1(k6_relat_1(A_207), A_208)))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_2156])).
% 31.37/21.92  tff(c_2328, plain, (![A_62, A_208]: (k4_relat_1(k7_relat_1(k6_relat_1(A_62), A_208))=k7_relat_1(k6_relat_1(A_208), A_62) | ~v1_relat_1(k6_relat_1(A_208)))), inference(superposition, [status(thm), theory('equality')], [c_46, c_2277])).
% 31.37/21.92  tff(c_2362, plain, (![A_62, A_208]: (k4_relat_1(k7_relat_1(k6_relat_1(A_62), A_208))=k7_relat_1(k6_relat_1(A_208), A_62))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_2328])).
% 31.37/21.92  tff(c_2173, plain, (![A_200, A_62]: (k5_relat_1(k6_relat_1(A_200), k6_relat_1(A_62))=k4_relat_1(k7_relat_1(k6_relat_1(A_200), A_62)))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_2156])).
% 31.37/21.92  tff(c_2433, plain, (![A_200, A_62]: (k5_relat_1(k6_relat_1(A_200), k6_relat_1(A_62))=k7_relat_1(k6_relat_1(A_62), A_200))), inference(demodulation, [status(thm), theory('equality')], [c_2362, c_2173])).
% 31.37/21.92  tff(c_2577, plain, (![A_217, A_218]: (k5_relat_1(k6_relat_1(A_217), k6_relat_1(A_218))=k7_relat_1(k6_relat_1(A_218), A_217))), inference(demodulation, [status(thm), theory('equality')], [c_2362, c_2173])).
% 31.37/21.92  tff(c_824, plain, (![A_53, B_128]: (k2_relat_1(k5_relat_1(k6_relat_1(A_53), B_128))=k9_relat_1(B_128, A_53) | ~v1_relat_1(B_128))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_820])).
% 31.37/21.92  tff(c_2597, plain, (![A_218, A_217]: (k2_relat_1(k7_relat_1(k6_relat_1(A_218), A_217))=k9_relat_1(k6_relat_1(A_218), A_217) | ~v1_relat_1(k6_relat_1(A_218)))), inference(superposition, [status(thm), theory('equality')], [c_2577, c_824])).
% 31.37/21.92  tff(c_2650, plain, (![A_218, A_217]: (k2_relat_1(k7_relat_1(k6_relat_1(A_218), A_217))=k9_relat_1(k6_relat_1(A_218), A_217))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_2597])).
% 31.37/21.92  tff(c_145, plain, (![A_80, B_81]: (k5_relat_1(k6_relat_1(A_80), B_81)=k7_relat_1(B_81, A_80) | ~v1_relat_1(B_81))), inference(cnfTransformation, [status(thm)], [f_112])).
% 31.37/21.92  tff(c_42, plain, (![A_59]: (k5_relat_1(A_59, k6_relat_1(k2_relat_1(A_59)))=A_59 | ~v1_relat_1(A_59))), inference(cnfTransformation, [status(thm)], [f_104])).
% 31.37/21.92  tff(c_159, plain, (![A_80]: (k7_relat_1(k6_relat_1(k2_relat_1(k6_relat_1(A_80))), A_80)=k6_relat_1(A_80) | ~v1_relat_1(k6_relat_1(A_80)) | ~v1_relat_1(k6_relat_1(k2_relat_1(k6_relat_1(A_80)))))), inference(superposition, [status(thm), theory('equality')], [c_145, c_42])).
% 31.37/21.92  tff(c_179, plain, (![A_80]: (k7_relat_1(k6_relat_1(A_80), A_80)=k6_relat_1(A_80))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_22, c_34, c_159])).
% 31.37/21.92  tff(c_231, plain, (![A_90, A_91]: (k1_relat_1(k7_relat_1(k6_relat_1(A_90), A_91))=k3_xboole_0(A_90, A_91))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_226])).
% 31.37/21.92  tff(c_243, plain, (![A_80]: (k3_xboole_0(A_80, A_80)=k1_relat_1(k6_relat_1(A_80)))), inference(superposition, [status(thm), theory('equality')], [c_179, c_231])).
% 31.37/21.92  tff(c_247, plain, (![A_92]: (k3_xboole_0(A_92, A_92)=A_92)), inference(demodulation, [status(thm), theory('equality')], [c_32, c_243])).
% 31.37/21.92  tff(c_257, plain, (![A_92]: (r1_tarski(A_92, A_92))), inference(superposition, [status(thm), theory('equality')], [c_247, c_2])).
% 31.37/21.92  tff(c_355, plain, (![B_105]: (k5_relat_1(k6_relat_1(k1_relat_1(B_105)), B_105)=B_105 | ~v1_relat_1(B_105))), inference(resolution, [status(thm)], [c_257, c_340])).
% 31.37/21.92  tff(c_26, plain, (![A_40, B_42]: (r1_tarski(k2_relat_1(k5_relat_1(A_40, B_42)), k2_relat_1(B_42)) | ~v1_relat_1(B_42) | ~v1_relat_1(A_40))), inference(cnfTransformation, [status(thm)], [f_65])).
% 31.37/21.92  tff(c_5788, plain, (![A_293, B_294]: (r1_tarski(k2_relat_1(k4_relat_1(k5_relat_1(A_293, B_294))), k2_relat_1(k4_relat_1(A_293))) | ~v1_relat_1(k4_relat_1(A_293)) | ~v1_relat_1(k4_relat_1(B_294)) | ~v1_relat_1(B_294) | ~v1_relat_1(A_293))), inference(superposition, [status(thm), theory('equality')], [c_1186, c_26])).
% 31.37/21.92  tff(c_5836, plain, (![B_105]: (r1_tarski(k2_relat_1(k4_relat_1(B_105)), k2_relat_1(k4_relat_1(k6_relat_1(k1_relat_1(B_105))))) | ~v1_relat_1(k4_relat_1(k6_relat_1(k1_relat_1(B_105)))) | ~v1_relat_1(k4_relat_1(B_105)) | ~v1_relat_1(B_105) | ~v1_relat_1(k6_relat_1(k1_relat_1(B_105))) | ~v1_relat_1(B_105))), inference(superposition, [status(thm), theory('equality')], [c_355, c_5788])).
% 31.37/21.92  tff(c_5879, plain, (![B_295]: (r1_tarski(k2_relat_1(k4_relat_1(B_295)), k1_relat_1(B_295)) | ~v1_relat_1(k4_relat_1(B_295)) | ~v1_relat_1(B_295))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_22, c_36, c_34, c_36, c_5836])).
% 31.37/21.92  tff(c_5897, plain, (![A_208, A_62]: (r1_tarski(k2_relat_1(k7_relat_1(k6_relat_1(A_208), A_62)), k1_relat_1(k7_relat_1(k6_relat_1(A_62), A_208))) | ~v1_relat_1(k4_relat_1(k7_relat_1(k6_relat_1(A_62), A_208))) | ~v1_relat_1(k7_relat_1(k6_relat_1(A_62), A_208)))), inference(superposition, [status(thm), theory('equality')], [c_2362, c_5879])).
% 31.37/21.92  tff(c_5917, plain, (![A_208, A_62]: (r1_tarski(k9_relat_1(k6_relat_1(A_208), A_62), k3_xboole_0(A_62, A_208)))), inference(demodulation, [status(thm), theory('equality')], [c_2251, c_2251, c_2362, c_2650, c_230, c_5897])).
% 31.37/21.92  tff(c_731, plain, (![B_123, A_124]: (k5_relat_1(B_123, k6_relat_1(A_124))=B_123 | ~r1_tarski(k2_relat_1(B_123), A_124) | ~v1_relat_1(B_123))), inference(cnfTransformation, [status(thm)], [f_100])).
% 31.37/21.92  tff(c_750, plain, (![A_53, A_124]: (k5_relat_1(k6_relat_1(A_53), k6_relat_1(A_124))=k6_relat_1(A_53) | ~r1_tarski(A_53, A_124) | ~v1_relat_1(k6_relat_1(A_53)))), inference(superposition, [status(thm), theory('equality')], [c_34, c_731])).
% 31.37/21.92  tff(c_757, plain, (![A_53, A_124]: (k5_relat_1(k6_relat_1(A_53), k6_relat_1(A_124))=k6_relat_1(A_53) | ~r1_tarski(A_53, A_124))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_750])).
% 31.37/21.92  tff(c_1114, plain, (![A_124, A_53]: (k9_relat_1(k6_relat_1(A_124), A_53)=k2_relat_1(k6_relat_1(A_53)) | ~v1_relat_1(k6_relat_1(A_124)) | ~r1_tarski(A_53, A_124))), inference(superposition, [status(thm), theory('equality')], [c_757, c_1083])).
% 31.37/21.92  tff(c_1138, plain, (![A_124, A_53]: (k9_relat_1(k6_relat_1(A_124), A_53)=A_53 | ~r1_tarski(A_53, A_124))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_34, c_1114])).
% 31.37/21.92  tff(c_827, plain, (![A_130, A_131]: (k5_relat_1(k6_relat_1(A_130), k6_relat_1(A_131))=k6_relat_1(A_130) | ~r1_tarski(A_130, A_131))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_750])).
% 31.37/21.92  tff(c_846, plain, (![A_131, A_130]: (k7_relat_1(k6_relat_1(A_131), A_130)=k6_relat_1(A_130) | ~v1_relat_1(k6_relat_1(A_131)) | ~r1_tarski(A_130, A_131))), inference(superposition, [status(thm), theory('equality')], [c_827, c_46])).
% 31.37/21.92  tff(c_890, plain, (![A_131, A_130]: (k7_relat_1(k6_relat_1(A_131), A_130)=k6_relat_1(A_130) | ~r1_tarski(A_130, A_131))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_846])).
% 31.37/21.92  tff(c_1398, plain, (![A_167, B_168, C_169]: (k5_relat_1(k5_relat_1(A_167, B_168), C_169)=k5_relat_1(A_167, k5_relat_1(B_168, C_169)) | ~v1_relat_1(C_169) | ~v1_relat_1(B_168) | ~v1_relat_1(A_167))), inference(cnfTransformation, [status(thm)], [f_82])).
% 31.37/21.92  tff(c_1439, plain, (![A_62, B_63, C_169]: (k5_relat_1(k6_relat_1(A_62), k5_relat_1(B_63, C_169))=k5_relat_1(k7_relat_1(B_63, A_62), C_169) | ~v1_relat_1(C_169) | ~v1_relat_1(B_63) | ~v1_relat_1(k6_relat_1(A_62)) | ~v1_relat_1(B_63))), inference(superposition, [status(thm), theory('equality')], [c_46, c_1398])).
% 31.37/21.92  tff(c_3324, plain, (![A_243, B_244, C_245]: (k5_relat_1(k6_relat_1(A_243), k5_relat_1(B_244, C_245))=k5_relat_1(k7_relat_1(B_244, A_243), C_245) | ~v1_relat_1(C_245) | ~v1_relat_1(B_244))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_1439])).
% 31.37/21.92  tff(c_3401, plain, (![A_62, A_243, B_63]: (k5_relat_1(k7_relat_1(k6_relat_1(A_62), A_243), B_63)=k5_relat_1(k6_relat_1(A_243), k7_relat_1(B_63, A_62)) | ~v1_relat_1(B_63) | ~v1_relat_1(k6_relat_1(A_62)) | ~v1_relat_1(B_63))), inference(superposition, [status(thm), theory('equality')], [c_46, c_3324])).
% 31.37/21.92  tff(c_22317, plain, (![A_500, A_501, B_502]: (k5_relat_1(k7_relat_1(k6_relat_1(A_500), A_501), B_502)=k5_relat_1(k6_relat_1(A_501), k7_relat_1(B_502, A_500)) | ~v1_relat_1(B_502))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_3401])).
% 31.37/21.92  tff(c_22399, plain, (![A_501, A_53, A_500]: (r1_tarski(k2_relat_1(k5_relat_1(k6_relat_1(A_501), k7_relat_1(k6_relat_1(A_53), A_500))), A_53) | ~v1_relat_1(k7_relat_1(k6_relat_1(A_500), A_501)) | ~v1_relat_1(k6_relat_1(A_53)))), inference(superposition, [status(thm), theory('equality')], [c_22317, c_307])).
% 31.37/21.92  tff(c_23044, plain, (![A_521, A_522, A_523]: (r1_tarski(k2_relat_1(k5_relat_1(k6_relat_1(A_521), k7_relat_1(k6_relat_1(A_522), A_523))), A_522))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_2251, c_22399])).
% 31.37/21.92  tff(c_23103, plain, (![A_521, A_130, A_131]: (r1_tarski(k2_relat_1(k5_relat_1(k6_relat_1(A_521), k6_relat_1(A_130))), A_131) | ~r1_tarski(A_130, A_131))), inference(superposition, [status(thm), theory('equality')], [c_890, c_23044])).
% 31.37/21.92  tff(c_23230, plain, (![A_527, A_528, A_529]: (r1_tarski(k9_relat_1(k6_relat_1(A_527), A_528), A_529) | ~r1_tarski(A_527, A_529))), inference(demodulation, [status(thm), theory('equality')], [c_2650, c_2433, c_23103])).
% 31.37/21.92  tff(c_23771, plain, (![A_541, A_542, A_543]: (r1_tarski(A_541, A_542) | ~r1_tarski(A_543, A_542) | ~r1_tarski(A_541, A_543))), inference(superposition, [status(thm), theory('equality')], [c_1138, c_23230])).
% 31.37/21.92  tff(c_24325, plain, (![A_550, A_551, B_552]: (r1_tarski(A_550, A_551) | ~r1_tarski(A_550, k3_xboole_0(A_551, B_552)))), inference(resolution, [status(thm)], [c_2, c_23771])).
% 31.37/21.92  tff(c_24597, plain, (![A_208, A_62]: (r1_tarski(k9_relat_1(k6_relat_1(A_208), A_62), A_62))), inference(resolution, [status(thm)], [c_5917, c_24325])).
% 31.37/21.92  tff(c_1449, plain, (![A_167, B_168]: (k5_relat_1(A_167, k5_relat_1(B_168, k6_relat_1(k2_relat_1(k5_relat_1(A_167, B_168)))))=k5_relat_1(A_167, B_168) | ~v1_relat_1(k6_relat_1(k2_relat_1(k5_relat_1(A_167, B_168)))) | ~v1_relat_1(B_168) | ~v1_relat_1(A_167) | ~v1_relat_1(k5_relat_1(A_167, B_168)))), inference(superposition, [status(thm), theory('equality')], [c_42, c_1398])).
% 31.37/21.92  tff(c_6858, plain, (![A_308, B_309]: (k5_relat_1(A_308, k5_relat_1(B_309, k6_relat_1(k2_relat_1(k5_relat_1(A_308, B_309)))))=k5_relat_1(A_308, B_309) | ~v1_relat_1(B_309) | ~v1_relat_1(A_308) | ~v1_relat_1(k5_relat_1(A_308, B_309)))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_1449])).
% 31.37/21.92  tff(c_6995, plain, (![A_308, A_62]: (k5_relat_1(A_308, k7_relat_1(k6_relat_1(k2_relat_1(k5_relat_1(A_308, k6_relat_1(A_62)))), A_62))=k5_relat_1(A_308, k6_relat_1(A_62)) | ~v1_relat_1(k6_relat_1(A_62)) | ~v1_relat_1(A_308) | ~v1_relat_1(k5_relat_1(A_308, k6_relat_1(A_62))) | ~v1_relat_1(k6_relat_1(k2_relat_1(k5_relat_1(A_308, k6_relat_1(A_62))))))), inference(superposition, [status(thm), theory('equality')], [c_46, c_6858])).
% 31.37/21.92  tff(c_119770, plain, (![A_1381, A_1382]: (k5_relat_1(A_1381, k7_relat_1(k6_relat_1(k2_relat_1(k5_relat_1(A_1381, k6_relat_1(A_1382)))), A_1382))=k5_relat_1(A_1381, k6_relat_1(A_1382)) | ~v1_relat_1(A_1381) | ~v1_relat_1(k5_relat_1(A_1381, k6_relat_1(A_1382))))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_22, c_6995])).
% 31.37/21.92  tff(c_350, plain, (![A_104, A_53, A_89]: (k5_relat_1(k6_relat_1(A_104), k7_relat_1(k6_relat_1(A_53), A_89))=k7_relat_1(k6_relat_1(A_53), A_89) | ~r1_tarski(k3_xboole_0(A_53, A_89), A_104) | ~v1_relat_1(k7_relat_1(k6_relat_1(A_53), A_89)))), inference(superposition, [status(thm), theory('equality')], [c_230, c_340])).
% 31.37/21.92  tff(c_105576, plain, (![A_104, A_53, A_89]: (k5_relat_1(k6_relat_1(A_104), k7_relat_1(k6_relat_1(A_53), A_89))=k7_relat_1(k6_relat_1(A_53), A_89) | ~r1_tarski(k3_xboole_0(A_53, A_89), A_104))), inference(demodulation, [status(thm), theory('equality')], [c_2251, c_350])).
% 31.37/21.92  tff(c_119808, plain, (![A_104, A_1382]: (k7_relat_1(k6_relat_1(k2_relat_1(k5_relat_1(k6_relat_1(A_104), k6_relat_1(A_1382)))), A_1382)=k5_relat_1(k6_relat_1(A_104), k6_relat_1(A_1382)) | ~r1_tarski(k3_xboole_0(k2_relat_1(k5_relat_1(k6_relat_1(A_104), k6_relat_1(A_1382))), A_1382), A_104) | ~v1_relat_1(k6_relat_1(A_104)) | ~v1_relat_1(k5_relat_1(k6_relat_1(A_104), k6_relat_1(A_1382))))), inference(superposition, [status(thm), theory('equality')], [c_119770, c_105576])).
% 31.37/21.92  tff(c_120393, plain, (![A_1383, A_1384]: (k7_relat_1(k6_relat_1(k9_relat_1(k6_relat_1(A_1383), A_1384)), A_1383)=k7_relat_1(k6_relat_1(A_1383), A_1384))), inference(demodulation, [status(thm), theory('equality')], [c_2251, c_2433, c_22, c_24597, c_1182, c_2650, c_2433, c_2650, c_2433, c_2433, c_119808])).
% 31.37/21.92  tff(c_44, plain, (![B_61, A_60]: (k3_xboole_0(k1_relat_1(B_61), A_60)=k1_relat_1(k7_relat_1(B_61, A_60)) | ~v1_relat_1(B_61))), inference(cnfTransformation, [status(thm)], [f_108])).
% 31.37/21.92  tff(c_246, plain, (![A_80]: (k3_xboole_0(A_80, A_80)=A_80)), inference(demodulation, [status(thm), theory('equality')], [c_32, c_243])).
% 31.37/21.92  tff(c_97, plain, (![A_76]: (k5_relat_1(A_76, k6_relat_1(k2_relat_1(A_76)))=A_76 | ~v1_relat_1(A_76))), inference(cnfTransformation, [status(thm)], [f_104])).
% 31.37/21.92  tff(c_109, plain, (![A_53]: (k5_relat_1(k6_relat_1(A_53), k6_relat_1(A_53))=k6_relat_1(A_53) | ~v1_relat_1(k6_relat_1(A_53)))), inference(superposition, [status(thm), theory('equality')], [c_34, c_97])).
% 31.37/21.92  tff(c_115, plain, (![A_53]: (k5_relat_1(k6_relat_1(A_53), k6_relat_1(A_53))=k6_relat_1(A_53))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_109])).
% 31.37/21.92  tff(c_1442, plain, (![A_53, C_169]: (k5_relat_1(k6_relat_1(A_53), k5_relat_1(k6_relat_1(A_53), C_169))=k5_relat_1(k6_relat_1(A_53), C_169) | ~v1_relat_1(C_169) | ~v1_relat_1(k6_relat_1(A_53)) | ~v1_relat_1(k6_relat_1(A_53)))), inference(superposition, [status(thm), theory('equality')], [c_115, c_1398])).
% 31.37/21.92  tff(c_14203, plain, (![A_418, C_419]: (k5_relat_1(k6_relat_1(A_418), k5_relat_1(k6_relat_1(A_418), C_419))=k5_relat_1(k6_relat_1(A_418), C_419) | ~v1_relat_1(C_419))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_22, c_1442])).
% 31.37/21.92  tff(c_14319, plain, (![A_200, A_62]: (k5_relat_1(k6_relat_1(A_200), k7_relat_1(k6_relat_1(A_62), A_200))=k5_relat_1(k6_relat_1(A_200), k6_relat_1(A_62)) | ~v1_relat_1(k6_relat_1(A_62)))), inference(superposition, [status(thm), theory('equality')], [c_2433, c_14203])).
% 31.37/21.92  tff(c_14565, plain, (![A_424, A_425]: (k5_relat_1(k6_relat_1(A_424), k7_relat_1(k6_relat_1(A_425), A_424))=k7_relat_1(k6_relat_1(A_425), A_424))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_2433, c_14319])).
% 31.37/21.92  tff(c_14623, plain, (![A_425, A_424]: (k7_relat_1(k7_relat_1(k6_relat_1(A_425), A_424), A_424)=k7_relat_1(k6_relat_1(A_425), A_424) | ~v1_relat_1(k7_relat_1(k6_relat_1(A_425), A_424)))), inference(superposition, [status(thm), theory('equality')], [c_14565, c_46])).
% 31.37/21.92  tff(c_14722, plain, (![A_426, A_427]: (k7_relat_1(k7_relat_1(k6_relat_1(A_426), A_427), A_427)=k7_relat_1(k6_relat_1(A_426), A_427))), inference(demodulation, [status(thm), theory('equality')], [c_2251, c_14623])).
% 31.37/21.92  tff(c_682, plain, (![A_119, B_120]: (k3_xboole_0(k3_xboole_0(A_119, B_120), A_119)=k3_xboole_0(A_119, B_120))), inference(resolution, [status(thm)], [c_2, c_651])).
% 31.37/21.92  tff(c_703, plain, (![B_61, A_60]: (k3_xboole_0(k1_relat_1(k7_relat_1(B_61, A_60)), k1_relat_1(B_61))=k3_xboole_0(k1_relat_1(B_61), A_60) | ~v1_relat_1(B_61))), inference(superposition, [status(thm), theory('equality')], [c_44, c_682])).
% 31.37/21.92  tff(c_14734, plain, (![A_426, A_427]: (k3_xboole_0(k1_relat_1(k7_relat_1(k6_relat_1(A_426), A_427)), k1_relat_1(k7_relat_1(k6_relat_1(A_426), A_427)))=k3_xboole_0(k1_relat_1(k7_relat_1(k6_relat_1(A_426), A_427)), A_427) | ~v1_relat_1(k7_relat_1(k6_relat_1(A_426), A_427)))), inference(superposition, [status(thm), theory('equality')], [c_14722, c_703])).
% 31.37/21.92  tff(c_14849, plain, (![A_428, A_429]: (k3_xboole_0(k3_xboole_0(A_428, A_429), A_429)=k3_xboole_0(A_428, A_429))), inference(demodulation, [status(thm), theory('equality')], [c_2251, c_246, c_230, c_230, c_230, c_14734])).
% 31.37/21.92  tff(c_15056, plain, (![B_61, A_60]: (k3_xboole_0(k1_relat_1(k7_relat_1(B_61, A_60)), A_60)=k3_xboole_0(k1_relat_1(B_61), A_60) | ~v1_relat_1(B_61))), inference(superposition, [status(thm), theory('equality')], [c_44, c_14849])).
% 31.37/21.92  tff(c_120710, plain, (![A_1383, A_1384]: (k3_xboole_0(k1_relat_1(k6_relat_1(k9_relat_1(k6_relat_1(A_1383), A_1384))), A_1383)=k3_xboole_0(k1_relat_1(k7_relat_1(k6_relat_1(A_1383), A_1384)), A_1383) | ~v1_relat_1(k6_relat_1(k9_relat_1(k6_relat_1(A_1383), A_1384))))), inference(superposition, [status(thm), theory('equality')], [c_120393, c_15056])).
% 31.37/21.92  tff(c_121061, plain, (![A_1383, A_1384]: (k9_relat_1(k6_relat_1(A_1383), A_1384)=k3_xboole_0(A_1383, A_1384))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_1182, c_680, c_230, c_32, c_120710])).
% 31.37/21.92  tff(c_1133, plain, (![A_53, A_143]: (r1_tarski(k9_relat_1(k6_relat_1(A_53), A_143), A_53))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_22, c_1096])).
% 31.37/21.92  tff(c_564, plain, (![A_114, A_113]: (k7_relat_1(k6_relat_1(A_114), A_113)=k6_relat_1(A_114) | ~r1_tarski(A_114, A_113))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_522])).
% 31.37/21.92  tff(c_120769, plain, (![A_1383, A_1384]: (k6_relat_1(k9_relat_1(k6_relat_1(A_1383), A_1384))=k7_relat_1(k6_relat_1(A_1383), A_1384) | ~r1_tarski(k9_relat_1(k6_relat_1(A_1383), A_1384), A_1383))), inference(superposition, [status(thm), theory('equality')], [c_120393, c_564])).
% 31.37/21.92  tff(c_121090, plain, (![A_1383, A_1384]: (k6_relat_1(k9_relat_1(k6_relat_1(A_1383), A_1384))=k7_relat_1(k6_relat_1(A_1383), A_1384))), inference(demodulation, [status(thm), theory('equality')], [c_1133, c_120769])).
% 31.37/21.92  tff(c_134900, plain, (![A_1383, A_1384]: (k7_relat_1(k6_relat_1(A_1383), A_1384)=k6_relat_1(k3_xboole_0(A_1383, A_1384)))), inference(demodulation, [status(thm), theory('equality')], [c_121061, c_121090])).
% 31.37/21.92  tff(c_48, plain, (k5_relat_1(k6_relat_1('#skF_2'), k6_relat_1('#skF_1'))!=k6_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_115])).
% 31.37/21.92  tff(c_155, plain, (k7_relat_1(k6_relat_1('#skF_1'), '#skF_2')!=k6_relat_1(k3_xboole_0('#skF_1', '#skF_2')) | ~v1_relat_1(k6_relat_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_145, c_48])).
% 31.37/21.92  tff(c_177, plain, (k7_relat_1(k6_relat_1('#skF_1'), '#skF_2')!=k6_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_155])).
% 31.37/21.92  tff(c_135005, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_134900, c_177])).
% 31.37/21.92  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 31.37/21.92  
% 31.37/21.92  Inference rules
% 31.37/21.92  ----------------------
% 31.37/21.92  #Ref     : 0
% 31.37/21.92  #Sup     : 33095
% 31.37/21.92  #Fact    : 0
% 31.37/21.92  #Define  : 0
% 31.37/21.92  #Split   : 2
% 31.37/21.92  #Chain   : 0
% 31.37/21.92  #Close   : 0
% 31.37/21.92  
% 31.37/21.92  Ordering : KBO
% 31.37/21.92  
% 31.37/21.92  Simplification rules
% 31.37/21.92  ----------------------
% 31.37/21.92  #Subsume      : 5433
% 31.37/21.92  #Demod        : 25390
% 31.37/21.92  #Tautology    : 8711
% 31.37/21.92  #SimpNegUnit  : 0
% 31.37/21.92  #BackRed      : 234
% 31.37/21.92  
% 31.37/21.92  #Partial instantiations: 0
% 31.37/21.92  #Strategies tried      : 1
% 31.37/21.92  
% 31.37/21.92  Timing (in seconds)
% 31.37/21.92  ----------------------
% 31.37/21.93  Preprocessing        : 0.35
% 31.37/21.93  Parsing              : 0.19
% 31.37/21.93  CNF conversion       : 0.02
% 31.37/21.93  Main loop            : 20.79
% 31.37/21.93  Inferencing          : 2.80
% 31.37/21.93  Reduction            : 8.65
% 31.37/21.93  Demodulation         : 7.54
% 31.62/21.93  BG Simplification    : 0.41
% 31.62/21.93  Subsumption          : 7.81
% 31.62/21.93  Abstraction          : 0.64
% 31.62/21.93  MUC search           : 0.00
% 31.62/21.93  Cooper               : 0.00
% 31.62/21.93  Total                : 21.19
% 31.62/21.93  Index Insertion      : 0.00
% 31.62/21.93  Index Deletion       : 0.00
% 31.62/21.93  Index Matching       : 0.00
% 31.62/21.93  BG Taut test         : 0.00
%------------------------------------------------------------------------------

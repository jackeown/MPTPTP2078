%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:03:33 EST 2020

% Result     : Theorem 5.06s
% Output     : CNFRefutation 5.06s
% Verified   : 
% Statistics : Number of formulae       :  104 ( 310 expanded)
%              Number of leaves         :   39 ( 127 expanded)
%              Depth                    :   16
%              Number of atoms          :  157 ( 564 expanded)
%              Number of equality atoms :   65 ( 178 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    6 (   2 average)

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

tff(f_117,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v4_relat_1(k6_relat_1(A),A)
      & v5_relat_1(k6_relat_1(A),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc24_relat_1)).

tff(f_93,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k7_relat_1(B,k3_xboole_0(k1_relat_1(B),A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t192_relat_1)).

tff(f_71,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_111,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k5_relat_1(k6_relat_1(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k8_relat_1(A,B) = k5_relat_1(B,k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_relat_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k8_relat_1(A,B)) = k3_xboole_0(k2_relat_1(B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t119_relat_1)).

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

tff(f_41,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_relat_1(B) )
     => v1_relat_1(k5_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).

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

tff(f_107,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k2_relat_1(B),A)
       => k5_relat_1(B,k6_relat_1(A)) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_relat_1)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k7_relat_1(k8_relat_1(A,C),B) = k8_relat_1(A,k7_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t140_relat_1)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k7_relat_1(k7_relat_1(C,A),B) = k7_relat_1(C,k3_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_relat_1)).

tff(f_120,negated_conjecture,(
    ~ ! [A,B] : k5_relat_1(k6_relat_1(B),k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_funct_1)).

tff(c_48,plain,(
    ! [A_48] : v1_relat_1(k6_relat_1(A_48)) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_34,plain,(
    ! [A_40] : k1_relat_1(k6_relat_1(A_40)) = A_40 ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_273,plain,(
    ! [B_93,A_94] :
      ( k7_relat_1(B_93,k3_xboole_0(k1_relat_1(B_93),A_94)) = k7_relat_1(B_93,A_94)
      | ~ v1_relat_1(B_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_297,plain,(
    ! [A_40,A_94] :
      ( k7_relat_1(k6_relat_1(A_40),k3_xboole_0(A_40,A_94)) = k7_relat_1(k6_relat_1(A_40),A_94)
      | ~ v1_relat_1(k6_relat_1(A_40)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_273])).

tff(c_307,plain,(
    ! [A_40,A_94] : k7_relat_1(k6_relat_1(A_40),k3_xboole_0(A_40,A_94)) = k7_relat_1(k6_relat_1(A_40),A_94) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_297])).

tff(c_50,plain,(
    ! [A_48] : v4_relat_1(k6_relat_1(A_48),A_48) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_128,plain,(
    ! [B_66,A_67] :
      ( k7_relat_1(B_66,A_67) = B_66
      | ~ v4_relat_1(B_66,A_67)
      | ~ v1_relat_1(B_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_131,plain,(
    ! [A_48] :
      ( k7_relat_1(k6_relat_1(A_48),A_48) = k6_relat_1(A_48)
      | ~ v1_relat_1(k6_relat_1(A_48)) ) ),
    inference(resolution,[status(thm)],[c_50,c_128])).

tff(c_134,plain,(
    ! [A_48] : k7_relat_1(k6_relat_1(A_48),A_48) = k6_relat_1(A_48) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_131])).

tff(c_46,plain,(
    ! [A_46,B_47] :
      ( k5_relat_1(k6_relat_1(A_46),B_47) = k7_relat_1(B_47,A_46)
      | ~ v1_relat_1(B_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_192,plain,(
    ! [B_79,A_80] :
      ( k5_relat_1(B_79,k6_relat_1(A_80)) = k8_relat_1(A_80,B_79)
      | ~ v1_relat_1(B_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_219,plain,(
    ! [A_80,A_46] :
      ( k8_relat_1(A_80,k6_relat_1(A_46)) = k7_relat_1(k6_relat_1(A_80),A_46)
      | ~ v1_relat_1(k6_relat_1(A_46))
      | ~ v1_relat_1(k6_relat_1(A_80)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_192])).

tff(c_231,plain,(
    ! [A_80,A_46] : k8_relat_1(A_80,k6_relat_1(A_46)) = k7_relat_1(k6_relat_1(A_80),A_46) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_48,c_219])).

tff(c_36,plain,(
    ! [A_40] : k2_relat_1(k6_relat_1(A_40)) = A_40 ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_234,plain,(
    ! [B_85,A_86] :
      ( k3_xboole_0(k2_relat_1(B_85),A_86) = k2_relat_1(k8_relat_1(A_86,B_85))
      | ~ v1_relat_1(B_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_243,plain,(
    ! [A_86,A_40] :
      ( k2_relat_1(k8_relat_1(A_86,k6_relat_1(A_40))) = k3_xboole_0(A_40,A_86)
      | ~ v1_relat_1(k6_relat_1(A_40)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_234])).

tff(c_247,plain,(
    ! [A_86,A_40] : k2_relat_1(k8_relat_1(A_86,k6_relat_1(A_40))) = k3_xboole_0(A_40,A_86) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_243])).

tff(c_308,plain,(
    ! [A_86,A_40] : k2_relat_1(k7_relat_1(k6_relat_1(A_86),A_40)) = k3_xboole_0(A_40,A_86) ),
    inference(demodulation,[status(thm),theory(equality)],[c_231,c_247])).

tff(c_20,plain,(
    ! [B_26,A_25] :
      ( k5_relat_1(B_26,k6_relat_1(A_25)) = k8_relat_1(A_25,B_26)
      | ~ v1_relat_1(B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_38,plain,(
    ! [A_41] : k4_relat_1(k6_relat_1(A_41)) = k6_relat_1(A_41) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_1201,plain,(
    ! [B_153,A_154] :
      ( k5_relat_1(k4_relat_1(B_153),k4_relat_1(A_154)) = k4_relat_1(k5_relat_1(A_154,B_153))
      | ~ v1_relat_1(B_153)
      | ~ v1_relat_1(A_154) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_1219,plain,(
    ! [A_41,A_154] :
      ( k5_relat_1(k6_relat_1(A_41),k4_relat_1(A_154)) = k4_relat_1(k5_relat_1(A_154,k6_relat_1(A_41)))
      | ~ v1_relat_1(k6_relat_1(A_41))
      | ~ v1_relat_1(A_154) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_1201])).

tff(c_1951,plain,(
    ! [A_184,A_185] :
      ( k5_relat_1(k6_relat_1(A_184),k4_relat_1(A_185)) = k4_relat_1(k5_relat_1(A_185,k6_relat_1(A_184)))
      | ~ v1_relat_1(A_185) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_1219])).

tff(c_1976,plain,(
    ! [A_41,A_184] :
      ( k4_relat_1(k5_relat_1(k6_relat_1(A_41),k6_relat_1(A_184))) = k5_relat_1(k6_relat_1(A_184),k6_relat_1(A_41))
      | ~ v1_relat_1(k6_relat_1(A_41)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_1951])).

tff(c_2069,plain,(
    ! [A_196,A_197] : k4_relat_1(k5_relat_1(k6_relat_1(A_196),k6_relat_1(A_197))) = k5_relat_1(k6_relat_1(A_197),k6_relat_1(A_196)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_1976])).

tff(c_2104,plain,(
    ! [A_25,A_196] :
      ( k5_relat_1(k6_relat_1(A_25),k6_relat_1(A_196)) = k4_relat_1(k8_relat_1(A_25,k6_relat_1(A_196)))
      | ~ v1_relat_1(k6_relat_1(A_196)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_2069])).

tff(c_2467,plain,(
    ! [A_208,A_209] : k5_relat_1(k6_relat_1(A_208),k6_relat_1(A_209)) = k4_relat_1(k7_relat_1(k6_relat_1(A_208),A_209)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_231,c_2104])).

tff(c_2510,plain,(
    ! [A_208,A_25] :
      ( k4_relat_1(k7_relat_1(k6_relat_1(A_208),A_25)) = k8_relat_1(A_25,k6_relat_1(A_208))
      | ~ v1_relat_1(k6_relat_1(A_208)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_2467])).

tff(c_2536,plain,(
    ! [A_208,A_25] : k4_relat_1(k7_relat_1(k6_relat_1(A_208),A_25)) = k7_relat_1(k6_relat_1(A_25),A_208) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_231,c_2510])).

tff(c_24,plain,(
    ! [B_31,A_30] :
      ( k7_relat_1(B_31,k3_xboole_0(k1_relat_1(B_31),A_30)) = k7_relat_1(B_31,A_30)
      | ~ v1_relat_1(B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_2778,plain,(
    ! [A_220,A_221] : k4_relat_1(k7_relat_1(k6_relat_1(A_220),A_221)) = k7_relat_1(k6_relat_1(A_221),A_220) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_231,c_2510])).

tff(c_2812,plain,(
    ! [A_220,A_30] :
      ( k7_relat_1(k6_relat_1(k3_xboole_0(k1_relat_1(k6_relat_1(A_220)),A_30)),A_220) = k4_relat_1(k7_relat_1(k6_relat_1(A_220),A_30))
      | ~ v1_relat_1(k6_relat_1(A_220)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_2778])).

tff(c_3093,plain,(
    ! [A_232,A_233] : k7_relat_1(k6_relat_1(k3_xboole_0(A_232,A_233)),A_232) = k7_relat_1(k6_relat_1(A_233),A_232) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_2536,c_34,c_2812])).

tff(c_3134,plain,(
    ! [A_232,A_233] : k3_xboole_0(A_232,k3_xboole_0(A_232,A_233)) = k2_relat_1(k7_relat_1(k6_relat_1(A_233),A_232)) ),
    inference(superposition,[status(thm),theory(equality)],[c_3093,c_308])).

tff(c_3210,plain,(
    ! [A_232,A_233] : k3_xboole_0(A_232,k3_xboole_0(A_232,A_233)) = k3_xboole_0(A_232,A_233) ),
    inference(demodulation,[status(thm),theory(equality)],[c_308,c_3134])).

tff(c_250,plain,(
    ! [A_87,A_88] : k8_relat_1(A_87,k6_relat_1(A_88)) = k7_relat_1(k6_relat_1(A_87),A_88) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_48,c_219])).

tff(c_12,plain,(
    ! [A_17,B_18] :
      ( v1_relat_1(k5_relat_1(A_17,B_18))
      | ~ v1_relat_1(B_18)
      | ~ v1_relat_1(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_209,plain,(
    ! [A_80,B_79] :
      ( v1_relat_1(k8_relat_1(A_80,B_79))
      | ~ v1_relat_1(k6_relat_1(A_80))
      | ~ v1_relat_1(B_79)
      | ~ v1_relat_1(B_79) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_192,c_12])).

tff(c_226,plain,(
    ! [A_80,B_79] :
      ( v1_relat_1(k8_relat_1(A_80,B_79))
      | ~ v1_relat_1(B_79) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_209])).

tff(c_256,plain,(
    ! [A_87,A_88] :
      ( v1_relat_1(k7_relat_1(k6_relat_1(A_87),A_88))
      | ~ v1_relat_1(k6_relat_1(A_88)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_250,c_226])).

tff(c_262,plain,(
    ! [A_87,A_88] : v1_relat_1(k7_relat_1(k6_relat_1(A_87),A_88)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_256])).

tff(c_42,plain,(
    ! [B_43,A_42] :
      ( r1_tarski(k5_relat_1(B_43,k6_relat_1(A_42)),B_43)
      | ~ v1_relat_1(B_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_206,plain,(
    ! [A_80,B_79] :
      ( r1_tarski(k8_relat_1(A_80,B_79),B_79)
      | ~ v1_relat_1(B_79)
      | ~ v1_relat_1(B_79) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_192,c_42])).

tff(c_635,plain,(
    ! [A_121,B_122] :
      ( r1_tarski(k2_relat_1(A_121),k2_relat_1(B_122))
      | ~ r1_tarski(A_121,B_122)
      | ~ v1_relat_1(B_122)
      | ~ v1_relat_1(A_121) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_656,plain,(
    ! [A_121,A_40] :
      ( r1_tarski(k2_relat_1(A_121),A_40)
      | ~ r1_tarski(A_121,k6_relat_1(A_40))
      | ~ v1_relat_1(k6_relat_1(A_40))
      | ~ v1_relat_1(A_121) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_635])).

tff(c_709,plain,(
    ! [A_125,A_126] :
      ( r1_tarski(k2_relat_1(A_125),A_126)
      | ~ r1_tarski(A_125,k6_relat_1(A_126))
      | ~ v1_relat_1(A_125) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_656])).

tff(c_44,plain,(
    ! [B_45,A_44] :
      ( k5_relat_1(B_45,k6_relat_1(A_44)) = B_45
      | ~ r1_tarski(k2_relat_1(B_45),A_44)
      | ~ v1_relat_1(B_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_1588,plain,(
    ! [A_172,A_173] :
      ( k5_relat_1(A_172,k6_relat_1(A_173)) = A_172
      | ~ r1_tarski(A_172,k6_relat_1(A_173))
      | ~ v1_relat_1(A_172) ) ),
    inference(resolution,[status(thm)],[c_709,c_44])).

tff(c_1617,plain,(
    ! [A_80,A_173] :
      ( k5_relat_1(k8_relat_1(A_80,k6_relat_1(A_173)),k6_relat_1(A_173)) = k8_relat_1(A_80,k6_relat_1(A_173))
      | ~ v1_relat_1(k8_relat_1(A_80,k6_relat_1(A_173)))
      | ~ v1_relat_1(k6_relat_1(A_173)) ) ),
    inference(resolution,[status(thm)],[c_206,c_1588])).

tff(c_4137,plain,(
    ! [A_254,A_255] : k5_relat_1(k7_relat_1(k6_relat_1(A_254),A_255),k6_relat_1(A_255)) = k7_relat_1(k6_relat_1(A_254),A_255) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_262,c_231,c_231,c_231,c_1617])).

tff(c_4156,plain,(
    ! [A_255,A_254] :
      ( k8_relat_1(A_255,k7_relat_1(k6_relat_1(A_254),A_255)) = k7_relat_1(k6_relat_1(A_254),A_255)
      | ~ v1_relat_1(k7_relat_1(k6_relat_1(A_254),A_255)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4137,c_20])).

tff(c_4222,plain,(
    ! [A_256,A_257] : k8_relat_1(A_256,k7_relat_1(k6_relat_1(A_257),A_256)) = k7_relat_1(k6_relat_1(A_257),A_256) ),
    inference(demodulation,[status(thm),theory(equality)],[c_262,c_4156])).

tff(c_22,plain,(
    ! [A_27,C_29,B_28] :
      ( k8_relat_1(A_27,k7_relat_1(C_29,B_28)) = k7_relat_1(k8_relat_1(A_27,C_29),B_28)
      | ~ v1_relat_1(C_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_4243,plain,(
    ! [A_256,A_257] :
      ( k7_relat_1(k8_relat_1(A_256,k6_relat_1(A_257)),A_256) = k7_relat_1(k6_relat_1(A_257),A_256)
      | ~ v1_relat_1(k6_relat_1(A_257)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4222,c_22])).

tff(c_4436,plain,(
    ! [A_262,A_263] : k7_relat_1(k7_relat_1(k6_relat_1(A_262),A_263),A_262) = k7_relat_1(k6_relat_1(A_263),A_262) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_231,c_4243])).

tff(c_16,plain,(
    ! [C_22,A_20,B_21] :
      ( k7_relat_1(k7_relat_1(C_22,A_20),B_21) = k7_relat_1(C_22,k3_xboole_0(A_20,B_21))
      | ~ v1_relat_1(C_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_4460,plain,(
    ! [A_262,A_263] :
      ( k7_relat_1(k6_relat_1(A_262),k3_xboole_0(A_263,A_262)) = k7_relat_1(k6_relat_1(A_263),A_262)
      | ~ v1_relat_1(k6_relat_1(A_262)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4436,c_16])).

tff(c_4716,plain,(
    ! [A_268,A_269] : k7_relat_1(k6_relat_1(A_268),k3_xboole_0(A_269,A_268)) = k7_relat_1(k6_relat_1(A_269),A_268) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_4460])).

tff(c_4809,plain,(
    ! [A_232,A_233] : k7_relat_1(k6_relat_1(k3_xboole_0(A_232,A_233)),k3_xboole_0(A_232,A_233)) = k7_relat_1(k6_relat_1(A_232),k3_xboole_0(A_232,A_233)) ),
    inference(superposition,[status(thm),theory(equality)],[c_3210,c_4716])).

tff(c_4893,plain,(
    ! [A_232,A_233] : k7_relat_1(k6_relat_1(A_232),A_233) = k6_relat_1(k3_xboole_0(A_232,A_233)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_307,c_134,c_4809])).

tff(c_144,plain,(
    ! [A_69,B_70] :
      ( k5_relat_1(k6_relat_1(A_69),B_70) = k7_relat_1(B_70,A_69)
      | ~ v1_relat_1(B_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_54,plain,(
    k5_relat_1(k6_relat_1('#skF_2'),k6_relat_1('#skF_1')) != k6_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_160,plain,
    ( k7_relat_1(k6_relat_1('#skF_1'),'#skF_2') != k6_relat_1(k3_xboole_0('#skF_1','#skF_2'))
    | ~ v1_relat_1(k6_relat_1('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_144,c_54])).

tff(c_170,plain,(
    k7_relat_1(k6_relat_1('#skF_1'),'#skF_2') != k6_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_160])).

tff(c_5298,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4893,c_170])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n013.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:19:24 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.06/2.03  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.06/2.04  
% 5.06/2.04  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.06/2.05  %$ v5_relat_1 > v4_relat_1 > r1_tarski > v1_relat_1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k8_relat_1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k6_relat_1 > k4_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1
% 5.06/2.05  
% 5.06/2.05  %Foreground sorts:
% 5.06/2.05  
% 5.06/2.05  
% 5.06/2.05  %Background operators:
% 5.06/2.05  
% 5.06/2.05  
% 5.06/2.05  %Foreground operators:
% 5.06/2.05  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 5.06/2.05  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.06/2.05  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 5.06/2.05  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 5.06/2.05  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 5.06/2.05  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.06/2.05  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 5.06/2.05  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.06/2.05  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 5.06/2.05  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 5.06/2.05  tff('#skF_2', type, '#skF_2': $i).
% 5.06/2.05  tff('#skF_1', type, '#skF_1': $i).
% 5.06/2.05  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 5.06/2.05  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 5.06/2.05  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.06/2.05  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.06/2.05  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 5.06/2.05  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.06/2.05  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 5.06/2.05  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.06/2.05  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.06/2.05  tff(k4_relat_1, type, k4_relat_1: $i > $i).
% 5.06/2.05  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 5.06/2.05  
% 5.06/2.06  tff(f_117, axiom, (![A]: ((v1_relat_1(k6_relat_1(A)) & v4_relat_1(k6_relat_1(A), A)) & v5_relat_1(k6_relat_1(A), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc24_relat_1)).
% 5.06/2.06  tff(f_93, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 5.06/2.06  tff(f_65, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k7_relat_1(B, k3_xboole_0(k1_relat_1(B), A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t192_relat_1)).
% 5.06/2.06  tff(f_71, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t209_relat_1)).
% 5.06/2.06  tff(f_111, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_relat_1)).
% 5.06/2.06  tff(f_57, axiom, (![A, B]: (v1_relat_1(B) => (k8_relat_1(A, B) = k5_relat_1(B, k6_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t123_relat_1)).
% 5.06/2.06  tff(f_53, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k8_relat_1(A, B)) = k3_xboole_0(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t119_relat_1)).
% 5.06/2.06  tff(f_95, axiom, (![A]: (k4_relat_1(k6_relat_1(A)) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_relat_1)).
% 5.06/2.06  tff(f_89, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k4_relat_1(k5_relat_1(A, B)) = k5_relat_1(k4_relat_1(B), k4_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t54_relat_1)).
% 5.06/2.06  tff(f_41, axiom, (![A, B]: ((v1_relat_1(A) & v1_relat_1(B)) => v1_relat_1(k5_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k5_relat_1)).
% 5.06/2.06  tff(f_101, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k5_relat_1(B, k6_relat_1(A)), B) & r1_tarski(k5_relat_1(k6_relat_1(A), B), B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t76_relat_1)).
% 5.06/2.06  tff(f_82, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(A, B) => (r1_tarski(k1_relat_1(A), k1_relat_1(B)) & r1_tarski(k2_relat_1(A), k2_relat_1(B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_relat_1)).
% 5.06/2.06  tff(f_107, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k5_relat_1(B, k6_relat_1(A)) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_relat_1)).
% 5.06/2.06  tff(f_61, axiom, (![A, B, C]: (v1_relat_1(C) => (k7_relat_1(k8_relat_1(A, C), B) = k8_relat_1(A, k7_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t140_relat_1)).
% 5.06/2.06  tff(f_49, axiom, (![A, B, C]: (v1_relat_1(C) => (k7_relat_1(k7_relat_1(C, A), B) = k7_relat_1(C, k3_xboole_0(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_relat_1)).
% 5.06/2.06  tff(f_120, negated_conjecture, ~(![A, B]: (k5_relat_1(k6_relat_1(B), k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_funct_1)).
% 5.06/2.06  tff(c_48, plain, (![A_48]: (v1_relat_1(k6_relat_1(A_48)))), inference(cnfTransformation, [status(thm)], [f_117])).
% 5.06/2.06  tff(c_34, plain, (![A_40]: (k1_relat_1(k6_relat_1(A_40))=A_40)), inference(cnfTransformation, [status(thm)], [f_93])).
% 5.06/2.06  tff(c_273, plain, (![B_93, A_94]: (k7_relat_1(B_93, k3_xboole_0(k1_relat_1(B_93), A_94))=k7_relat_1(B_93, A_94) | ~v1_relat_1(B_93))), inference(cnfTransformation, [status(thm)], [f_65])).
% 5.06/2.06  tff(c_297, plain, (![A_40, A_94]: (k7_relat_1(k6_relat_1(A_40), k3_xboole_0(A_40, A_94))=k7_relat_1(k6_relat_1(A_40), A_94) | ~v1_relat_1(k6_relat_1(A_40)))), inference(superposition, [status(thm), theory('equality')], [c_34, c_273])).
% 5.06/2.06  tff(c_307, plain, (![A_40, A_94]: (k7_relat_1(k6_relat_1(A_40), k3_xboole_0(A_40, A_94))=k7_relat_1(k6_relat_1(A_40), A_94))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_297])).
% 5.06/2.06  tff(c_50, plain, (![A_48]: (v4_relat_1(k6_relat_1(A_48), A_48))), inference(cnfTransformation, [status(thm)], [f_117])).
% 5.06/2.06  tff(c_128, plain, (![B_66, A_67]: (k7_relat_1(B_66, A_67)=B_66 | ~v4_relat_1(B_66, A_67) | ~v1_relat_1(B_66))), inference(cnfTransformation, [status(thm)], [f_71])).
% 5.06/2.06  tff(c_131, plain, (![A_48]: (k7_relat_1(k6_relat_1(A_48), A_48)=k6_relat_1(A_48) | ~v1_relat_1(k6_relat_1(A_48)))), inference(resolution, [status(thm)], [c_50, c_128])).
% 5.06/2.06  tff(c_134, plain, (![A_48]: (k7_relat_1(k6_relat_1(A_48), A_48)=k6_relat_1(A_48))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_131])).
% 5.06/2.06  tff(c_46, plain, (![A_46, B_47]: (k5_relat_1(k6_relat_1(A_46), B_47)=k7_relat_1(B_47, A_46) | ~v1_relat_1(B_47))), inference(cnfTransformation, [status(thm)], [f_111])).
% 5.06/2.06  tff(c_192, plain, (![B_79, A_80]: (k5_relat_1(B_79, k6_relat_1(A_80))=k8_relat_1(A_80, B_79) | ~v1_relat_1(B_79))), inference(cnfTransformation, [status(thm)], [f_57])).
% 5.06/2.06  tff(c_219, plain, (![A_80, A_46]: (k8_relat_1(A_80, k6_relat_1(A_46))=k7_relat_1(k6_relat_1(A_80), A_46) | ~v1_relat_1(k6_relat_1(A_46)) | ~v1_relat_1(k6_relat_1(A_80)))), inference(superposition, [status(thm), theory('equality')], [c_46, c_192])).
% 5.06/2.06  tff(c_231, plain, (![A_80, A_46]: (k8_relat_1(A_80, k6_relat_1(A_46))=k7_relat_1(k6_relat_1(A_80), A_46))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_48, c_219])).
% 5.06/2.06  tff(c_36, plain, (![A_40]: (k2_relat_1(k6_relat_1(A_40))=A_40)), inference(cnfTransformation, [status(thm)], [f_93])).
% 5.06/2.06  tff(c_234, plain, (![B_85, A_86]: (k3_xboole_0(k2_relat_1(B_85), A_86)=k2_relat_1(k8_relat_1(A_86, B_85)) | ~v1_relat_1(B_85))), inference(cnfTransformation, [status(thm)], [f_53])).
% 5.06/2.06  tff(c_243, plain, (![A_86, A_40]: (k2_relat_1(k8_relat_1(A_86, k6_relat_1(A_40)))=k3_xboole_0(A_40, A_86) | ~v1_relat_1(k6_relat_1(A_40)))), inference(superposition, [status(thm), theory('equality')], [c_36, c_234])).
% 5.06/2.06  tff(c_247, plain, (![A_86, A_40]: (k2_relat_1(k8_relat_1(A_86, k6_relat_1(A_40)))=k3_xboole_0(A_40, A_86))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_243])).
% 5.06/2.06  tff(c_308, plain, (![A_86, A_40]: (k2_relat_1(k7_relat_1(k6_relat_1(A_86), A_40))=k3_xboole_0(A_40, A_86))), inference(demodulation, [status(thm), theory('equality')], [c_231, c_247])).
% 5.06/2.06  tff(c_20, plain, (![B_26, A_25]: (k5_relat_1(B_26, k6_relat_1(A_25))=k8_relat_1(A_25, B_26) | ~v1_relat_1(B_26))), inference(cnfTransformation, [status(thm)], [f_57])).
% 5.06/2.06  tff(c_38, plain, (![A_41]: (k4_relat_1(k6_relat_1(A_41))=k6_relat_1(A_41))), inference(cnfTransformation, [status(thm)], [f_95])).
% 5.06/2.06  tff(c_1201, plain, (![B_153, A_154]: (k5_relat_1(k4_relat_1(B_153), k4_relat_1(A_154))=k4_relat_1(k5_relat_1(A_154, B_153)) | ~v1_relat_1(B_153) | ~v1_relat_1(A_154))), inference(cnfTransformation, [status(thm)], [f_89])).
% 5.06/2.06  tff(c_1219, plain, (![A_41, A_154]: (k5_relat_1(k6_relat_1(A_41), k4_relat_1(A_154))=k4_relat_1(k5_relat_1(A_154, k6_relat_1(A_41))) | ~v1_relat_1(k6_relat_1(A_41)) | ~v1_relat_1(A_154))), inference(superposition, [status(thm), theory('equality')], [c_38, c_1201])).
% 5.06/2.06  tff(c_1951, plain, (![A_184, A_185]: (k5_relat_1(k6_relat_1(A_184), k4_relat_1(A_185))=k4_relat_1(k5_relat_1(A_185, k6_relat_1(A_184))) | ~v1_relat_1(A_185))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_1219])).
% 5.06/2.06  tff(c_1976, plain, (![A_41, A_184]: (k4_relat_1(k5_relat_1(k6_relat_1(A_41), k6_relat_1(A_184)))=k5_relat_1(k6_relat_1(A_184), k6_relat_1(A_41)) | ~v1_relat_1(k6_relat_1(A_41)))), inference(superposition, [status(thm), theory('equality')], [c_38, c_1951])).
% 5.06/2.06  tff(c_2069, plain, (![A_196, A_197]: (k4_relat_1(k5_relat_1(k6_relat_1(A_196), k6_relat_1(A_197)))=k5_relat_1(k6_relat_1(A_197), k6_relat_1(A_196)))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_1976])).
% 5.06/2.06  tff(c_2104, plain, (![A_25, A_196]: (k5_relat_1(k6_relat_1(A_25), k6_relat_1(A_196))=k4_relat_1(k8_relat_1(A_25, k6_relat_1(A_196))) | ~v1_relat_1(k6_relat_1(A_196)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_2069])).
% 5.06/2.06  tff(c_2467, plain, (![A_208, A_209]: (k5_relat_1(k6_relat_1(A_208), k6_relat_1(A_209))=k4_relat_1(k7_relat_1(k6_relat_1(A_208), A_209)))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_231, c_2104])).
% 5.06/2.06  tff(c_2510, plain, (![A_208, A_25]: (k4_relat_1(k7_relat_1(k6_relat_1(A_208), A_25))=k8_relat_1(A_25, k6_relat_1(A_208)) | ~v1_relat_1(k6_relat_1(A_208)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_2467])).
% 5.06/2.06  tff(c_2536, plain, (![A_208, A_25]: (k4_relat_1(k7_relat_1(k6_relat_1(A_208), A_25))=k7_relat_1(k6_relat_1(A_25), A_208))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_231, c_2510])).
% 5.06/2.06  tff(c_24, plain, (![B_31, A_30]: (k7_relat_1(B_31, k3_xboole_0(k1_relat_1(B_31), A_30))=k7_relat_1(B_31, A_30) | ~v1_relat_1(B_31))), inference(cnfTransformation, [status(thm)], [f_65])).
% 5.06/2.06  tff(c_2778, plain, (![A_220, A_221]: (k4_relat_1(k7_relat_1(k6_relat_1(A_220), A_221))=k7_relat_1(k6_relat_1(A_221), A_220))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_231, c_2510])).
% 5.06/2.06  tff(c_2812, plain, (![A_220, A_30]: (k7_relat_1(k6_relat_1(k3_xboole_0(k1_relat_1(k6_relat_1(A_220)), A_30)), A_220)=k4_relat_1(k7_relat_1(k6_relat_1(A_220), A_30)) | ~v1_relat_1(k6_relat_1(A_220)))), inference(superposition, [status(thm), theory('equality')], [c_24, c_2778])).
% 5.06/2.06  tff(c_3093, plain, (![A_232, A_233]: (k7_relat_1(k6_relat_1(k3_xboole_0(A_232, A_233)), A_232)=k7_relat_1(k6_relat_1(A_233), A_232))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_2536, c_34, c_2812])).
% 5.06/2.06  tff(c_3134, plain, (![A_232, A_233]: (k3_xboole_0(A_232, k3_xboole_0(A_232, A_233))=k2_relat_1(k7_relat_1(k6_relat_1(A_233), A_232)))), inference(superposition, [status(thm), theory('equality')], [c_3093, c_308])).
% 5.06/2.06  tff(c_3210, plain, (![A_232, A_233]: (k3_xboole_0(A_232, k3_xboole_0(A_232, A_233))=k3_xboole_0(A_232, A_233))), inference(demodulation, [status(thm), theory('equality')], [c_308, c_3134])).
% 5.06/2.06  tff(c_250, plain, (![A_87, A_88]: (k8_relat_1(A_87, k6_relat_1(A_88))=k7_relat_1(k6_relat_1(A_87), A_88))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_48, c_219])).
% 5.06/2.06  tff(c_12, plain, (![A_17, B_18]: (v1_relat_1(k5_relat_1(A_17, B_18)) | ~v1_relat_1(B_18) | ~v1_relat_1(A_17))), inference(cnfTransformation, [status(thm)], [f_41])).
% 5.06/2.06  tff(c_209, plain, (![A_80, B_79]: (v1_relat_1(k8_relat_1(A_80, B_79)) | ~v1_relat_1(k6_relat_1(A_80)) | ~v1_relat_1(B_79) | ~v1_relat_1(B_79))), inference(superposition, [status(thm), theory('equality')], [c_192, c_12])).
% 5.06/2.06  tff(c_226, plain, (![A_80, B_79]: (v1_relat_1(k8_relat_1(A_80, B_79)) | ~v1_relat_1(B_79))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_209])).
% 5.06/2.06  tff(c_256, plain, (![A_87, A_88]: (v1_relat_1(k7_relat_1(k6_relat_1(A_87), A_88)) | ~v1_relat_1(k6_relat_1(A_88)))), inference(superposition, [status(thm), theory('equality')], [c_250, c_226])).
% 5.06/2.06  tff(c_262, plain, (![A_87, A_88]: (v1_relat_1(k7_relat_1(k6_relat_1(A_87), A_88)))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_256])).
% 5.06/2.06  tff(c_42, plain, (![B_43, A_42]: (r1_tarski(k5_relat_1(B_43, k6_relat_1(A_42)), B_43) | ~v1_relat_1(B_43))), inference(cnfTransformation, [status(thm)], [f_101])).
% 5.06/2.06  tff(c_206, plain, (![A_80, B_79]: (r1_tarski(k8_relat_1(A_80, B_79), B_79) | ~v1_relat_1(B_79) | ~v1_relat_1(B_79))), inference(superposition, [status(thm), theory('equality')], [c_192, c_42])).
% 5.06/2.06  tff(c_635, plain, (![A_121, B_122]: (r1_tarski(k2_relat_1(A_121), k2_relat_1(B_122)) | ~r1_tarski(A_121, B_122) | ~v1_relat_1(B_122) | ~v1_relat_1(A_121))), inference(cnfTransformation, [status(thm)], [f_82])).
% 5.06/2.06  tff(c_656, plain, (![A_121, A_40]: (r1_tarski(k2_relat_1(A_121), A_40) | ~r1_tarski(A_121, k6_relat_1(A_40)) | ~v1_relat_1(k6_relat_1(A_40)) | ~v1_relat_1(A_121))), inference(superposition, [status(thm), theory('equality')], [c_36, c_635])).
% 5.06/2.06  tff(c_709, plain, (![A_125, A_126]: (r1_tarski(k2_relat_1(A_125), A_126) | ~r1_tarski(A_125, k6_relat_1(A_126)) | ~v1_relat_1(A_125))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_656])).
% 5.06/2.06  tff(c_44, plain, (![B_45, A_44]: (k5_relat_1(B_45, k6_relat_1(A_44))=B_45 | ~r1_tarski(k2_relat_1(B_45), A_44) | ~v1_relat_1(B_45))), inference(cnfTransformation, [status(thm)], [f_107])).
% 5.06/2.06  tff(c_1588, plain, (![A_172, A_173]: (k5_relat_1(A_172, k6_relat_1(A_173))=A_172 | ~r1_tarski(A_172, k6_relat_1(A_173)) | ~v1_relat_1(A_172))), inference(resolution, [status(thm)], [c_709, c_44])).
% 5.06/2.06  tff(c_1617, plain, (![A_80, A_173]: (k5_relat_1(k8_relat_1(A_80, k6_relat_1(A_173)), k6_relat_1(A_173))=k8_relat_1(A_80, k6_relat_1(A_173)) | ~v1_relat_1(k8_relat_1(A_80, k6_relat_1(A_173))) | ~v1_relat_1(k6_relat_1(A_173)))), inference(resolution, [status(thm)], [c_206, c_1588])).
% 5.06/2.06  tff(c_4137, plain, (![A_254, A_255]: (k5_relat_1(k7_relat_1(k6_relat_1(A_254), A_255), k6_relat_1(A_255))=k7_relat_1(k6_relat_1(A_254), A_255))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_262, c_231, c_231, c_231, c_1617])).
% 5.06/2.06  tff(c_4156, plain, (![A_255, A_254]: (k8_relat_1(A_255, k7_relat_1(k6_relat_1(A_254), A_255))=k7_relat_1(k6_relat_1(A_254), A_255) | ~v1_relat_1(k7_relat_1(k6_relat_1(A_254), A_255)))), inference(superposition, [status(thm), theory('equality')], [c_4137, c_20])).
% 5.06/2.06  tff(c_4222, plain, (![A_256, A_257]: (k8_relat_1(A_256, k7_relat_1(k6_relat_1(A_257), A_256))=k7_relat_1(k6_relat_1(A_257), A_256))), inference(demodulation, [status(thm), theory('equality')], [c_262, c_4156])).
% 5.06/2.06  tff(c_22, plain, (![A_27, C_29, B_28]: (k8_relat_1(A_27, k7_relat_1(C_29, B_28))=k7_relat_1(k8_relat_1(A_27, C_29), B_28) | ~v1_relat_1(C_29))), inference(cnfTransformation, [status(thm)], [f_61])).
% 5.06/2.06  tff(c_4243, plain, (![A_256, A_257]: (k7_relat_1(k8_relat_1(A_256, k6_relat_1(A_257)), A_256)=k7_relat_1(k6_relat_1(A_257), A_256) | ~v1_relat_1(k6_relat_1(A_257)))), inference(superposition, [status(thm), theory('equality')], [c_4222, c_22])).
% 5.06/2.06  tff(c_4436, plain, (![A_262, A_263]: (k7_relat_1(k7_relat_1(k6_relat_1(A_262), A_263), A_262)=k7_relat_1(k6_relat_1(A_263), A_262))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_231, c_4243])).
% 5.06/2.06  tff(c_16, plain, (![C_22, A_20, B_21]: (k7_relat_1(k7_relat_1(C_22, A_20), B_21)=k7_relat_1(C_22, k3_xboole_0(A_20, B_21)) | ~v1_relat_1(C_22))), inference(cnfTransformation, [status(thm)], [f_49])).
% 5.06/2.06  tff(c_4460, plain, (![A_262, A_263]: (k7_relat_1(k6_relat_1(A_262), k3_xboole_0(A_263, A_262))=k7_relat_1(k6_relat_1(A_263), A_262) | ~v1_relat_1(k6_relat_1(A_262)))), inference(superposition, [status(thm), theory('equality')], [c_4436, c_16])).
% 5.06/2.06  tff(c_4716, plain, (![A_268, A_269]: (k7_relat_1(k6_relat_1(A_268), k3_xboole_0(A_269, A_268))=k7_relat_1(k6_relat_1(A_269), A_268))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_4460])).
% 5.06/2.06  tff(c_4809, plain, (![A_232, A_233]: (k7_relat_1(k6_relat_1(k3_xboole_0(A_232, A_233)), k3_xboole_0(A_232, A_233))=k7_relat_1(k6_relat_1(A_232), k3_xboole_0(A_232, A_233)))), inference(superposition, [status(thm), theory('equality')], [c_3210, c_4716])).
% 5.06/2.06  tff(c_4893, plain, (![A_232, A_233]: (k7_relat_1(k6_relat_1(A_232), A_233)=k6_relat_1(k3_xboole_0(A_232, A_233)))), inference(demodulation, [status(thm), theory('equality')], [c_307, c_134, c_4809])).
% 5.06/2.06  tff(c_144, plain, (![A_69, B_70]: (k5_relat_1(k6_relat_1(A_69), B_70)=k7_relat_1(B_70, A_69) | ~v1_relat_1(B_70))), inference(cnfTransformation, [status(thm)], [f_111])).
% 5.06/2.06  tff(c_54, plain, (k5_relat_1(k6_relat_1('#skF_2'), k6_relat_1('#skF_1'))!=k6_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_120])).
% 5.06/2.06  tff(c_160, plain, (k7_relat_1(k6_relat_1('#skF_1'), '#skF_2')!=k6_relat_1(k3_xboole_0('#skF_1', '#skF_2')) | ~v1_relat_1(k6_relat_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_144, c_54])).
% 5.06/2.06  tff(c_170, plain, (k7_relat_1(k6_relat_1('#skF_1'), '#skF_2')!=k6_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_160])).
% 5.06/2.06  tff(c_5298, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4893, c_170])).
% 5.06/2.06  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.06/2.06  
% 5.06/2.06  Inference rules
% 5.06/2.06  ----------------------
% 5.06/2.06  #Ref     : 0
% 5.06/2.06  #Sup     : 1218
% 5.06/2.06  #Fact    : 0
% 5.06/2.06  #Define  : 0
% 5.06/2.06  #Split   : 2
% 5.06/2.06  #Chain   : 0
% 5.06/2.06  #Close   : 0
% 5.06/2.06  
% 5.06/2.06  Ordering : KBO
% 5.06/2.06  
% 5.06/2.06  Simplification rules
% 5.06/2.06  ----------------------
% 5.06/2.06  #Subsume      : 147
% 5.06/2.06  #Demod        : 1261
% 5.06/2.06  #Tautology    : 581
% 5.06/2.06  #SimpNegUnit  : 0
% 5.06/2.06  #BackRed      : 40
% 5.06/2.06  
% 5.06/2.06  #Partial instantiations: 0
% 5.06/2.06  #Strategies tried      : 1
% 5.06/2.06  
% 5.06/2.06  Timing (in seconds)
% 5.06/2.06  ----------------------
% 5.06/2.07  Preprocessing        : 0.35
% 5.06/2.07  Parsing              : 0.19
% 5.06/2.07  CNF conversion       : 0.02
% 5.06/2.07  Main loop            : 0.89
% 5.06/2.07  Inferencing          : 0.31
% 5.06/2.07  Reduction            : 0.32
% 5.06/2.07  Demodulation         : 0.24
% 5.06/2.07  BG Simplification    : 0.04
% 5.06/2.07  Subsumption          : 0.14
% 5.06/2.07  Abstraction          : 0.06
% 5.06/2.07  MUC search           : 0.00
% 5.06/2.07  Cooper               : 0.00
% 5.06/2.07  Total                : 1.29
% 5.06/2.07  Index Insertion      : 0.00
% 5.06/2.07  Index Deletion       : 0.00
% 5.06/2.07  Index Matching       : 0.00
% 5.06/2.07  BG Taut test         : 0.00
%------------------------------------------------------------------------------

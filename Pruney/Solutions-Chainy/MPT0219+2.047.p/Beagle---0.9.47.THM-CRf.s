%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:47:56 EST 2020

% Result     : Theorem 7.34s
% Output     : CNFRefutation 7.34s
% Verified   : 
% Statistics : Number of formulae       :   98 (1220 expanded)
%              Number of leaves         :   32 ( 436 expanded)
%              Depth                    :   23
%              Number of atoms          :  106 (1814 expanded)
%              Number of equality atoms :   63 ( 942 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_82,negated_conjecture,(
    ~ ! [A,B] :
        ( k2_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
       => A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_zfmisc_1)).

tff(f_59,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_49,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_55,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_51,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_36,axiom,(
    ! [A,B] : k2_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

tff(f_65,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_63,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_34,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k5_xboole_0(B,C))
    <=> ~ ( r2_hidden(A,B)
        <=> r2_hidden(A,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_0)).

tff(f_57,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_61,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_77,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),k1_tarski(B))
     => A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_zfmisc_1)).

tff(c_54,plain,(
    '#skF_2' != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_36,plain,(
    ! [A_20] : k5_xboole_0(A_20,k1_xboole_0) = A_20 ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_28,plain,(
    ! [B_14] : r1_tarski(B_14,B_14) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_149,plain,(
    ! [A_53,B_54] :
      ( k3_xboole_0(A_53,B_54) = A_53
      | ~ r1_tarski(A_53,B_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_160,plain,(
    ! [B_14] : k3_xboole_0(B_14,B_14) = B_14 ),
    inference(resolution,[status(thm)],[c_28,c_149])).

tff(c_245,plain,(
    ! [A_58,B_59] : k5_xboole_0(A_58,k3_xboole_0(A_58,B_59)) = k4_xboole_0(A_58,B_59) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_260,plain,(
    ! [B_14] : k5_xboole_0(B_14,B_14) = k4_xboole_0(B_14,B_14) ),
    inference(superposition,[status(thm),theory(equality)],[c_160,c_245])).

tff(c_10,plain,(
    ! [A_8] : k2_xboole_0(A_8,A_8) = A_8 ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_42,plain,(
    ! [A_26,B_27] : k5_xboole_0(A_26,k4_xboole_0(B_27,A_26)) = k2_xboole_0(A_26,B_27) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_576,plain,(
    ! [A_86,B_87,C_88] : k5_xboole_0(k5_xboole_0(A_86,B_87),C_88) = k5_xboole_0(A_86,k5_xboole_0(B_87,C_88)) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_855,plain,(
    ! [B_101,C_102] : k5_xboole_0(k4_xboole_0(B_101,B_101),C_102) = k5_xboole_0(B_101,k5_xboole_0(B_101,C_102)) ),
    inference(superposition,[status(thm),theory(equality)],[c_260,c_576])).

tff(c_880,plain,(
    ! [B_101] : k5_xboole_0(B_101,k5_xboole_0(B_101,k4_xboole_0(B_101,B_101))) = k4_xboole_0(k4_xboole_0(B_101,B_101),k4_xboole_0(B_101,B_101)) ),
    inference(superposition,[status(thm),theory(equality)],[c_855,c_260])).

tff(c_927,plain,(
    ! [B_101] : k4_xboole_0(k4_xboole_0(B_101,B_101),k4_xboole_0(B_101,B_101)) = k4_xboole_0(B_101,B_101) ),
    inference(demodulation,[status(thm),theory(equality)],[c_260,c_10,c_42,c_880])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r2_hidden('#skF_1'(A_3,B_4),A_3)
      | r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_563,plain,(
    ! [C_80,B_81,A_82] :
      ( r2_hidden(C_80,B_81)
      | ~ r2_hidden(C_80,A_82)
      | ~ r1_tarski(A_82,B_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_566,plain,(
    ! [A_3,B_4,B_81] :
      ( r2_hidden('#skF_1'(A_3,B_4),B_81)
      | ~ r1_tarski(A_3,B_81)
      | r1_tarski(A_3,B_4) ) ),
    inference(resolution,[status(thm)],[c_8,c_563])).

tff(c_750,plain,(
    ! [A_92,C_93,B_94] :
      ( ~ r2_hidden(A_92,C_93)
      | ~ r2_hidden(A_92,B_94)
      | ~ r2_hidden(A_92,k5_xboole_0(B_94,C_93)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_1762,plain,(
    ! [A_137,B_138] :
      ( ~ r2_hidden(A_137,B_138)
      | ~ r2_hidden(A_137,B_138)
      | ~ r2_hidden(A_137,k4_xboole_0(B_138,B_138)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_260,c_750])).

tff(c_2391,plain,(
    ! [B_159,B_160] :
      ( ~ r2_hidden('#skF_1'(k4_xboole_0(B_159,B_159),B_160),B_159)
      | r1_tarski(k4_xboole_0(B_159,B_159),B_160) ) ),
    inference(resolution,[status(thm)],[c_8,c_1762])).

tff(c_2471,plain,(
    ! [B_164,B_165] :
      ( ~ r1_tarski(k4_xboole_0(B_164,B_164),B_164)
      | r1_tarski(k4_xboole_0(B_164,B_164),B_165) ) ),
    inference(resolution,[status(thm)],[c_566,c_2391])).

tff(c_2473,plain,(
    ! [B_101,B_165] :
      ( ~ r1_tarski(k4_xboole_0(B_101,B_101),k4_xboole_0(B_101,B_101))
      | r1_tarski(k4_xboole_0(k4_xboole_0(B_101,B_101),k4_xboole_0(B_101,B_101)),B_165) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_927,c_2471])).

tff(c_2489,plain,(
    ! [B_166,B_167] : r1_tarski(k4_xboole_0(B_166,B_166),B_167) ),
    inference(demodulation,[status(thm),theory(equality)],[c_927,c_28,c_2473])).

tff(c_34,plain,(
    ! [A_19] : r1_tarski(k1_xboole_0,A_19) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_350,plain,(
    ! [B_67,A_68] :
      ( B_67 = A_68
      | ~ r1_tarski(B_67,A_68)
      | ~ r1_tarski(A_68,B_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_362,plain,(
    ! [A_19] :
      ( k1_xboole_0 = A_19
      | ~ r1_tarski(A_19,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_34,c_350])).

tff(c_2513,plain,(
    ! [B_166] : k4_xboole_0(B_166,B_166) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2489,c_362])).

tff(c_2574,plain,(
    ! [B_169] : k5_xboole_0(B_169,B_169) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2513,c_260])).

tff(c_621,plain,(
    ! [A_26,B_27,C_88] : k5_xboole_0(A_26,k5_xboole_0(k4_xboole_0(B_27,A_26),C_88)) = k5_xboole_0(k2_xboole_0(A_26,B_27),C_88) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_576])).

tff(c_2591,plain,(
    ! [A_26,B_27] : k5_xboole_0(k2_xboole_0(A_26,B_27),k4_xboole_0(B_27,A_26)) = k5_xboole_0(A_26,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_2574,c_621])).

tff(c_4499,plain,(
    ! [A_209,B_210] : k5_xboole_0(k2_xboole_0(A_209,B_210),k4_xboole_0(B_210,A_209)) = A_209 ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_2591])).

tff(c_40,plain,(
    ! [A_23,B_24,C_25] : k5_xboole_0(k5_xboole_0(A_23,B_24),C_25) = k5_xboole_0(A_23,k5_xboole_0(B_24,C_25)) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_2640,plain,(
    ! [A_23,B_24] : k5_xboole_0(A_23,k5_xboole_0(B_24,k5_xboole_0(A_23,B_24))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_2574])).

tff(c_2527,plain,(
    ! [B_14] : k5_xboole_0(B_14,B_14) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2513,c_260])).

tff(c_171,plain,(
    ! [A_56] : k3_xboole_0(k1_xboole_0,A_56) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_34,c_149])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_180,plain,(
    ! [A_56] : k3_xboole_0(A_56,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_171,c_2])).

tff(c_254,plain,(
    ! [A_56] : k5_xboole_0(A_56,k1_xboole_0) = k4_xboole_0(A_56,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_180,c_245])).

tff(c_269,plain,(
    ! [A_56] : k4_xboole_0(A_56,k1_xboole_0) = A_56 ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_254])).

tff(c_363,plain,(
    ! [A_69,B_70] : k5_xboole_0(A_69,k4_xboole_0(B_70,A_69)) = k2_xboole_0(A_69,B_70) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_372,plain,(
    ! [A_56] : k5_xboole_0(k1_xboole_0,A_56) = k2_xboole_0(k1_xboole_0,A_56) ),
    inference(superposition,[status(thm),theory(equality)],[c_269,c_363])).

tff(c_628,plain,(
    ! [B_14,C_88] : k5_xboole_0(k4_xboole_0(B_14,B_14),C_88) = k5_xboole_0(B_14,k5_xboole_0(B_14,C_88)) ),
    inference(superposition,[status(thm),theory(equality)],[c_260,c_576])).

tff(c_2525,plain,(
    ! [B_14,C_88] : k5_xboole_0(B_14,k5_xboole_0(B_14,C_88)) = k5_xboole_0(k1_xboole_0,C_88) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2513,c_628])).

tff(c_2889,plain,(
    ! [B_178,C_179] : k5_xboole_0(B_178,k5_xboole_0(B_178,C_179)) = k2_xboole_0(k1_xboole_0,C_179) ),
    inference(demodulation,[status(thm),theory(equality)],[c_372,c_2525])).

tff(c_2954,plain,(
    ! [B_14] : k5_xboole_0(B_14,k1_xboole_0) = k2_xboole_0(k1_xboole_0,B_14) ),
    inference(superposition,[status(thm),theory(equality)],[c_2527,c_2889])).

tff(c_3027,plain,(
    ! [B_14] : k2_xboole_0(k1_xboole_0,B_14) = B_14 ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_2954])).

tff(c_2531,plain,(
    ! [B_14,C_88] : k5_xboole_0(B_14,k5_xboole_0(B_14,C_88)) = k2_xboole_0(k1_xboole_0,C_88) ),
    inference(demodulation,[status(thm),theory(equality)],[c_372,c_2525])).

tff(c_3403,plain,(
    ! [B_184,C_185] : k5_xboole_0(B_184,k5_xboole_0(B_184,C_185)) = C_185 ),
    inference(demodulation,[status(thm),theory(equality)],[c_3027,c_2531])).

tff(c_3471,plain,(
    ! [B_24,A_23] : k5_xboole_0(B_24,k5_xboole_0(A_23,B_24)) = k5_xboole_0(A_23,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_2640,c_3403])).

tff(c_3522,plain,(
    ! [B_24,A_23] : k5_xboole_0(B_24,k5_xboole_0(A_23,B_24)) = A_23 ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_3471])).

tff(c_4511,plain,(
    ! [B_210,A_209] : k5_xboole_0(k4_xboole_0(B_210,A_209),A_209) = k2_xboole_0(A_209,B_210) ),
    inference(superposition,[status(thm),theory(equality)],[c_4499,c_3522])).

tff(c_30,plain,(
    ! [A_15,B_16] : k5_xboole_0(A_15,k3_xboole_0(A_15,B_16)) = k4_xboole_0(A_15,B_16) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_635,plain,(
    ! [A_15,B_16,C_88] : k5_xboole_0(A_15,k5_xboole_0(k3_xboole_0(A_15,B_16),C_88)) = k5_xboole_0(k4_xboole_0(A_15,B_16),C_88) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_576])).

tff(c_2584,plain,(
    ! [A_15,B_16] : k5_xboole_0(k4_xboole_0(A_15,B_16),k3_xboole_0(A_15,B_16)) = k5_xboole_0(A_15,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_2574,c_635])).

tff(c_4264,plain,(
    ! [A_202,B_203] : k5_xboole_0(k4_xboole_0(A_202,B_203),k3_xboole_0(A_202,B_203)) = A_202 ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_2584])).

tff(c_6566,plain,(
    ! [A_251,B_252] : k5_xboole_0(k3_xboole_0(A_251,B_252),A_251) = k4_xboole_0(A_251,B_252) ),
    inference(superposition,[status(thm),theory(equality)],[c_4264,c_3522])).

tff(c_1922,plain,(
    ! [A_143,B_144,C_145] : k5_xboole_0(A_143,k5_xboole_0(k3_xboole_0(A_143,B_144),C_145)) = k5_xboole_0(k4_xboole_0(A_143,B_144),C_145) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_576])).

tff(c_2044,plain,(
    ! [B_2,A_1,C_145] : k5_xboole_0(B_2,k5_xboole_0(k3_xboole_0(A_1,B_2),C_145)) = k5_xboole_0(k4_xboole_0(B_2,A_1),C_145) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_1922])).

tff(c_6597,plain,(
    ! [B_252,A_251] : k5_xboole_0(k4_xboole_0(B_252,A_251),A_251) = k5_xboole_0(B_252,k4_xboole_0(A_251,B_252)) ),
    inference(superposition,[status(thm),theory(equality)],[c_6566,c_2044])).

tff(c_6691,plain,(
    ! [B_253,A_254] : k2_xboole_0(B_253,A_254) = k2_xboole_0(A_254,B_253) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4511,c_42,c_6597])).

tff(c_56,plain,(
    k2_xboole_0(k1_tarski('#skF_2'),k1_tarski('#skF_3')) = k1_tarski('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_6802,plain,(
    k2_xboole_0(k1_tarski('#skF_3'),k1_tarski('#skF_2')) = k1_tarski('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_6691,c_56])).

tff(c_38,plain,(
    ! [A_21,B_22] : r1_tarski(A_21,k2_xboole_0(A_21,B_22)) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_6911,plain,(
    r1_tarski(k1_tarski('#skF_3'),k1_tarski('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_6802,c_38])).

tff(c_52,plain,(
    ! [B_39,A_38] :
      ( B_39 = A_38
      | ~ r1_tarski(k1_tarski(A_38),k1_tarski(B_39)) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_6975,plain,(
    '#skF_2' = '#skF_3' ),
    inference(resolution,[status(thm)],[c_6911,c_52])).

tff(c_6982,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_6975])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n012.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 11:55:07 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.34/3.05  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.34/3.07  
% 7.34/3.07  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.34/3.07  %$ r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 7.34/3.07  
% 7.34/3.07  %Foreground sorts:
% 7.34/3.07  
% 7.34/3.07  
% 7.34/3.07  %Background operators:
% 7.34/3.07  
% 7.34/3.07  
% 7.34/3.07  %Foreground operators:
% 7.34/3.07  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.34/3.07  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.34/3.07  tff(k1_tarski, type, k1_tarski: $i > $i).
% 7.34/3.07  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 7.34/3.07  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.34/3.07  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 7.34/3.07  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 7.34/3.07  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.34/3.07  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 7.34/3.07  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 7.34/3.07  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 7.34/3.07  tff('#skF_2', type, '#skF_2': $i).
% 7.34/3.07  tff('#skF_3', type, '#skF_3': $i).
% 7.34/3.07  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.34/3.07  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.34/3.07  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 7.34/3.07  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 7.34/3.07  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 7.34/3.07  
% 7.34/3.10  tff(f_82, negated_conjecture, ~(![A, B]: ((k2_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) => (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t13_zfmisc_1)).
% 7.34/3.10  tff(f_59, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 7.34/3.10  tff(f_49, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 7.34/3.10  tff(f_55, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 7.34/3.10  tff(f_51, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 7.34/3.10  tff(f_36, axiom, (![A, B]: (k2_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 7.34/3.10  tff(f_65, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 7.34/3.10  tff(f_63, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_xboole_1)).
% 7.34/3.10  tff(f_34, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 7.34/3.10  tff(f_43, axiom, (![A, B, C]: (r2_hidden(A, k5_xboole_0(B, C)) <=> ~(r2_hidden(A, B) <=> r2_hidden(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_0)).
% 7.34/3.10  tff(f_57, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 7.34/3.10  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 7.34/3.10  tff(f_61, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 7.34/3.10  tff(f_77, axiom, (![A, B]: (r1_tarski(k1_tarski(A), k1_tarski(B)) => (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_zfmisc_1)).
% 7.34/3.10  tff(c_54, plain, ('#skF_2'!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_82])).
% 7.34/3.10  tff(c_36, plain, (![A_20]: (k5_xboole_0(A_20, k1_xboole_0)=A_20)), inference(cnfTransformation, [status(thm)], [f_59])).
% 7.34/3.10  tff(c_28, plain, (![B_14]: (r1_tarski(B_14, B_14))), inference(cnfTransformation, [status(thm)], [f_49])).
% 7.34/3.10  tff(c_149, plain, (![A_53, B_54]: (k3_xboole_0(A_53, B_54)=A_53 | ~r1_tarski(A_53, B_54))), inference(cnfTransformation, [status(thm)], [f_55])).
% 7.34/3.10  tff(c_160, plain, (![B_14]: (k3_xboole_0(B_14, B_14)=B_14)), inference(resolution, [status(thm)], [c_28, c_149])).
% 7.34/3.10  tff(c_245, plain, (![A_58, B_59]: (k5_xboole_0(A_58, k3_xboole_0(A_58, B_59))=k4_xboole_0(A_58, B_59))), inference(cnfTransformation, [status(thm)], [f_51])).
% 7.34/3.10  tff(c_260, plain, (![B_14]: (k5_xboole_0(B_14, B_14)=k4_xboole_0(B_14, B_14))), inference(superposition, [status(thm), theory('equality')], [c_160, c_245])).
% 7.34/3.10  tff(c_10, plain, (![A_8]: (k2_xboole_0(A_8, A_8)=A_8)), inference(cnfTransformation, [status(thm)], [f_36])).
% 7.34/3.10  tff(c_42, plain, (![A_26, B_27]: (k5_xboole_0(A_26, k4_xboole_0(B_27, A_26))=k2_xboole_0(A_26, B_27))), inference(cnfTransformation, [status(thm)], [f_65])).
% 7.34/3.10  tff(c_576, plain, (![A_86, B_87, C_88]: (k5_xboole_0(k5_xboole_0(A_86, B_87), C_88)=k5_xboole_0(A_86, k5_xboole_0(B_87, C_88)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 7.34/3.10  tff(c_855, plain, (![B_101, C_102]: (k5_xboole_0(k4_xboole_0(B_101, B_101), C_102)=k5_xboole_0(B_101, k5_xboole_0(B_101, C_102)))), inference(superposition, [status(thm), theory('equality')], [c_260, c_576])).
% 7.34/3.10  tff(c_880, plain, (![B_101]: (k5_xboole_0(B_101, k5_xboole_0(B_101, k4_xboole_0(B_101, B_101)))=k4_xboole_0(k4_xboole_0(B_101, B_101), k4_xboole_0(B_101, B_101)))), inference(superposition, [status(thm), theory('equality')], [c_855, c_260])).
% 7.34/3.10  tff(c_927, plain, (![B_101]: (k4_xboole_0(k4_xboole_0(B_101, B_101), k4_xboole_0(B_101, B_101))=k4_xboole_0(B_101, B_101))), inference(demodulation, [status(thm), theory('equality')], [c_260, c_10, c_42, c_880])).
% 7.34/3.10  tff(c_8, plain, (![A_3, B_4]: (r2_hidden('#skF_1'(A_3, B_4), A_3) | r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_34])).
% 7.34/3.10  tff(c_563, plain, (![C_80, B_81, A_82]: (r2_hidden(C_80, B_81) | ~r2_hidden(C_80, A_82) | ~r1_tarski(A_82, B_81))), inference(cnfTransformation, [status(thm)], [f_34])).
% 7.34/3.10  tff(c_566, plain, (![A_3, B_4, B_81]: (r2_hidden('#skF_1'(A_3, B_4), B_81) | ~r1_tarski(A_3, B_81) | r1_tarski(A_3, B_4))), inference(resolution, [status(thm)], [c_8, c_563])).
% 7.34/3.10  tff(c_750, plain, (![A_92, C_93, B_94]: (~r2_hidden(A_92, C_93) | ~r2_hidden(A_92, B_94) | ~r2_hidden(A_92, k5_xboole_0(B_94, C_93)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 7.34/3.10  tff(c_1762, plain, (![A_137, B_138]: (~r2_hidden(A_137, B_138) | ~r2_hidden(A_137, B_138) | ~r2_hidden(A_137, k4_xboole_0(B_138, B_138)))), inference(superposition, [status(thm), theory('equality')], [c_260, c_750])).
% 7.34/3.10  tff(c_2391, plain, (![B_159, B_160]: (~r2_hidden('#skF_1'(k4_xboole_0(B_159, B_159), B_160), B_159) | r1_tarski(k4_xboole_0(B_159, B_159), B_160))), inference(resolution, [status(thm)], [c_8, c_1762])).
% 7.34/3.10  tff(c_2471, plain, (![B_164, B_165]: (~r1_tarski(k4_xboole_0(B_164, B_164), B_164) | r1_tarski(k4_xboole_0(B_164, B_164), B_165))), inference(resolution, [status(thm)], [c_566, c_2391])).
% 7.34/3.10  tff(c_2473, plain, (![B_101, B_165]: (~r1_tarski(k4_xboole_0(B_101, B_101), k4_xboole_0(B_101, B_101)) | r1_tarski(k4_xboole_0(k4_xboole_0(B_101, B_101), k4_xboole_0(B_101, B_101)), B_165))), inference(superposition, [status(thm), theory('equality')], [c_927, c_2471])).
% 7.34/3.10  tff(c_2489, plain, (![B_166, B_167]: (r1_tarski(k4_xboole_0(B_166, B_166), B_167))), inference(demodulation, [status(thm), theory('equality')], [c_927, c_28, c_2473])).
% 7.34/3.10  tff(c_34, plain, (![A_19]: (r1_tarski(k1_xboole_0, A_19))), inference(cnfTransformation, [status(thm)], [f_57])).
% 7.34/3.10  tff(c_350, plain, (![B_67, A_68]: (B_67=A_68 | ~r1_tarski(B_67, A_68) | ~r1_tarski(A_68, B_67))), inference(cnfTransformation, [status(thm)], [f_49])).
% 7.34/3.10  tff(c_362, plain, (![A_19]: (k1_xboole_0=A_19 | ~r1_tarski(A_19, k1_xboole_0))), inference(resolution, [status(thm)], [c_34, c_350])).
% 7.34/3.10  tff(c_2513, plain, (![B_166]: (k4_xboole_0(B_166, B_166)=k1_xboole_0)), inference(resolution, [status(thm)], [c_2489, c_362])).
% 7.34/3.10  tff(c_2574, plain, (![B_169]: (k5_xboole_0(B_169, B_169)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_2513, c_260])).
% 7.34/3.10  tff(c_621, plain, (![A_26, B_27, C_88]: (k5_xboole_0(A_26, k5_xboole_0(k4_xboole_0(B_27, A_26), C_88))=k5_xboole_0(k2_xboole_0(A_26, B_27), C_88))), inference(superposition, [status(thm), theory('equality')], [c_42, c_576])).
% 7.34/3.10  tff(c_2591, plain, (![A_26, B_27]: (k5_xboole_0(k2_xboole_0(A_26, B_27), k4_xboole_0(B_27, A_26))=k5_xboole_0(A_26, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_2574, c_621])).
% 7.34/3.10  tff(c_4499, plain, (![A_209, B_210]: (k5_xboole_0(k2_xboole_0(A_209, B_210), k4_xboole_0(B_210, A_209))=A_209)), inference(demodulation, [status(thm), theory('equality')], [c_36, c_2591])).
% 7.34/3.10  tff(c_40, plain, (![A_23, B_24, C_25]: (k5_xboole_0(k5_xboole_0(A_23, B_24), C_25)=k5_xboole_0(A_23, k5_xboole_0(B_24, C_25)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 7.34/3.10  tff(c_2640, plain, (![A_23, B_24]: (k5_xboole_0(A_23, k5_xboole_0(B_24, k5_xboole_0(A_23, B_24)))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_40, c_2574])).
% 7.34/3.10  tff(c_2527, plain, (![B_14]: (k5_xboole_0(B_14, B_14)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_2513, c_260])).
% 7.34/3.10  tff(c_171, plain, (![A_56]: (k3_xboole_0(k1_xboole_0, A_56)=k1_xboole_0)), inference(resolution, [status(thm)], [c_34, c_149])).
% 7.34/3.10  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 7.34/3.10  tff(c_180, plain, (![A_56]: (k3_xboole_0(A_56, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_171, c_2])).
% 7.34/3.10  tff(c_254, plain, (![A_56]: (k5_xboole_0(A_56, k1_xboole_0)=k4_xboole_0(A_56, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_180, c_245])).
% 7.34/3.10  tff(c_269, plain, (![A_56]: (k4_xboole_0(A_56, k1_xboole_0)=A_56)), inference(demodulation, [status(thm), theory('equality')], [c_36, c_254])).
% 7.34/3.10  tff(c_363, plain, (![A_69, B_70]: (k5_xboole_0(A_69, k4_xboole_0(B_70, A_69))=k2_xboole_0(A_69, B_70))), inference(cnfTransformation, [status(thm)], [f_65])).
% 7.34/3.10  tff(c_372, plain, (![A_56]: (k5_xboole_0(k1_xboole_0, A_56)=k2_xboole_0(k1_xboole_0, A_56))), inference(superposition, [status(thm), theory('equality')], [c_269, c_363])).
% 7.34/3.10  tff(c_628, plain, (![B_14, C_88]: (k5_xboole_0(k4_xboole_0(B_14, B_14), C_88)=k5_xboole_0(B_14, k5_xboole_0(B_14, C_88)))), inference(superposition, [status(thm), theory('equality')], [c_260, c_576])).
% 7.34/3.10  tff(c_2525, plain, (![B_14, C_88]: (k5_xboole_0(B_14, k5_xboole_0(B_14, C_88))=k5_xboole_0(k1_xboole_0, C_88))), inference(demodulation, [status(thm), theory('equality')], [c_2513, c_628])).
% 7.34/3.10  tff(c_2889, plain, (![B_178, C_179]: (k5_xboole_0(B_178, k5_xboole_0(B_178, C_179))=k2_xboole_0(k1_xboole_0, C_179))), inference(demodulation, [status(thm), theory('equality')], [c_372, c_2525])).
% 7.34/3.10  tff(c_2954, plain, (![B_14]: (k5_xboole_0(B_14, k1_xboole_0)=k2_xboole_0(k1_xboole_0, B_14))), inference(superposition, [status(thm), theory('equality')], [c_2527, c_2889])).
% 7.34/3.10  tff(c_3027, plain, (![B_14]: (k2_xboole_0(k1_xboole_0, B_14)=B_14)), inference(demodulation, [status(thm), theory('equality')], [c_36, c_2954])).
% 7.34/3.10  tff(c_2531, plain, (![B_14, C_88]: (k5_xboole_0(B_14, k5_xboole_0(B_14, C_88))=k2_xboole_0(k1_xboole_0, C_88))), inference(demodulation, [status(thm), theory('equality')], [c_372, c_2525])).
% 7.34/3.10  tff(c_3403, plain, (![B_184, C_185]: (k5_xboole_0(B_184, k5_xboole_0(B_184, C_185))=C_185)), inference(demodulation, [status(thm), theory('equality')], [c_3027, c_2531])).
% 7.34/3.10  tff(c_3471, plain, (![B_24, A_23]: (k5_xboole_0(B_24, k5_xboole_0(A_23, B_24))=k5_xboole_0(A_23, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_2640, c_3403])).
% 7.34/3.10  tff(c_3522, plain, (![B_24, A_23]: (k5_xboole_0(B_24, k5_xboole_0(A_23, B_24))=A_23)), inference(demodulation, [status(thm), theory('equality')], [c_36, c_3471])).
% 7.34/3.10  tff(c_4511, plain, (![B_210, A_209]: (k5_xboole_0(k4_xboole_0(B_210, A_209), A_209)=k2_xboole_0(A_209, B_210))), inference(superposition, [status(thm), theory('equality')], [c_4499, c_3522])).
% 7.34/3.10  tff(c_30, plain, (![A_15, B_16]: (k5_xboole_0(A_15, k3_xboole_0(A_15, B_16))=k4_xboole_0(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_51])).
% 7.34/3.10  tff(c_635, plain, (![A_15, B_16, C_88]: (k5_xboole_0(A_15, k5_xboole_0(k3_xboole_0(A_15, B_16), C_88))=k5_xboole_0(k4_xboole_0(A_15, B_16), C_88))), inference(superposition, [status(thm), theory('equality')], [c_30, c_576])).
% 7.34/3.10  tff(c_2584, plain, (![A_15, B_16]: (k5_xboole_0(k4_xboole_0(A_15, B_16), k3_xboole_0(A_15, B_16))=k5_xboole_0(A_15, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_2574, c_635])).
% 7.34/3.10  tff(c_4264, plain, (![A_202, B_203]: (k5_xboole_0(k4_xboole_0(A_202, B_203), k3_xboole_0(A_202, B_203))=A_202)), inference(demodulation, [status(thm), theory('equality')], [c_36, c_2584])).
% 7.34/3.10  tff(c_6566, plain, (![A_251, B_252]: (k5_xboole_0(k3_xboole_0(A_251, B_252), A_251)=k4_xboole_0(A_251, B_252))), inference(superposition, [status(thm), theory('equality')], [c_4264, c_3522])).
% 7.34/3.10  tff(c_1922, plain, (![A_143, B_144, C_145]: (k5_xboole_0(A_143, k5_xboole_0(k3_xboole_0(A_143, B_144), C_145))=k5_xboole_0(k4_xboole_0(A_143, B_144), C_145))), inference(superposition, [status(thm), theory('equality')], [c_30, c_576])).
% 7.34/3.10  tff(c_2044, plain, (![B_2, A_1, C_145]: (k5_xboole_0(B_2, k5_xboole_0(k3_xboole_0(A_1, B_2), C_145))=k5_xboole_0(k4_xboole_0(B_2, A_1), C_145))), inference(superposition, [status(thm), theory('equality')], [c_2, c_1922])).
% 7.34/3.10  tff(c_6597, plain, (![B_252, A_251]: (k5_xboole_0(k4_xboole_0(B_252, A_251), A_251)=k5_xboole_0(B_252, k4_xboole_0(A_251, B_252)))), inference(superposition, [status(thm), theory('equality')], [c_6566, c_2044])).
% 7.34/3.10  tff(c_6691, plain, (![B_253, A_254]: (k2_xboole_0(B_253, A_254)=k2_xboole_0(A_254, B_253))), inference(demodulation, [status(thm), theory('equality')], [c_4511, c_42, c_6597])).
% 7.34/3.10  tff(c_56, plain, (k2_xboole_0(k1_tarski('#skF_2'), k1_tarski('#skF_3'))=k1_tarski('#skF_2')), inference(cnfTransformation, [status(thm)], [f_82])).
% 7.34/3.10  tff(c_6802, plain, (k2_xboole_0(k1_tarski('#skF_3'), k1_tarski('#skF_2'))=k1_tarski('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_6691, c_56])).
% 7.34/3.10  tff(c_38, plain, (![A_21, B_22]: (r1_tarski(A_21, k2_xboole_0(A_21, B_22)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 7.34/3.10  tff(c_6911, plain, (r1_tarski(k1_tarski('#skF_3'), k1_tarski('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_6802, c_38])).
% 7.34/3.10  tff(c_52, plain, (![B_39, A_38]: (B_39=A_38 | ~r1_tarski(k1_tarski(A_38), k1_tarski(B_39)))), inference(cnfTransformation, [status(thm)], [f_77])).
% 7.34/3.10  tff(c_6975, plain, ('#skF_2'='#skF_3'), inference(resolution, [status(thm)], [c_6911, c_52])).
% 7.34/3.10  tff(c_6982, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54, c_6975])).
% 7.34/3.10  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.34/3.10  
% 7.34/3.10  Inference rules
% 7.34/3.10  ----------------------
% 7.34/3.10  #Ref     : 0
% 7.34/3.10  #Sup     : 1717
% 7.34/3.10  #Fact    : 0
% 7.34/3.10  #Define  : 0
% 7.34/3.10  #Split   : 0
% 7.34/3.10  #Chain   : 0
% 7.34/3.10  #Close   : 0
% 7.34/3.10  
% 7.34/3.10  Ordering : KBO
% 7.34/3.10  
% 7.34/3.10  Simplification rules
% 7.34/3.10  ----------------------
% 7.34/3.10  #Subsume      : 103
% 7.34/3.10  #Demod        : 1561
% 7.34/3.10  #Tautology    : 983
% 7.34/3.10  #SimpNegUnit  : 1
% 7.34/3.10  #BackRed      : 17
% 7.34/3.10  
% 7.34/3.10  #Partial instantiations: 0
% 7.34/3.10  #Strategies tried      : 1
% 7.34/3.10  
% 7.34/3.10  Timing (in seconds)
% 7.34/3.10  ----------------------
% 7.34/3.10  Preprocessing        : 0.47
% 7.34/3.10  Parsing              : 0.24
% 7.34/3.10  CNF conversion       : 0.03
% 7.34/3.10  Main loop            : 1.73
% 7.34/3.10  Inferencing          : 0.58
% 7.34/3.10  Reduction            : 0.72
% 7.34/3.10  Demodulation         : 0.60
% 7.34/3.10  BG Simplification    : 0.07
% 7.34/3.10  Subsumption          : 0.27
% 7.34/3.10  Abstraction          : 0.09
% 7.34/3.10  MUC search           : 0.00
% 7.34/3.10  Cooper               : 0.00
% 7.34/3.10  Total                : 2.26
% 7.34/3.10  Index Insertion      : 0.00
% 7.34/3.10  Index Deletion       : 0.00
% 7.34/3.10  Index Matching       : 0.00
% 7.34/3.10  BG Taut test         : 0.00
%------------------------------------------------------------------------------

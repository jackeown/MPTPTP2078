%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:49:46 EST 2020

% Result     : Theorem 38.17s
% Output     : CNFRefutation 38.42s
% Verified   : 
% Statistics : Number of formulae       :  107 (7509 expanded)
%              Number of leaves         :   39 (2521 expanded)
%              Depth                    :   23
%              Number of atoms          :  101 (8299 expanded)
%              Number of equality atoms :   90 (6844 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i ) > $i )).

tff(f_66,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_41,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_37,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_31,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_47,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_49,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_xboole_1)).

tff(f_94,axiom,(
    ! [A,B] :
      ( A != B
     => k5_xboole_0(k1_tarski(A),k1_tarski(B)) = k2_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_zfmisc_1)).

tff(f_29,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_89,axiom,(
    ! [A,B] :
      ( A != B
     => r1_xboole_0(k1_tarski(A),k1_tarski(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_zfmisc_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_84,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_97,negated_conjecture,(
    ~ ! [A,B] : k3_tarski(k2_tarski(k1_tarski(A),k1_tarski(B))) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_zfmisc_1)).

tff(c_48,plain,(
    ! [A_27] : k2_tarski(A_27,A_27) = k1_tarski(A_27) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_14,plain,(
    ! [A_12] : k5_xboole_0(A_12,k1_xboole_0) = A_12 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_10,plain,(
    ! [A_9] : r1_tarski(k1_xboole_0,A_9) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_176,plain,(
    ! [A_87,B_88] :
      ( k3_xboole_0(A_87,B_88) = A_87
      | ~ r1_tarski(A_87,B_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_199,plain,(
    ! [A_91] : k3_xboole_0(k1_xboole_0,A_91) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_10,c_176])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_204,plain,(
    ! [A_91] : k3_xboole_0(A_91,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_199,c_2])).

tff(c_301,plain,(
    ! [A_100,B_101] : k5_xboole_0(A_100,k3_xboole_0(A_100,B_101)) = k4_xboole_0(A_100,B_101) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_310,plain,(
    ! [A_91] : k5_xboole_0(A_91,k1_xboole_0) = k4_xboole_0(A_91,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_204,c_301])).

tff(c_348,plain,(
    ! [A_103] : k4_xboole_0(A_103,k1_xboole_0) = A_103 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_310])).

tff(c_12,plain,(
    ! [A_10,B_11] : k4_xboole_0(A_10,k4_xboole_0(A_10,B_11)) = k3_xboole_0(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_358,plain,(
    ! [A_103] : k4_xboole_0(A_103,A_103) = k3_xboole_0(A_103,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_348,c_12])).

tff(c_368,plain,(
    ! [A_103] : k4_xboole_0(A_103,A_103) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_204,c_358])).

tff(c_319,plain,(
    ! [B_2,A_1] : k5_xboole_0(B_2,k3_xboole_0(A_1,B_2)) = k4_xboole_0(B_2,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_301])).

tff(c_20,plain,(
    ! [A_15,B_16,C_17] : k5_xboole_0(k5_xboole_0(A_15,B_16),C_17) = k5_xboole_0(A_15,k5_xboole_0(B_16,C_17)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_983,plain,(
    ! [A_127,B_128] : k5_xboole_0(k5_xboole_0(A_127,B_128),k3_xboole_0(A_127,B_128)) = k2_xboole_0(A_127,B_128) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_1023,plain,(
    ! [A_15,B_16] : k5_xboole_0(A_15,k5_xboole_0(B_16,k3_xboole_0(A_15,B_16))) = k2_xboole_0(A_15,B_16) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_983])).

tff(c_1576,plain,(
    ! [A_160,B_161] : k5_xboole_0(A_160,k4_xboole_0(B_161,A_160)) = k2_xboole_0(A_160,B_161) ),
    inference(demodulation,[status(thm),theory(equality)],[c_319,c_1023])).

tff(c_1613,plain,(
    ! [A_103] : k5_xboole_0(A_103,k1_xboole_0) = k2_xboole_0(A_103,A_103) ),
    inference(superposition,[status(thm),theory(equality)],[c_368,c_1576])).

tff(c_1628,plain,(
    ! [A_103] : k2_xboole_0(A_103,A_103) = A_103 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_1613])).

tff(c_68,plain,(
    ! [A_61,B_62] :
      ( k5_xboole_0(k1_tarski(A_61),k1_tarski(B_62)) = k2_tarski(A_61,B_62)
      | B_62 = A_61 ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_624,plain,(
    ! [A_118,B_119,C_120] : k5_xboole_0(k5_xboole_0(A_118,B_119),C_120) = k5_xboole_0(A_118,k5_xboole_0(B_119,C_120)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_4,plain,(
    ! [A_3] : k3_xboole_0(A_3,A_3) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_322,plain,(
    ! [A_3] : k5_xboole_0(A_3,A_3) = k4_xboole_0(A_3,A_3) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_301])).

tff(c_449,plain,(
    ! [A_3] : k5_xboole_0(A_3,A_3) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_368,c_322])).

tff(c_638,plain,(
    ! [A_118,B_119] : k5_xboole_0(A_118,k5_xboole_0(B_119,k5_xboole_0(A_118,B_119))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_624,c_449])).

tff(c_1056,plain,(
    ! [A_3] : k5_xboole_0(k5_xboole_0(A_3,A_3),A_3) = k2_xboole_0(A_3,A_3) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_983])).

tff(c_1069,plain,(
    ! [A_3] : k5_xboole_0(k1_xboole_0,A_3) = k2_xboole_0(A_3,A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_449,c_1056])).

tff(c_1634,plain,(
    ! [A_3] : k5_xboole_0(k1_xboole_0,A_3) = A_3 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1628,c_1069])).

tff(c_662,plain,(
    ! [A_3,C_120] : k5_xboole_0(A_3,k5_xboole_0(A_3,C_120)) = k5_xboole_0(k1_xboole_0,C_120) ),
    inference(superposition,[status(thm),theory(equality)],[c_449,c_624])).

tff(c_1848,plain,(
    ! [A_179,C_180] : k5_xboole_0(A_179,k5_xboole_0(A_179,C_180)) = C_180 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1634,c_662])).

tff(c_1904,plain,(
    ! [B_119,A_118] : k5_xboole_0(B_119,k5_xboole_0(A_118,B_119)) = k5_xboole_0(A_118,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_638,c_1848])).

tff(c_1948,plain,(
    ! [B_185,A_186] : k5_xboole_0(B_185,k5_xboole_0(A_186,B_185)) = A_186 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_1904])).

tff(c_1847,plain,(
    ! [A_3,C_120] : k5_xboole_0(A_3,k5_xboole_0(A_3,C_120)) = C_120 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1634,c_662])).

tff(c_2121,plain,(
    ! [B_189,A_190] : k5_xboole_0(B_189,A_190) = k5_xboole_0(A_190,B_189) ),
    inference(superposition,[status(thm),theory(equality)],[c_1948,c_1847])).

tff(c_25108,plain,(
    ! [B_442,A_443] :
      ( k5_xboole_0(k1_tarski(B_442),k1_tarski(A_443)) = k2_tarski(A_443,B_442)
      | B_442 = A_443 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_68,c_2121])).

tff(c_25228,plain,(
    ! [B_442,A_443] :
      ( k2_tarski(B_442,A_443) = k2_tarski(A_443,B_442)
      | B_442 = A_443
      | B_442 = A_443 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_25108,c_68])).

tff(c_166,plain,(
    ! [A_83,B_84] :
      ( r1_xboole_0(k1_tarski(A_83),k1_tarski(B_84))
      | B_84 = A_83 ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_16,plain,(
    ! [A_13,B_14] :
      ( k4_xboole_0(A_13,B_14) = A_13
      | ~ r1_xboole_0(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_3406,plain,(
    ! [A_243,B_244] :
      ( k4_xboole_0(k1_tarski(A_243),k1_tarski(B_244)) = k1_tarski(A_243)
      | B_244 = A_243 ) ),
    inference(resolution,[status(thm)],[c_166,c_16])).

tff(c_1063,plain,(
    ! [A_15,B_16] : k5_xboole_0(A_15,k4_xboole_0(B_16,A_15)) = k2_xboole_0(A_15,B_16) ),
    inference(demodulation,[status(thm),theory(equality)],[c_319,c_1023])).

tff(c_32475,plain,(
    ! [B_468,A_469] :
      ( k5_xboole_0(k1_tarski(B_468),k1_tarski(A_469)) = k2_xboole_0(k1_tarski(B_468),k1_tarski(A_469))
      | B_468 = A_469 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3406,c_1063])).

tff(c_101680,plain,(
    ! [A_644,B_645] :
      ( k2_xboole_0(k1_tarski(A_644),k1_tarski(B_645)) = k2_tarski(A_644,B_645)
      | B_645 = A_644
      | B_645 = A_644 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_68,c_32475])).

tff(c_2588,plain,(
    ! [A_205,B_206] : k5_xboole_0(A_205,k2_xboole_0(A_205,B_206)) = k4_xboole_0(B_206,A_205) ),
    inference(superposition,[status(thm),theory(equality)],[c_1063,c_1848])).

tff(c_1940,plain,(
    ! [B_119,A_118] : k5_xboole_0(B_119,k5_xboole_0(A_118,B_119)) = A_118 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_1904])).

tff(c_3665,plain,(
    ! [A_249,B_250] : k5_xboole_0(k2_xboole_0(A_249,B_250),k4_xboole_0(B_250,A_249)) = A_249 ),
    inference(superposition,[status(thm),theory(equality)],[c_2588,c_1940])).

tff(c_3677,plain,(
    ! [B_250,A_249] : k5_xboole_0(k4_xboole_0(B_250,A_249),A_249) = k2_xboole_0(A_249,B_250) ),
    inference(superposition,[status(thm),theory(equality)],[c_3665,c_1940])).

tff(c_3554,plain,(
    ! [A_247,B_248] : k5_xboole_0(k3_xboole_0(A_247,B_248),k4_xboole_0(B_248,A_247)) = B_248 ),
    inference(superposition,[status(thm),theory(equality)],[c_319,c_1948])).

tff(c_3573,plain,(
    ! [A_247,B_248] : k5_xboole_0(k3_xboole_0(A_247,B_248),B_248) = k4_xboole_0(B_248,A_247) ),
    inference(superposition,[status(thm),theory(equality)],[c_3554,c_1847])).

tff(c_6,plain,(
    ! [A_5,B_6] : k5_xboole_0(A_5,k3_xboole_0(A_5,B_6)) = k4_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_6920,plain,(
    ! [A_300,B_301,C_302] : k5_xboole_0(A_300,k5_xboole_0(k3_xboole_0(A_300,B_301),C_302)) = k5_xboole_0(k4_xboole_0(A_300,B_301),C_302) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_624])).

tff(c_6998,plain,(
    ! [A_247,B_248] : k5_xboole_0(k4_xboole_0(A_247,B_248),B_248) = k5_xboole_0(A_247,k4_xboole_0(B_248,A_247)) ),
    inference(superposition,[status(thm),theory(equality)],[c_3573,c_6920])).

tff(c_7106,plain,(
    ! [B_248,A_247] : k2_xboole_0(B_248,A_247) = k2_xboole_0(A_247,B_248) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3677,c_1063,c_6998])).

tff(c_64,plain,(
    ! [A_57,B_58] : k3_tarski(k2_tarski(A_57,B_58)) = k2_xboole_0(A_57,B_58) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_70,plain,(
    k3_tarski(k2_tarski(k1_tarski('#skF_3'),k1_tarski('#skF_4'))) != k2_tarski('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_71,plain,(
    k2_xboole_0(k1_tarski('#skF_3'),k1_tarski('#skF_4')) != k2_tarski('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_70])).

tff(c_7118,plain,(
    k2_xboole_0(k1_tarski('#skF_4'),k1_tarski('#skF_3')) != k2_tarski('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7106,c_71])).

tff(c_101800,plain,
    ( k2_tarski('#skF_3','#skF_4') != k2_tarski('#skF_4','#skF_3')
    | '#skF_3' = '#skF_4'
    | '#skF_3' = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_101680,c_7118])).

tff(c_101886,plain,(
    k2_tarski('#skF_3','#skF_4') != k2_tarski('#skF_4','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_101800])).

tff(c_101893,plain,(
    '#skF_3' = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_25228,c_101886])).

tff(c_101900,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_101893,c_101893,c_101886])).

tff(c_101901,plain,
    ( '#skF_3' = '#skF_4'
    | '#skF_3' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_101800])).

tff(c_101903,plain,(
    '#skF_3' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_101901])).

tff(c_101904,plain,(
    k2_xboole_0(k1_tarski('#skF_4'),k1_tarski('#skF_4')) != k2_tarski('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_101903,c_101903,c_7118])).

tff(c_101909,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_1628,c_101904])).

tff(c_101910,plain,(
    '#skF_3' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_101901])).

tff(c_101912,plain,(
    k2_xboole_0(k1_tarski('#skF_4'),k1_tarski('#skF_4')) != k2_tarski('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_101910,c_101910,c_7118])).

tff(c_101917,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_1628,c_101912])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:38:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 38.17/29.99  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 38.17/30.00  
% 38.17/30.00  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 38.17/30.01  %$ r2_hidden > r1_xboole_0 > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 38.17/30.01  
% 38.17/30.01  %Foreground sorts:
% 38.17/30.01  
% 38.17/30.01  
% 38.17/30.01  %Background operators:
% 38.17/30.01  
% 38.17/30.01  
% 38.17/30.01  %Foreground operators:
% 38.17/30.01  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 38.17/30.01  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 38.17/30.01  tff(k1_tarski, type, k1_tarski: $i > $i).
% 38.17/30.01  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 38.17/30.01  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 38.17/30.01  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 38.17/30.01  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 38.17/30.01  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 38.17/30.01  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 38.17/30.01  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 38.17/30.01  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 38.17/30.01  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 38.17/30.01  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 38.17/30.01  tff('#skF_3', type, '#skF_3': $i).
% 38.17/30.01  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 38.17/30.01  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 38.17/30.01  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 38.17/30.01  tff(k3_tarski, type, k3_tarski: $i > $i).
% 38.17/30.01  tff('#skF_4', type, '#skF_4': $i).
% 38.17/30.01  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 38.17/30.01  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 38.17/30.01  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 38.17/30.01  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 38.17/30.01  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 38.17/30.01  
% 38.42/30.02  tff(f_66, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 38.42/30.02  tff(f_41, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 38.42/30.02  tff(f_37, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 38.42/30.02  tff(f_35, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 38.42/30.02  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 38.42/30.02  tff(f_31, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 38.42/30.02  tff(f_39, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 38.42/30.02  tff(f_47, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_xboole_1)).
% 38.42/30.02  tff(f_49, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_xboole_1)).
% 38.42/30.02  tff(f_94, axiom, (![A, B]: (~(A = B) => (k5_xboole_0(k1_tarski(A), k1_tarski(B)) = k2_tarski(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_zfmisc_1)).
% 38.42/30.02  tff(f_29, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 38.42/30.02  tff(f_89, axiom, (![A, B]: (~(A = B) => r1_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_zfmisc_1)).
% 38.42/30.02  tff(f_45, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 38.42/30.02  tff(f_84, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 38.42/30.02  tff(f_97, negated_conjecture, ~(![A, B]: (k3_tarski(k2_tarski(k1_tarski(A), k1_tarski(B))) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t32_zfmisc_1)).
% 38.42/30.02  tff(c_48, plain, (![A_27]: (k2_tarski(A_27, A_27)=k1_tarski(A_27))), inference(cnfTransformation, [status(thm)], [f_66])).
% 38.42/30.02  tff(c_14, plain, (![A_12]: (k5_xboole_0(A_12, k1_xboole_0)=A_12)), inference(cnfTransformation, [status(thm)], [f_41])).
% 38.42/30.02  tff(c_10, plain, (![A_9]: (r1_tarski(k1_xboole_0, A_9))), inference(cnfTransformation, [status(thm)], [f_37])).
% 38.42/30.02  tff(c_176, plain, (![A_87, B_88]: (k3_xboole_0(A_87, B_88)=A_87 | ~r1_tarski(A_87, B_88))), inference(cnfTransformation, [status(thm)], [f_35])).
% 38.42/30.02  tff(c_199, plain, (![A_91]: (k3_xboole_0(k1_xboole_0, A_91)=k1_xboole_0)), inference(resolution, [status(thm)], [c_10, c_176])).
% 38.42/30.02  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 38.42/30.02  tff(c_204, plain, (![A_91]: (k3_xboole_0(A_91, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_199, c_2])).
% 38.42/30.02  tff(c_301, plain, (![A_100, B_101]: (k5_xboole_0(A_100, k3_xboole_0(A_100, B_101))=k4_xboole_0(A_100, B_101))), inference(cnfTransformation, [status(thm)], [f_31])).
% 38.42/30.02  tff(c_310, plain, (![A_91]: (k5_xboole_0(A_91, k1_xboole_0)=k4_xboole_0(A_91, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_204, c_301])).
% 38.42/30.02  tff(c_348, plain, (![A_103]: (k4_xboole_0(A_103, k1_xboole_0)=A_103)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_310])).
% 38.42/30.02  tff(c_12, plain, (![A_10, B_11]: (k4_xboole_0(A_10, k4_xboole_0(A_10, B_11))=k3_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_39])).
% 38.42/30.02  tff(c_358, plain, (![A_103]: (k4_xboole_0(A_103, A_103)=k3_xboole_0(A_103, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_348, c_12])).
% 38.42/30.02  tff(c_368, plain, (![A_103]: (k4_xboole_0(A_103, A_103)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_204, c_358])).
% 38.42/30.02  tff(c_319, plain, (![B_2, A_1]: (k5_xboole_0(B_2, k3_xboole_0(A_1, B_2))=k4_xboole_0(B_2, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_301])).
% 38.42/30.02  tff(c_20, plain, (![A_15, B_16, C_17]: (k5_xboole_0(k5_xboole_0(A_15, B_16), C_17)=k5_xboole_0(A_15, k5_xboole_0(B_16, C_17)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 38.42/30.02  tff(c_983, plain, (![A_127, B_128]: (k5_xboole_0(k5_xboole_0(A_127, B_128), k3_xboole_0(A_127, B_128))=k2_xboole_0(A_127, B_128))), inference(cnfTransformation, [status(thm)], [f_49])).
% 38.42/30.02  tff(c_1023, plain, (![A_15, B_16]: (k5_xboole_0(A_15, k5_xboole_0(B_16, k3_xboole_0(A_15, B_16)))=k2_xboole_0(A_15, B_16))), inference(superposition, [status(thm), theory('equality')], [c_20, c_983])).
% 38.42/30.02  tff(c_1576, plain, (![A_160, B_161]: (k5_xboole_0(A_160, k4_xboole_0(B_161, A_160))=k2_xboole_0(A_160, B_161))), inference(demodulation, [status(thm), theory('equality')], [c_319, c_1023])).
% 38.42/30.02  tff(c_1613, plain, (![A_103]: (k5_xboole_0(A_103, k1_xboole_0)=k2_xboole_0(A_103, A_103))), inference(superposition, [status(thm), theory('equality')], [c_368, c_1576])).
% 38.42/30.02  tff(c_1628, plain, (![A_103]: (k2_xboole_0(A_103, A_103)=A_103)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_1613])).
% 38.42/30.02  tff(c_68, plain, (![A_61, B_62]: (k5_xboole_0(k1_tarski(A_61), k1_tarski(B_62))=k2_tarski(A_61, B_62) | B_62=A_61)), inference(cnfTransformation, [status(thm)], [f_94])).
% 38.42/30.02  tff(c_624, plain, (![A_118, B_119, C_120]: (k5_xboole_0(k5_xboole_0(A_118, B_119), C_120)=k5_xboole_0(A_118, k5_xboole_0(B_119, C_120)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 38.42/30.02  tff(c_4, plain, (![A_3]: (k3_xboole_0(A_3, A_3)=A_3)), inference(cnfTransformation, [status(thm)], [f_29])).
% 38.42/30.02  tff(c_322, plain, (![A_3]: (k5_xboole_0(A_3, A_3)=k4_xboole_0(A_3, A_3))), inference(superposition, [status(thm), theory('equality')], [c_4, c_301])).
% 38.42/30.02  tff(c_449, plain, (![A_3]: (k5_xboole_0(A_3, A_3)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_368, c_322])).
% 38.42/30.02  tff(c_638, plain, (![A_118, B_119]: (k5_xboole_0(A_118, k5_xboole_0(B_119, k5_xboole_0(A_118, B_119)))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_624, c_449])).
% 38.42/30.02  tff(c_1056, plain, (![A_3]: (k5_xboole_0(k5_xboole_0(A_3, A_3), A_3)=k2_xboole_0(A_3, A_3))), inference(superposition, [status(thm), theory('equality')], [c_4, c_983])).
% 38.42/30.02  tff(c_1069, plain, (![A_3]: (k5_xboole_0(k1_xboole_0, A_3)=k2_xboole_0(A_3, A_3))), inference(demodulation, [status(thm), theory('equality')], [c_449, c_1056])).
% 38.42/30.02  tff(c_1634, plain, (![A_3]: (k5_xboole_0(k1_xboole_0, A_3)=A_3)), inference(demodulation, [status(thm), theory('equality')], [c_1628, c_1069])).
% 38.42/30.02  tff(c_662, plain, (![A_3, C_120]: (k5_xboole_0(A_3, k5_xboole_0(A_3, C_120))=k5_xboole_0(k1_xboole_0, C_120))), inference(superposition, [status(thm), theory('equality')], [c_449, c_624])).
% 38.42/30.02  tff(c_1848, plain, (![A_179, C_180]: (k5_xboole_0(A_179, k5_xboole_0(A_179, C_180))=C_180)), inference(demodulation, [status(thm), theory('equality')], [c_1634, c_662])).
% 38.42/30.02  tff(c_1904, plain, (![B_119, A_118]: (k5_xboole_0(B_119, k5_xboole_0(A_118, B_119))=k5_xboole_0(A_118, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_638, c_1848])).
% 38.42/30.02  tff(c_1948, plain, (![B_185, A_186]: (k5_xboole_0(B_185, k5_xboole_0(A_186, B_185))=A_186)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_1904])).
% 38.42/30.02  tff(c_1847, plain, (![A_3, C_120]: (k5_xboole_0(A_3, k5_xboole_0(A_3, C_120))=C_120)), inference(demodulation, [status(thm), theory('equality')], [c_1634, c_662])).
% 38.42/30.02  tff(c_2121, plain, (![B_189, A_190]: (k5_xboole_0(B_189, A_190)=k5_xboole_0(A_190, B_189))), inference(superposition, [status(thm), theory('equality')], [c_1948, c_1847])).
% 38.42/30.02  tff(c_25108, plain, (![B_442, A_443]: (k5_xboole_0(k1_tarski(B_442), k1_tarski(A_443))=k2_tarski(A_443, B_442) | B_442=A_443)), inference(superposition, [status(thm), theory('equality')], [c_68, c_2121])).
% 38.42/30.02  tff(c_25228, plain, (![B_442, A_443]: (k2_tarski(B_442, A_443)=k2_tarski(A_443, B_442) | B_442=A_443 | B_442=A_443)), inference(superposition, [status(thm), theory('equality')], [c_25108, c_68])).
% 38.42/30.02  tff(c_166, plain, (![A_83, B_84]: (r1_xboole_0(k1_tarski(A_83), k1_tarski(B_84)) | B_84=A_83)), inference(cnfTransformation, [status(thm)], [f_89])).
% 38.42/30.02  tff(c_16, plain, (![A_13, B_14]: (k4_xboole_0(A_13, B_14)=A_13 | ~r1_xboole_0(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_45])).
% 38.42/30.02  tff(c_3406, plain, (![A_243, B_244]: (k4_xboole_0(k1_tarski(A_243), k1_tarski(B_244))=k1_tarski(A_243) | B_244=A_243)), inference(resolution, [status(thm)], [c_166, c_16])).
% 38.42/30.02  tff(c_1063, plain, (![A_15, B_16]: (k5_xboole_0(A_15, k4_xboole_0(B_16, A_15))=k2_xboole_0(A_15, B_16))), inference(demodulation, [status(thm), theory('equality')], [c_319, c_1023])).
% 38.42/30.02  tff(c_32475, plain, (![B_468, A_469]: (k5_xboole_0(k1_tarski(B_468), k1_tarski(A_469))=k2_xboole_0(k1_tarski(B_468), k1_tarski(A_469)) | B_468=A_469)), inference(superposition, [status(thm), theory('equality')], [c_3406, c_1063])).
% 38.42/30.02  tff(c_101680, plain, (![A_644, B_645]: (k2_xboole_0(k1_tarski(A_644), k1_tarski(B_645))=k2_tarski(A_644, B_645) | B_645=A_644 | B_645=A_644)), inference(superposition, [status(thm), theory('equality')], [c_68, c_32475])).
% 38.42/30.02  tff(c_2588, plain, (![A_205, B_206]: (k5_xboole_0(A_205, k2_xboole_0(A_205, B_206))=k4_xboole_0(B_206, A_205))), inference(superposition, [status(thm), theory('equality')], [c_1063, c_1848])).
% 38.42/30.02  tff(c_1940, plain, (![B_119, A_118]: (k5_xboole_0(B_119, k5_xboole_0(A_118, B_119))=A_118)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_1904])).
% 38.42/30.02  tff(c_3665, plain, (![A_249, B_250]: (k5_xboole_0(k2_xboole_0(A_249, B_250), k4_xboole_0(B_250, A_249))=A_249)), inference(superposition, [status(thm), theory('equality')], [c_2588, c_1940])).
% 38.42/30.02  tff(c_3677, plain, (![B_250, A_249]: (k5_xboole_0(k4_xboole_0(B_250, A_249), A_249)=k2_xboole_0(A_249, B_250))), inference(superposition, [status(thm), theory('equality')], [c_3665, c_1940])).
% 38.42/30.02  tff(c_3554, plain, (![A_247, B_248]: (k5_xboole_0(k3_xboole_0(A_247, B_248), k4_xboole_0(B_248, A_247))=B_248)), inference(superposition, [status(thm), theory('equality')], [c_319, c_1948])).
% 38.42/30.02  tff(c_3573, plain, (![A_247, B_248]: (k5_xboole_0(k3_xboole_0(A_247, B_248), B_248)=k4_xboole_0(B_248, A_247))), inference(superposition, [status(thm), theory('equality')], [c_3554, c_1847])).
% 38.42/30.02  tff(c_6, plain, (![A_5, B_6]: (k5_xboole_0(A_5, k3_xboole_0(A_5, B_6))=k4_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_31])).
% 38.42/30.02  tff(c_6920, plain, (![A_300, B_301, C_302]: (k5_xboole_0(A_300, k5_xboole_0(k3_xboole_0(A_300, B_301), C_302))=k5_xboole_0(k4_xboole_0(A_300, B_301), C_302))), inference(superposition, [status(thm), theory('equality')], [c_6, c_624])).
% 38.42/30.02  tff(c_6998, plain, (![A_247, B_248]: (k5_xboole_0(k4_xboole_0(A_247, B_248), B_248)=k5_xboole_0(A_247, k4_xboole_0(B_248, A_247)))), inference(superposition, [status(thm), theory('equality')], [c_3573, c_6920])).
% 38.42/30.02  tff(c_7106, plain, (![B_248, A_247]: (k2_xboole_0(B_248, A_247)=k2_xboole_0(A_247, B_248))), inference(demodulation, [status(thm), theory('equality')], [c_3677, c_1063, c_6998])).
% 38.42/30.02  tff(c_64, plain, (![A_57, B_58]: (k3_tarski(k2_tarski(A_57, B_58))=k2_xboole_0(A_57, B_58))), inference(cnfTransformation, [status(thm)], [f_84])).
% 38.42/30.02  tff(c_70, plain, (k3_tarski(k2_tarski(k1_tarski('#skF_3'), k1_tarski('#skF_4')))!=k2_tarski('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_97])).
% 38.42/30.02  tff(c_71, plain, (k2_xboole_0(k1_tarski('#skF_3'), k1_tarski('#skF_4'))!=k2_tarski('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_70])).
% 38.42/30.02  tff(c_7118, plain, (k2_xboole_0(k1_tarski('#skF_4'), k1_tarski('#skF_3'))!=k2_tarski('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_7106, c_71])).
% 38.42/30.02  tff(c_101800, plain, (k2_tarski('#skF_3', '#skF_4')!=k2_tarski('#skF_4', '#skF_3') | '#skF_3'='#skF_4' | '#skF_3'='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_101680, c_7118])).
% 38.42/30.02  tff(c_101886, plain, (k2_tarski('#skF_3', '#skF_4')!=k2_tarski('#skF_4', '#skF_3')), inference(splitLeft, [status(thm)], [c_101800])).
% 38.42/30.02  tff(c_101893, plain, ('#skF_3'='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_25228, c_101886])).
% 38.42/30.02  tff(c_101900, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_101893, c_101893, c_101886])).
% 38.42/30.02  tff(c_101901, plain, ('#skF_3'='#skF_4' | '#skF_3'='#skF_4'), inference(splitRight, [status(thm)], [c_101800])).
% 38.42/30.02  tff(c_101903, plain, ('#skF_3'='#skF_4'), inference(splitLeft, [status(thm)], [c_101901])).
% 38.42/30.02  tff(c_101904, plain, (k2_xboole_0(k1_tarski('#skF_4'), k1_tarski('#skF_4'))!=k2_tarski('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_101903, c_101903, c_7118])).
% 38.42/30.02  tff(c_101909, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_1628, c_101904])).
% 38.42/30.02  tff(c_101910, plain, ('#skF_3'='#skF_4'), inference(splitRight, [status(thm)], [c_101901])).
% 38.42/30.02  tff(c_101912, plain, (k2_xboole_0(k1_tarski('#skF_4'), k1_tarski('#skF_4'))!=k2_tarski('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_101910, c_101910, c_7118])).
% 38.42/30.02  tff(c_101917, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_1628, c_101912])).
% 38.42/30.02  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 38.42/30.02  
% 38.42/30.02  Inference rules
% 38.42/30.02  ----------------------
% 38.42/30.02  #Ref     : 0
% 38.42/30.02  #Sup     : 26579
% 38.42/30.02  #Fact    : 6
% 38.42/30.02  #Define  : 0
% 38.42/30.02  #Split   : 4
% 38.42/30.02  #Chain   : 0
% 38.42/30.02  #Close   : 0
% 38.42/30.02  
% 38.42/30.02  Ordering : KBO
% 38.42/30.02  
% 38.42/30.02  Simplification rules
% 38.42/30.02  ----------------------
% 38.42/30.02  #Subsume      : 2441
% 38.42/30.02  #Demod        : 43490
% 38.42/30.02  #Tautology    : 8931
% 38.42/30.02  #SimpNegUnit  : 0
% 38.42/30.02  #BackRed      : 26
% 38.42/30.02  
% 38.42/30.02  #Partial instantiations: 0
% 38.42/30.02  #Strategies tried      : 1
% 38.42/30.02  
% 38.42/30.02  Timing (in seconds)
% 38.42/30.02  ----------------------
% 38.42/30.03  Preprocessing        : 0.33
% 38.42/30.03  Parsing              : 0.17
% 38.42/30.03  CNF conversion       : 0.02
% 38.42/30.03  Main loop            : 28.92
% 38.42/30.03  Inferencing          : 2.66
% 38.42/30.03  Reduction            : 21.29
% 38.42/30.03  Demodulation         : 20.31
% 38.42/30.03  BG Simplification    : 0.47
% 38.42/30.03  Subsumption          : 3.71
% 38.42/30.03  Abstraction          : 0.87
% 38.42/30.03  MUC search           : 0.00
% 38.42/30.03  Cooper               : 0.00
% 38.42/30.03  Total                : 29.29
% 38.42/30.03  Index Insertion      : 0.00
% 38.42/30.03  Index Deletion       : 0.00
% 38.42/30.03  Index Matching       : 0.00
% 38.42/30.03  BG Taut test         : 0.00
%------------------------------------------------------------------------------

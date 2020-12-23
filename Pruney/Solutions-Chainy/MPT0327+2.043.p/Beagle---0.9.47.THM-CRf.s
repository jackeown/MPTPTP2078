%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:54:36 EST 2020

% Result     : Theorem 6.87s
% Output     : CNFRefutation 6.87s
% Verified   : 
% Statistics : Number of formulae       :  115 (3962 expanded)
%              Number of leaves         :   30 (1337 expanded)
%              Depth                    :   23
%              Number of atoms          :  110 (5327 expanded)
%              Number of equality atoms :   88 (3437 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1

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

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_74,negated_conjecture,(
    ~ ! [A,B] :
        ( r2_hidden(A,B)
       => k2_xboole_0(k4_xboole_0(B,k1_tarski(A)),k1_tarski(A)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t140_zfmisc_1)).

tff(f_47,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_33,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_37,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_39,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_67,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_53,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_55,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_xboole_1)).

tff(f_49,axiom,(
    ! [A,B,C] : k3_xboole_0(A,k4_xboole_0(B,C)) = k4_xboole_0(k3_xboole_0(A,B),C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).

tff(c_46,plain,(
    r2_hidden('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_20,plain,(
    ! [A_13] : k4_xboole_0(A_13,k1_xboole_0) = A_13 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_8,plain,(
    ! [B_4] : r1_tarski(B_4,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_192,plain,(
    ! [A_57,B_58] :
      ( k4_xboole_0(A_57,B_58) = k1_xboole_0
      | ~ r1_tarski(A_57,B_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_209,plain,(
    ! [B_59] : k4_xboole_0(B_59,B_59) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_8,c_192])).

tff(c_18,plain,(
    ! [A_11,B_12] : r1_tarski(k4_xboole_0(A_11,B_12),A_11) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_237,plain,(
    ! [B_60] : r1_tarski(k1_xboole_0,B_60) ),
    inference(superposition,[status(thm),theory(equality)],[c_209,c_18])).

tff(c_16,plain,(
    ! [A_9,B_10] :
      ( k3_xboole_0(A_9,B_10) = A_9
      | ~ r1_tarski(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_247,plain,(
    ! [B_61] : k3_xboole_0(k1_xboole_0,B_61) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_237,c_16])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_256,plain,(
    ! [B_61] : k3_xboole_0(B_61,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_247,c_2])).

tff(c_340,plain,(
    ! [A_66,B_67] : k5_xboole_0(A_66,k3_xboole_0(A_66,B_67)) = k4_xboole_0(A_66,B_67) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_349,plain,(
    ! [B_61] : k5_xboole_0(B_61,k1_xboole_0) = k4_xboole_0(B_61,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_256,c_340])).

tff(c_364,plain,(
    ! [B_61] : k5_xboole_0(B_61,k1_xboole_0) = B_61 ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_349])).

tff(c_40,plain,(
    ! [A_33,B_34] :
      ( r1_tarski(k1_tarski(A_33),B_34)
      | ~ r2_hidden(A_33,B_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_206,plain,(
    ! [A_33,B_34] :
      ( k4_xboole_0(k1_tarski(A_33),B_34) = k1_xboole_0
      | ~ r2_hidden(A_33,B_34) ) ),
    inference(resolution,[status(thm)],[c_40,c_192])).

tff(c_358,plain,(
    ! [A_1,B_2] : k5_xboole_0(A_1,k3_xboole_0(B_2,A_1)) = k4_xboole_0(A_1,B_2) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_340])).

tff(c_26,plain,(
    ! [A_18,B_19,C_20] : k5_xboole_0(k5_xboole_0(A_18,B_19),C_20) = k5_xboole_0(A_18,k5_xboole_0(B_19,C_20)) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_941,plain,(
    ! [A_100,B_101] : k5_xboole_0(k5_xboole_0(A_100,B_101),k3_xboole_0(A_100,B_101)) = k2_xboole_0(A_100,B_101) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_972,plain,(
    ! [A_18,B_19] : k5_xboole_0(A_18,k5_xboole_0(B_19,k3_xboole_0(A_18,B_19))) = k2_xboole_0(A_18,B_19) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_941])).

tff(c_1330,plain,(
    ! [A_115,B_116] : k5_xboole_0(A_115,k4_xboole_0(B_116,A_115)) = k2_xboole_0(A_115,B_116) ),
    inference(demodulation,[status(thm),theory(equality)],[c_358,c_972])).

tff(c_1367,plain,(
    ! [B_34,A_33] :
      ( k2_xboole_0(B_34,k1_tarski(A_33)) = k5_xboole_0(B_34,k1_xboole_0)
      | ~ r2_hidden(A_33,B_34) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_206,c_1330])).

tff(c_1384,plain,(
    ! [B_34,A_33] :
      ( k2_xboole_0(B_34,k1_tarski(A_33)) = B_34
      | ~ r2_hidden(A_33,B_34) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_364,c_1367])).

tff(c_1008,plain,(
    ! [A_18,B_19] : k5_xboole_0(A_18,k4_xboole_0(B_19,A_18)) = k2_xboole_0(A_18,B_19) ),
    inference(demodulation,[status(thm),theory(equality)],[c_358,c_972])).

tff(c_208,plain,(
    ! [B_4] : k4_xboole_0(B_4,B_4) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_8,c_192])).

tff(c_1373,plain,(
    ! [B_4] : k5_xboole_0(B_4,k1_xboole_0) = k2_xboole_0(B_4,B_4) ),
    inference(superposition,[status(thm),theory(equality)],[c_208,c_1330])).

tff(c_1386,plain,(
    ! [B_4] : k2_xboole_0(B_4,B_4) = B_4 ),
    inference(demodulation,[status(thm),theory(equality)],[c_364,c_1373])).

tff(c_155,plain,(
    ! [A_48,B_49] :
      ( k3_xboole_0(A_48,B_49) = A_48
      | ~ r1_tarski(A_48,B_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_163,plain,(
    ! [B_4] : k3_xboole_0(B_4,B_4) = B_4 ),
    inference(resolution,[status(thm)],[c_8,c_155])).

tff(c_355,plain,(
    ! [B_4] : k5_xboole_0(B_4,B_4) = k4_xboole_0(B_4,B_4) ),
    inference(superposition,[status(thm),theory(equality)],[c_163,c_340])).

tff(c_366,plain,(
    ! [B_4] : k5_xboole_0(B_4,B_4) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_208,c_355])).

tff(c_996,plain,(
    ! [B_4] : k5_xboole_0(k5_xboole_0(B_4,B_4),B_4) = k2_xboole_0(B_4,B_4) ),
    inference(superposition,[status(thm),theory(equality)],[c_163,c_941])).

tff(c_1012,plain,(
    ! [B_4] : k5_xboole_0(k1_xboole_0,B_4) = k2_xboole_0(B_4,B_4) ),
    inference(demodulation,[status(thm),theory(equality)],[c_366,c_996])).

tff(c_1390,plain,(
    ! [B_4] : k5_xboole_0(k1_xboole_0,B_4) = B_4 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1386,c_1012])).

tff(c_671,plain,(
    ! [A_89,B_90,C_91] : k5_xboole_0(k5_xboole_0(A_89,B_90),C_91) = k5_xboole_0(A_89,k5_xboole_0(B_90,C_91)) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_716,plain,(
    ! [B_4,C_91] : k5_xboole_0(B_4,k5_xboole_0(B_4,C_91)) = k5_xboole_0(k1_xboole_0,C_91) ),
    inference(superposition,[status(thm),theory(equality)],[c_366,c_671])).

tff(c_1698,plain,(
    ! [B_125,C_126] : k5_xboole_0(B_125,k5_xboole_0(B_125,C_126)) = C_126 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1390,c_716])).

tff(c_2650,plain,(
    ! [A_146,B_147] : k5_xboole_0(A_146,k2_xboole_0(A_146,B_147)) = k4_xboole_0(B_147,A_146) ),
    inference(superposition,[status(thm),theory(equality)],[c_1008,c_1698])).

tff(c_689,plain,(
    ! [A_89,B_90] : k5_xboole_0(A_89,k5_xboole_0(B_90,k5_xboole_0(A_89,B_90))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_671,c_366])).

tff(c_1748,plain,(
    ! [B_90,A_89] : k5_xboole_0(B_90,k5_xboole_0(A_89,B_90)) = k5_xboole_0(A_89,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_689,c_1698])).

tff(c_1787,plain,(
    ! [B_90,A_89] : k5_xboole_0(B_90,k5_xboole_0(A_89,B_90)) = A_89 ),
    inference(demodulation,[status(thm),theory(equality)],[c_364,c_1748])).

tff(c_3506,plain,(
    ! [A_164,B_165] : k5_xboole_0(k2_xboole_0(A_164,B_165),k4_xboole_0(B_165,A_164)) = A_164 ),
    inference(superposition,[status(thm),theory(equality)],[c_2650,c_1787])).

tff(c_3518,plain,(
    ! [B_165,A_164] : k5_xboole_0(k4_xboole_0(B_165,A_164),A_164) = k2_xboole_0(A_164,B_165) ),
    inference(superposition,[status(thm),theory(equality)],[c_3506,c_1787])).

tff(c_2807,plain,(
    ! [A_150,B_151] : k5_xboole_0(A_150,k4_xboole_0(A_150,B_151)) = k3_xboole_0(B_151,A_150) ),
    inference(superposition,[status(thm),theory(equality)],[c_358,c_1698])).

tff(c_3642,plain,(
    ! [A_168,B_169] : k5_xboole_0(k4_xboole_0(A_168,B_169),k3_xboole_0(B_169,A_168)) = A_168 ),
    inference(superposition,[status(thm),theory(equality)],[c_2807,c_1787])).

tff(c_3660,plain,(
    ! [B_169,A_168] : k5_xboole_0(k3_xboole_0(B_169,A_168),A_168) = k4_xboole_0(A_168,B_169) ),
    inference(superposition,[status(thm),theory(equality)],[c_3642,c_1787])).

tff(c_14,plain,(
    ! [A_7,B_8] : k5_xboole_0(A_7,k3_xboole_0(A_7,B_8)) = k4_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_6329,plain,(
    ! [A_213,B_214,C_215] : k5_xboole_0(A_213,k5_xboole_0(k3_xboole_0(A_213,B_214),C_215)) = k5_xboole_0(k4_xboole_0(A_213,B_214),C_215) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_671])).

tff(c_6385,plain,(
    ! [B_169,A_168] : k5_xboole_0(k4_xboole_0(B_169,A_168),A_168) = k5_xboole_0(B_169,k4_xboole_0(A_168,B_169)) ),
    inference(superposition,[status(thm),theory(equality)],[c_3660,c_6329])).

tff(c_6498,plain,(
    ! [B_169,A_168] : k2_xboole_0(B_169,A_168) = k2_xboole_0(A_168,B_169) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3518,c_1008,c_6385])).

tff(c_246,plain,(
    ! [B_60] : k3_xboole_0(k1_xboole_0,B_60) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_237,c_16])).

tff(c_1023,plain,(
    ! [B_103] : k5_xboole_0(k1_xboole_0,B_103) = k2_xboole_0(B_103,B_103) ),
    inference(demodulation,[status(thm),theory(equality)],[c_366,c_996])).

tff(c_28,plain,(
    ! [A_21,B_22] : k5_xboole_0(k5_xboole_0(A_21,B_22),k3_xboole_0(A_21,B_22)) = k2_xboole_0(A_21,B_22) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_1032,plain,(
    ! [B_103] : k5_xboole_0(k2_xboole_0(B_103,B_103),k3_xboole_0(k1_xboole_0,B_103)) = k2_xboole_0(k1_xboole_0,B_103) ),
    inference(superposition,[status(thm),theory(equality)],[c_1023,c_28])).

tff(c_1066,plain,(
    ! [B_103] : k2_xboole_0(k1_xboole_0,B_103) = k2_xboole_0(B_103,B_103) ),
    inference(demodulation,[status(thm),theory(equality)],[c_364,c_246,c_1032])).

tff(c_1389,plain,(
    ! [B_103] : k2_xboole_0(k1_xboole_0,B_103) = B_103 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1386,c_1066])).

tff(c_788,plain,(
    ! [A_95,B_96,C_97] : k4_xboole_0(k3_xboole_0(A_95,B_96),C_97) = k3_xboole_0(A_95,k4_xboole_0(B_96,C_97)) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_839,plain,(
    ! [B_2,A_1,C_97] : k4_xboole_0(k3_xboole_0(B_2,A_1),C_97) = k3_xboole_0(A_1,k4_xboole_0(B_2,C_97)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_788])).

tff(c_1697,plain,(
    ! [B_4,C_91] : k5_xboole_0(B_4,k5_xboole_0(B_4,C_91)) = C_91 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1390,c_716])).

tff(c_3663,plain,(
    ! [A_168,B_169] : k5_xboole_0(k4_xboole_0(A_168,B_169),A_168) = k3_xboole_0(B_169,A_168) ),
    inference(superposition,[status(thm),theory(equality)],[c_3642,c_1697])).

tff(c_162,plain,(
    ! [A_11,B_12] : k3_xboole_0(k4_xboole_0(A_11,B_12),A_11) = k4_xboole_0(A_11,B_12) ),
    inference(resolution,[status(thm)],[c_18,c_155])).

tff(c_4220,plain,(
    ! [B_178,A_179] : k5_xboole_0(k3_xboole_0(B_178,A_179),A_179) = k4_xboole_0(A_179,B_178) ),
    inference(superposition,[status(thm),theory(equality)],[c_3642,c_1787])).

tff(c_4283,plain,(
    ! [A_11,B_12] : k5_xboole_0(k4_xboole_0(A_11,B_12),A_11) = k4_xboole_0(A_11,k4_xboole_0(A_11,B_12)) ),
    inference(superposition,[status(thm),theory(equality)],[c_162,c_4220])).

tff(c_5192,plain,(
    ! [A_195,B_196] : k4_xboole_0(A_195,k4_xboole_0(A_195,B_196)) = k3_xboole_0(B_196,A_195) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3663,c_4283])).

tff(c_207,plain,(
    ! [A_11,B_12] : k4_xboole_0(k4_xboole_0(A_11,B_12),A_11) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_18,c_192])).

tff(c_5619,plain,(
    ! [B_203,A_204] : k4_xboole_0(k3_xboole_0(B_203,A_204),A_204) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_5192,c_207])).

tff(c_5703,plain,(
    ! [C_97,B_2] : k3_xboole_0(C_97,k4_xboole_0(B_2,C_97)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_839,c_5619])).

tff(c_1794,plain,(
    ! [B_127,A_128] : k5_xboole_0(B_127,k5_xboole_0(A_128,B_127)) = A_128 ),
    inference(demodulation,[status(thm),theory(equality)],[c_364,c_1748])).

tff(c_1866,plain,(
    ! [A_7,B_8] : k5_xboole_0(k3_xboole_0(A_7,B_8),k4_xboole_0(A_7,B_8)) = A_7 ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_1794])).

tff(c_7365,plain,(
    ! [A_226,B_227,C_228] : k5_xboole_0(k5_xboole_0(A_226,B_227),k5_xboole_0(k3_xboole_0(A_226,B_227),C_228)) = k5_xboole_0(k2_xboole_0(A_226,B_227),C_228) ),
    inference(superposition,[status(thm),theory(equality)],[c_941,c_26])).

tff(c_7475,plain,(
    ! [A_7,B_8] : k5_xboole_0(k2_xboole_0(A_7,B_8),k4_xboole_0(A_7,B_8)) = k5_xboole_0(k5_xboole_0(A_7,B_8),A_7) ),
    inference(superposition,[status(thm),theory(equality)],[c_1866,c_7365])).

tff(c_7672,plain,(
    ! [A_229,B_230] : k5_xboole_0(k2_xboole_0(A_229,B_230),k4_xboole_0(A_229,B_230)) = B_230 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1787,c_26,c_7475])).

tff(c_1830,plain,(
    ! [B_4,C_91] : k5_xboole_0(k5_xboole_0(B_4,C_91),C_91) = B_4 ),
    inference(superposition,[status(thm),theory(equality)],[c_1697,c_1794])).

tff(c_7688,plain,(
    ! [B_230,A_229] : k5_xboole_0(B_230,k4_xboole_0(A_229,B_230)) = k2_xboole_0(A_229,B_230) ),
    inference(superposition,[status(thm),theory(equality)],[c_7672,c_1830])).

tff(c_944,plain,(
    ! [A_100,B_101] : k5_xboole_0(k2_xboole_0(A_100,B_101),k3_xboole_0(k5_xboole_0(A_100,B_101),k3_xboole_0(A_100,B_101))) = k2_xboole_0(k5_xboole_0(A_100,B_101),k3_xboole_0(A_100,B_101)) ),
    inference(superposition,[status(thm),theory(equality)],[c_941,c_28])).

tff(c_1003,plain,(
    ! [A_100,B_101] : k5_xboole_0(k2_xboole_0(A_100,B_101),k3_xboole_0(k3_xboole_0(A_100,B_101),k5_xboole_0(A_100,B_101))) = k2_xboole_0(k5_xboole_0(A_100,B_101),k3_xboole_0(A_100,B_101)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_944])).

tff(c_10657,plain,(
    ! [A_259,B_260] : k5_xboole_0(k2_xboole_0(A_259,B_260),k3_xboole_0(k3_xboole_0(A_259,B_260),k5_xboole_0(A_259,B_260))) = k2_xboole_0(k3_xboole_0(A_259,B_260),k5_xboole_0(A_259,B_260)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6498,c_1003])).

tff(c_10729,plain,(
    ! [B_230,A_229] : k5_xboole_0(k2_xboole_0(B_230,k4_xboole_0(A_229,B_230)),k3_xboole_0(k3_xboole_0(B_230,k4_xboole_0(A_229,B_230)),k2_xboole_0(A_229,B_230))) = k2_xboole_0(k3_xboole_0(B_230,k4_xboole_0(A_229,B_230)),k5_xboole_0(B_230,k4_xboole_0(A_229,B_230))) ),
    inference(superposition,[status(thm),theory(equality)],[c_7688,c_10657])).

tff(c_10922,plain,(
    ! [B_230,A_229] : k2_xboole_0(B_230,k4_xboole_0(A_229,B_230)) = k2_xboole_0(B_230,A_229) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1389,c_5703,c_364,c_246,c_2,c_5703,c_1008,c_2,c_10729])).

tff(c_44,plain,(
    k2_xboole_0(k4_xboole_0('#skF_2',k1_tarski('#skF_1')),k1_tarski('#skF_1')) != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_6518,plain,(
    k2_xboole_0(k1_tarski('#skF_1'),k4_xboole_0('#skF_2',k1_tarski('#skF_1'))) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6498,c_44])).

tff(c_11473,plain,(
    k2_xboole_0(k1_tarski('#skF_1'),'#skF_2') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10922,c_6518])).

tff(c_11474,plain,(
    k2_xboole_0('#skF_2',k1_tarski('#skF_1')) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6498,c_11473])).

tff(c_11606,plain,(
    ~ r2_hidden('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1384,c_11474])).

tff(c_11610,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_11606])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n025.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 18:12:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.87/2.71  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.87/2.72  
% 6.87/2.72  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.87/2.72  %$ r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 6.87/2.72  
% 6.87/2.72  %Foreground sorts:
% 6.87/2.72  
% 6.87/2.72  
% 6.87/2.72  %Background operators:
% 6.87/2.72  
% 6.87/2.72  
% 6.87/2.72  %Foreground operators:
% 6.87/2.72  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.87/2.72  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.87/2.72  tff(k1_tarski, type, k1_tarski: $i > $i).
% 6.87/2.72  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 6.87/2.72  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.87/2.72  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 6.87/2.72  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 6.87/2.72  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.87/2.72  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 6.87/2.72  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 6.87/2.72  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 6.87/2.72  tff('#skF_2', type, '#skF_2': $i).
% 6.87/2.72  tff('#skF_1', type, '#skF_1': $i).
% 6.87/2.72  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.87/2.72  tff(k3_tarski, type, k3_tarski: $i > $i).
% 6.87/2.72  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.87/2.72  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 6.87/2.72  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 6.87/2.72  
% 6.87/2.74  tff(f_74, negated_conjecture, ~(![A, B]: (r2_hidden(A, B) => (k2_xboole_0(k4_xboole_0(B, k1_tarski(A)), k1_tarski(A)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t140_zfmisc_1)).
% 6.87/2.74  tff(f_47, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 6.87/2.74  tff(f_33, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 6.87/2.74  tff(f_37, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 6.87/2.74  tff(f_45, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 6.87/2.74  tff(f_43, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 6.87/2.74  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 6.87/2.74  tff(f_39, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 6.87/2.74  tff(f_67, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 6.87/2.74  tff(f_53, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_xboole_1)).
% 6.87/2.74  tff(f_55, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_xboole_1)).
% 6.87/2.74  tff(f_49, axiom, (![A, B, C]: (k3_xboole_0(A, k4_xboole_0(B, C)) = k4_xboole_0(k3_xboole_0(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_xboole_1)).
% 6.87/2.74  tff(c_46, plain, (r2_hidden('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_74])).
% 6.87/2.74  tff(c_20, plain, (![A_13]: (k4_xboole_0(A_13, k1_xboole_0)=A_13)), inference(cnfTransformation, [status(thm)], [f_47])).
% 6.87/2.74  tff(c_8, plain, (![B_4]: (r1_tarski(B_4, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 6.87/2.74  tff(c_192, plain, (![A_57, B_58]: (k4_xboole_0(A_57, B_58)=k1_xboole_0 | ~r1_tarski(A_57, B_58))), inference(cnfTransformation, [status(thm)], [f_37])).
% 6.87/2.74  tff(c_209, plain, (![B_59]: (k4_xboole_0(B_59, B_59)=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_192])).
% 6.87/2.74  tff(c_18, plain, (![A_11, B_12]: (r1_tarski(k4_xboole_0(A_11, B_12), A_11))), inference(cnfTransformation, [status(thm)], [f_45])).
% 6.87/2.74  tff(c_237, plain, (![B_60]: (r1_tarski(k1_xboole_0, B_60))), inference(superposition, [status(thm), theory('equality')], [c_209, c_18])).
% 6.87/2.74  tff(c_16, plain, (![A_9, B_10]: (k3_xboole_0(A_9, B_10)=A_9 | ~r1_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_43])).
% 6.87/2.74  tff(c_247, plain, (![B_61]: (k3_xboole_0(k1_xboole_0, B_61)=k1_xboole_0)), inference(resolution, [status(thm)], [c_237, c_16])).
% 6.87/2.74  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 6.87/2.74  tff(c_256, plain, (![B_61]: (k3_xboole_0(B_61, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_247, c_2])).
% 6.87/2.74  tff(c_340, plain, (![A_66, B_67]: (k5_xboole_0(A_66, k3_xboole_0(A_66, B_67))=k4_xboole_0(A_66, B_67))), inference(cnfTransformation, [status(thm)], [f_39])).
% 6.87/2.74  tff(c_349, plain, (![B_61]: (k5_xboole_0(B_61, k1_xboole_0)=k4_xboole_0(B_61, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_256, c_340])).
% 6.87/2.74  tff(c_364, plain, (![B_61]: (k5_xboole_0(B_61, k1_xboole_0)=B_61)), inference(demodulation, [status(thm), theory('equality')], [c_20, c_349])).
% 6.87/2.74  tff(c_40, plain, (![A_33, B_34]: (r1_tarski(k1_tarski(A_33), B_34) | ~r2_hidden(A_33, B_34))), inference(cnfTransformation, [status(thm)], [f_67])).
% 6.87/2.74  tff(c_206, plain, (![A_33, B_34]: (k4_xboole_0(k1_tarski(A_33), B_34)=k1_xboole_0 | ~r2_hidden(A_33, B_34))), inference(resolution, [status(thm)], [c_40, c_192])).
% 6.87/2.74  tff(c_358, plain, (![A_1, B_2]: (k5_xboole_0(A_1, k3_xboole_0(B_2, A_1))=k4_xboole_0(A_1, B_2))), inference(superposition, [status(thm), theory('equality')], [c_2, c_340])).
% 6.87/2.74  tff(c_26, plain, (![A_18, B_19, C_20]: (k5_xboole_0(k5_xboole_0(A_18, B_19), C_20)=k5_xboole_0(A_18, k5_xboole_0(B_19, C_20)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 6.87/2.74  tff(c_941, plain, (![A_100, B_101]: (k5_xboole_0(k5_xboole_0(A_100, B_101), k3_xboole_0(A_100, B_101))=k2_xboole_0(A_100, B_101))), inference(cnfTransformation, [status(thm)], [f_55])).
% 6.87/2.74  tff(c_972, plain, (![A_18, B_19]: (k5_xboole_0(A_18, k5_xboole_0(B_19, k3_xboole_0(A_18, B_19)))=k2_xboole_0(A_18, B_19))), inference(superposition, [status(thm), theory('equality')], [c_26, c_941])).
% 6.87/2.74  tff(c_1330, plain, (![A_115, B_116]: (k5_xboole_0(A_115, k4_xboole_0(B_116, A_115))=k2_xboole_0(A_115, B_116))), inference(demodulation, [status(thm), theory('equality')], [c_358, c_972])).
% 6.87/2.74  tff(c_1367, plain, (![B_34, A_33]: (k2_xboole_0(B_34, k1_tarski(A_33))=k5_xboole_0(B_34, k1_xboole_0) | ~r2_hidden(A_33, B_34))), inference(superposition, [status(thm), theory('equality')], [c_206, c_1330])).
% 6.87/2.74  tff(c_1384, plain, (![B_34, A_33]: (k2_xboole_0(B_34, k1_tarski(A_33))=B_34 | ~r2_hidden(A_33, B_34))), inference(demodulation, [status(thm), theory('equality')], [c_364, c_1367])).
% 6.87/2.74  tff(c_1008, plain, (![A_18, B_19]: (k5_xboole_0(A_18, k4_xboole_0(B_19, A_18))=k2_xboole_0(A_18, B_19))), inference(demodulation, [status(thm), theory('equality')], [c_358, c_972])).
% 6.87/2.74  tff(c_208, plain, (![B_4]: (k4_xboole_0(B_4, B_4)=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_192])).
% 6.87/2.74  tff(c_1373, plain, (![B_4]: (k5_xboole_0(B_4, k1_xboole_0)=k2_xboole_0(B_4, B_4))), inference(superposition, [status(thm), theory('equality')], [c_208, c_1330])).
% 6.87/2.74  tff(c_1386, plain, (![B_4]: (k2_xboole_0(B_4, B_4)=B_4)), inference(demodulation, [status(thm), theory('equality')], [c_364, c_1373])).
% 6.87/2.74  tff(c_155, plain, (![A_48, B_49]: (k3_xboole_0(A_48, B_49)=A_48 | ~r1_tarski(A_48, B_49))), inference(cnfTransformation, [status(thm)], [f_43])).
% 6.87/2.74  tff(c_163, plain, (![B_4]: (k3_xboole_0(B_4, B_4)=B_4)), inference(resolution, [status(thm)], [c_8, c_155])).
% 6.87/2.74  tff(c_355, plain, (![B_4]: (k5_xboole_0(B_4, B_4)=k4_xboole_0(B_4, B_4))), inference(superposition, [status(thm), theory('equality')], [c_163, c_340])).
% 6.87/2.74  tff(c_366, plain, (![B_4]: (k5_xboole_0(B_4, B_4)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_208, c_355])).
% 6.87/2.74  tff(c_996, plain, (![B_4]: (k5_xboole_0(k5_xboole_0(B_4, B_4), B_4)=k2_xboole_0(B_4, B_4))), inference(superposition, [status(thm), theory('equality')], [c_163, c_941])).
% 6.87/2.74  tff(c_1012, plain, (![B_4]: (k5_xboole_0(k1_xboole_0, B_4)=k2_xboole_0(B_4, B_4))), inference(demodulation, [status(thm), theory('equality')], [c_366, c_996])).
% 6.87/2.74  tff(c_1390, plain, (![B_4]: (k5_xboole_0(k1_xboole_0, B_4)=B_4)), inference(demodulation, [status(thm), theory('equality')], [c_1386, c_1012])).
% 6.87/2.74  tff(c_671, plain, (![A_89, B_90, C_91]: (k5_xboole_0(k5_xboole_0(A_89, B_90), C_91)=k5_xboole_0(A_89, k5_xboole_0(B_90, C_91)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 6.87/2.74  tff(c_716, plain, (![B_4, C_91]: (k5_xboole_0(B_4, k5_xboole_0(B_4, C_91))=k5_xboole_0(k1_xboole_0, C_91))), inference(superposition, [status(thm), theory('equality')], [c_366, c_671])).
% 6.87/2.74  tff(c_1698, plain, (![B_125, C_126]: (k5_xboole_0(B_125, k5_xboole_0(B_125, C_126))=C_126)), inference(demodulation, [status(thm), theory('equality')], [c_1390, c_716])).
% 6.87/2.74  tff(c_2650, plain, (![A_146, B_147]: (k5_xboole_0(A_146, k2_xboole_0(A_146, B_147))=k4_xboole_0(B_147, A_146))), inference(superposition, [status(thm), theory('equality')], [c_1008, c_1698])).
% 6.87/2.74  tff(c_689, plain, (![A_89, B_90]: (k5_xboole_0(A_89, k5_xboole_0(B_90, k5_xboole_0(A_89, B_90)))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_671, c_366])).
% 6.87/2.74  tff(c_1748, plain, (![B_90, A_89]: (k5_xboole_0(B_90, k5_xboole_0(A_89, B_90))=k5_xboole_0(A_89, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_689, c_1698])).
% 6.87/2.74  tff(c_1787, plain, (![B_90, A_89]: (k5_xboole_0(B_90, k5_xboole_0(A_89, B_90))=A_89)), inference(demodulation, [status(thm), theory('equality')], [c_364, c_1748])).
% 6.87/2.74  tff(c_3506, plain, (![A_164, B_165]: (k5_xboole_0(k2_xboole_0(A_164, B_165), k4_xboole_0(B_165, A_164))=A_164)), inference(superposition, [status(thm), theory('equality')], [c_2650, c_1787])).
% 6.87/2.74  tff(c_3518, plain, (![B_165, A_164]: (k5_xboole_0(k4_xboole_0(B_165, A_164), A_164)=k2_xboole_0(A_164, B_165))), inference(superposition, [status(thm), theory('equality')], [c_3506, c_1787])).
% 6.87/2.74  tff(c_2807, plain, (![A_150, B_151]: (k5_xboole_0(A_150, k4_xboole_0(A_150, B_151))=k3_xboole_0(B_151, A_150))), inference(superposition, [status(thm), theory('equality')], [c_358, c_1698])).
% 6.87/2.74  tff(c_3642, plain, (![A_168, B_169]: (k5_xboole_0(k4_xboole_0(A_168, B_169), k3_xboole_0(B_169, A_168))=A_168)), inference(superposition, [status(thm), theory('equality')], [c_2807, c_1787])).
% 6.87/2.74  tff(c_3660, plain, (![B_169, A_168]: (k5_xboole_0(k3_xboole_0(B_169, A_168), A_168)=k4_xboole_0(A_168, B_169))), inference(superposition, [status(thm), theory('equality')], [c_3642, c_1787])).
% 6.87/2.74  tff(c_14, plain, (![A_7, B_8]: (k5_xboole_0(A_7, k3_xboole_0(A_7, B_8))=k4_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_39])).
% 6.87/2.74  tff(c_6329, plain, (![A_213, B_214, C_215]: (k5_xboole_0(A_213, k5_xboole_0(k3_xboole_0(A_213, B_214), C_215))=k5_xboole_0(k4_xboole_0(A_213, B_214), C_215))), inference(superposition, [status(thm), theory('equality')], [c_14, c_671])).
% 6.87/2.74  tff(c_6385, plain, (![B_169, A_168]: (k5_xboole_0(k4_xboole_0(B_169, A_168), A_168)=k5_xboole_0(B_169, k4_xboole_0(A_168, B_169)))), inference(superposition, [status(thm), theory('equality')], [c_3660, c_6329])).
% 6.87/2.74  tff(c_6498, plain, (![B_169, A_168]: (k2_xboole_0(B_169, A_168)=k2_xboole_0(A_168, B_169))), inference(demodulation, [status(thm), theory('equality')], [c_3518, c_1008, c_6385])).
% 6.87/2.74  tff(c_246, plain, (![B_60]: (k3_xboole_0(k1_xboole_0, B_60)=k1_xboole_0)), inference(resolution, [status(thm)], [c_237, c_16])).
% 6.87/2.74  tff(c_1023, plain, (![B_103]: (k5_xboole_0(k1_xboole_0, B_103)=k2_xboole_0(B_103, B_103))), inference(demodulation, [status(thm), theory('equality')], [c_366, c_996])).
% 6.87/2.74  tff(c_28, plain, (![A_21, B_22]: (k5_xboole_0(k5_xboole_0(A_21, B_22), k3_xboole_0(A_21, B_22))=k2_xboole_0(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_55])).
% 6.87/2.74  tff(c_1032, plain, (![B_103]: (k5_xboole_0(k2_xboole_0(B_103, B_103), k3_xboole_0(k1_xboole_0, B_103))=k2_xboole_0(k1_xboole_0, B_103))), inference(superposition, [status(thm), theory('equality')], [c_1023, c_28])).
% 6.87/2.74  tff(c_1066, plain, (![B_103]: (k2_xboole_0(k1_xboole_0, B_103)=k2_xboole_0(B_103, B_103))), inference(demodulation, [status(thm), theory('equality')], [c_364, c_246, c_1032])).
% 6.87/2.74  tff(c_1389, plain, (![B_103]: (k2_xboole_0(k1_xboole_0, B_103)=B_103)), inference(demodulation, [status(thm), theory('equality')], [c_1386, c_1066])).
% 6.87/2.74  tff(c_788, plain, (![A_95, B_96, C_97]: (k4_xboole_0(k3_xboole_0(A_95, B_96), C_97)=k3_xboole_0(A_95, k4_xboole_0(B_96, C_97)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 6.87/2.74  tff(c_839, plain, (![B_2, A_1, C_97]: (k4_xboole_0(k3_xboole_0(B_2, A_1), C_97)=k3_xboole_0(A_1, k4_xboole_0(B_2, C_97)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_788])).
% 6.87/2.74  tff(c_1697, plain, (![B_4, C_91]: (k5_xboole_0(B_4, k5_xboole_0(B_4, C_91))=C_91)), inference(demodulation, [status(thm), theory('equality')], [c_1390, c_716])).
% 6.87/2.74  tff(c_3663, plain, (![A_168, B_169]: (k5_xboole_0(k4_xboole_0(A_168, B_169), A_168)=k3_xboole_0(B_169, A_168))), inference(superposition, [status(thm), theory('equality')], [c_3642, c_1697])).
% 6.87/2.74  tff(c_162, plain, (![A_11, B_12]: (k3_xboole_0(k4_xboole_0(A_11, B_12), A_11)=k4_xboole_0(A_11, B_12))), inference(resolution, [status(thm)], [c_18, c_155])).
% 6.87/2.74  tff(c_4220, plain, (![B_178, A_179]: (k5_xboole_0(k3_xboole_0(B_178, A_179), A_179)=k4_xboole_0(A_179, B_178))), inference(superposition, [status(thm), theory('equality')], [c_3642, c_1787])).
% 6.87/2.74  tff(c_4283, plain, (![A_11, B_12]: (k5_xboole_0(k4_xboole_0(A_11, B_12), A_11)=k4_xboole_0(A_11, k4_xboole_0(A_11, B_12)))), inference(superposition, [status(thm), theory('equality')], [c_162, c_4220])).
% 6.87/2.74  tff(c_5192, plain, (![A_195, B_196]: (k4_xboole_0(A_195, k4_xboole_0(A_195, B_196))=k3_xboole_0(B_196, A_195))), inference(demodulation, [status(thm), theory('equality')], [c_3663, c_4283])).
% 6.87/2.74  tff(c_207, plain, (![A_11, B_12]: (k4_xboole_0(k4_xboole_0(A_11, B_12), A_11)=k1_xboole_0)), inference(resolution, [status(thm)], [c_18, c_192])).
% 6.87/2.74  tff(c_5619, plain, (![B_203, A_204]: (k4_xboole_0(k3_xboole_0(B_203, A_204), A_204)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_5192, c_207])).
% 6.87/2.74  tff(c_5703, plain, (![C_97, B_2]: (k3_xboole_0(C_97, k4_xboole_0(B_2, C_97))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_839, c_5619])).
% 6.87/2.74  tff(c_1794, plain, (![B_127, A_128]: (k5_xboole_0(B_127, k5_xboole_0(A_128, B_127))=A_128)), inference(demodulation, [status(thm), theory('equality')], [c_364, c_1748])).
% 6.87/2.74  tff(c_1866, plain, (![A_7, B_8]: (k5_xboole_0(k3_xboole_0(A_7, B_8), k4_xboole_0(A_7, B_8))=A_7)), inference(superposition, [status(thm), theory('equality')], [c_14, c_1794])).
% 6.87/2.74  tff(c_7365, plain, (![A_226, B_227, C_228]: (k5_xboole_0(k5_xboole_0(A_226, B_227), k5_xboole_0(k3_xboole_0(A_226, B_227), C_228))=k5_xboole_0(k2_xboole_0(A_226, B_227), C_228))), inference(superposition, [status(thm), theory('equality')], [c_941, c_26])).
% 6.87/2.74  tff(c_7475, plain, (![A_7, B_8]: (k5_xboole_0(k2_xboole_0(A_7, B_8), k4_xboole_0(A_7, B_8))=k5_xboole_0(k5_xboole_0(A_7, B_8), A_7))), inference(superposition, [status(thm), theory('equality')], [c_1866, c_7365])).
% 6.87/2.74  tff(c_7672, plain, (![A_229, B_230]: (k5_xboole_0(k2_xboole_0(A_229, B_230), k4_xboole_0(A_229, B_230))=B_230)), inference(demodulation, [status(thm), theory('equality')], [c_1787, c_26, c_7475])).
% 6.87/2.74  tff(c_1830, plain, (![B_4, C_91]: (k5_xboole_0(k5_xboole_0(B_4, C_91), C_91)=B_4)), inference(superposition, [status(thm), theory('equality')], [c_1697, c_1794])).
% 6.87/2.74  tff(c_7688, plain, (![B_230, A_229]: (k5_xboole_0(B_230, k4_xboole_0(A_229, B_230))=k2_xboole_0(A_229, B_230))), inference(superposition, [status(thm), theory('equality')], [c_7672, c_1830])).
% 6.87/2.74  tff(c_944, plain, (![A_100, B_101]: (k5_xboole_0(k2_xboole_0(A_100, B_101), k3_xboole_0(k5_xboole_0(A_100, B_101), k3_xboole_0(A_100, B_101)))=k2_xboole_0(k5_xboole_0(A_100, B_101), k3_xboole_0(A_100, B_101)))), inference(superposition, [status(thm), theory('equality')], [c_941, c_28])).
% 6.87/2.74  tff(c_1003, plain, (![A_100, B_101]: (k5_xboole_0(k2_xboole_0(A_100, B_101), k3_xboole_0(k3_xboole_0(A_100, B_101), k5_xboole_0(A_100, B_101)))=k2_xboole_0(k5_xboole_0(A_100, B_101), k3_xboole_0(A_100, B_101)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_944])).
% 6.87/2.74  tff(c_10657, plain, (![A_259, B_260]: (k5_xboole_0(k2_xboole_0(A_259, B_260), k3_xboole_0(k3_xboole_0(A_259, B_260), k5_xboole_0(A_259, B_260)))=k2_xboole_0(k3_xboole_0(A_259, B_260), k5_xboole_0(A_259, B_260)))), inference(demodulation, [status(thm), theory('equality')], [c_6498, c_1003])).
% 6.87/2.74  tff(c_10729, plain, (![B_230, A_229]: (k5_xboole_0(k2_xboole_0(B_230, k4_xboole_0(A_229, B_230)), k3_xboole_0(k3_xboole_0(B_230, k4_xboole_0(A_229, B_230)), k2_xboole_0(A_229, B_230)))=k2_xboole_0(k3_xboole_0(B_230, k4_xboole_0(A_229, B_230)), k5_xboole_0(B_230, k4_xboole_0(A_229, B_230))))), inference(superposition, [status(thm), theory('equality')], [c_7688, c_10657])).
% 6.87/2.74  tff(c_10922, plain, (![B_230, A_229]: (k2_xboole_0(B_230, k4_xboole_0(A_229, B_230))=k2_xboole_0(B_230, A_229))), inference(demodulation, [status(thm), theory('equality')], [c_1389, c_5703, c_364, c_246, c_2, c_5703, c_1008, c_2, c_10729])).
% 6.87/2.74  tff(c_44, plain, (k2_xboole_0(k4_xboole_0('#skF_2', k1_tarski('#skF_1')), k1_tarski('#skF_1'))!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_74])).
% 6.87/2.74  tff(c_6518, plain, (k2_xboole_0(k1_tarski('#skF_1'), k4_xboole_0('#skF_2', k1_tarski('#skF_1')))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_6498, c_44])).
% 6.87/2.74  tff(c_11473, plain, (k2_xboole_0(k1_tarski('#skF_1'), '#skF_2')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_10922, c_6518])).
% 6.87/2.74  tff(c_11474, plain, (k2_xboole_0('#skF_2', k1_tarski('#skF_1'))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_6498, c_11473])).
% 6.87/2.74  tff(c_11606, plain, (~r2_hidden('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1384, c_11474])).
% 6.87/2.74  tff(c_11610, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_46, c_11606])).
% 6.87/2.74  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.87/2.74  
% 6.87/2.74  Inference rules
% 6.87/2.74  ----------------------
% 6.87/2.74  #Ref     : 0
% 6.87/2.74  #Sup     : 2849
% 6.87/2.74  #Fact    : 0
% 6.87/2.74  #Define  : 0
% 6.87/2.74  #Split   : 1
% 6.87/2.74  #Chain   : 0
% 6.87/2.74  #Close   : 0
% 6.87/2.74  
% 6.87/2.74  Ordering : KBO
% 6.87/2.74  
% 6.87/2.74  Simplification rules
% 6.87/2.74  ----------------------
% 6.87/2.74  #Subsume      : 108
% 6.87/2.74  #Demod        : 3659
% 6.87/2.74  #Tautology    : 1686
% 6.87/2.74  #SimpNegUnit  : 0
% 6.87/2.74  #BackRed      : 17
% 6.87/2.74  
% 6.87/2.74  #Partial instantiations: 0
% 6.87/2.74  #Strategies tried      : 1
% 6.87/2.74  
% 6.87/2.74  Timing (in seconds)
% 6.87/2.74  ----------------------
% 6.87/2.75  Preprocessing        : 0.31
% 6.87/2.75  Parsing              : 0.16
% 6.87/2.75  CNF conversion       : 0.02
% 6.87/2.75  Main loop            : 1.66
% 6.87/2.75  Inferencing          : 0.42
% 6.87/2.75  Reduction            : 0.89
% 6.87/2.75  Demodulation         : 0.79
% 6.87/2.75  BG Simplification    : 0.05
% 6.87/2.75  Subsumption          : 0.21
% 6.87/2.75  Abstraction          : 0.09
% 6.87/2.75  MUC search           : 0.00
% 6.87/2.75  Cooper               : 0.00
% 6.87/2.75  Total                : 2.01
% 6.87/2.75  Index Insertion      : 0.00
% 6.87/2.75  Index Deletion       : 0.00
% 6.87/2.75  Index Matching       : 0.00
% 6.87/2.75  BG Taut test         : 0.00
%------------------------------------------------------------------------------

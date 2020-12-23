%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:45:12 EST 2020

% Result     : Theorem 6.24s
% Output     : CNFRefutation 6.59s
% Verified   : 
% Statistics : Number of formulae       :  105 ( 170 expanded)
%              Number of leaves         :   36 (  68 expanded)
%              Depth                    :   15
%              Number of atoms          :  118 ( 216 expanded)
%              Number of equality atoms :   64 ( 106 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_xboole_0 > r1_xboole_0 > r1_tarski > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > o_0_0_xboole_0 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(o_0_0_xboole_0,type,(
    o_0_0_xboole_0: $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(r2_xboole_0,type,(
    r2_xboole_0: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_49,axiom,(
    ? [A] : v1_xboole_0(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc1_xboole_0)).

tff(f_47,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_34,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_57,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_133,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_tarski(A,k4_xboole_0(B,C))
       => ( r1_tarski(A,B)
          & r1_xboole_0(A,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_53,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_67,axiom,(
    ! [A,B] : k3_xboole_0(A,k2_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_xboole_1)).

tff(f_126,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_83,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_122,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_120,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_59,axiom,(
    ! [A,B] : r1_xboole_0(k3_xboole_0(A,B),k5_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l97_xboole_1)).

tff(f_114,axiom,(
    ! [A,B,C] :
      ~ ( ~ r1_xboole_0(A,B)
        & r1_xboole_0(A,C)
        & r1_xboole_0(A,k4_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t84_xboole_1)).

tff(f_79,axiom,(
    ! [A,B,C] : k3_xboole_0(A,k4_xboole_0(B,C)) = k4_xboole_0(k3_xboole_0(A,B),C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).

tff(f_65,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_75,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_22,plain,(
    v1_xboole_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_134,plain,(
    ! [A_68] :
      ( k1_xboole_0 = A_68
      | ~ v1_xboole_0(A_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_138,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_22,c_134])).

tff(c_10,plain,(
    ! [A_5,B_6] :
      ( r1_xboole_0(A_5,B_6)
      | k3_xboole_0(A_5,B_6) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_6750,plain,(
    ! [A_263,B_264] :
      ( r1_xboole_0(A_263,B_264)
      | k3_xboole_0(A_263,B_264) != '#skF_1' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_138,c_10])).

tff(c_26,plain,(
    ! [A_14,B_15] :
      ( r1_tarski(A_14,B_15)
      | k4_xboole_0(A_14,B_15) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_562,plain,(
    ! [A_102,B_103] :
      ( r1_tarski(A_102,B_103)
      | k4_xboole_0(A_102,B_103) != '#skF_1' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_138,c_26])).

tff(c_74,plain,
    ( ~ r1_xboole_0('#skF_2','#skF_4')
    | ~ r1_tarski('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_216,plain,(
    ~ r1_tarski('#skF_2','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_74])).

tff(c_566,plain,(
    k4_xboole_0('#skF_2','#skF_3') != '#skF_1' ),
    inference(resolution,[status(thm)],[c_562,c_216])).

tff(c_18,plain,(
    ! [A_9] : k3_xboole_0(A_9,A_9) = A_9 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_909,plain,(
    ! [A_122,B_123] :
      ( r1_xboole_0(A_122,B_123)
      | k3_xboole_0(A_122,B_123) != '#skF_1' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_138,c_10])).

tff(c_24,plain,(
    ! [B_13,A_12] :
      ( r1_xboole_0(B_13,A_12)
      | ~ r1_xboole_0(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_920,plain,(
    ! [B_123,A_122] :
      ( r1_xboole_0(B_123,A_122)
      | k3_xboole_0(A_122,B_123) != '#skF_1' ) ),
    inference(resolution,[status(thm)],[c_909,c_24])).

tff(c_38,plain,(
    ! [A_25,B_26] : k3_xboole_0(A_25,k2_xboole_0(A_25,B_26)) = A_25 ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_72,plain,(
    ! [A_61,B_62] : k5_xboole_0(A_61,k4_xboole_0(B_62,A_61)) = k2_xboole_0(A_61,B_62) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_224,plain,(
    ! [B_80,A_81] : k5_xboole_0(B_80,A_81) = k5_xboole_0(A_81,B_80) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_52,plain,(
    ! [A_42] : k5_xboole_0(A_42,k1_xboole_0) = A_42 ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_140,plain,(
    ! [A_42] : k5_xboole_0(A_42,'#skF_1') = A_42 ),
    inference(demodulation,[status(thm),theory(equality)],[c_138,c_52])).

tff(c_240,plain,(
    ! [A_81] : k5_xboole_0('#skF_1',A_81) = A_81 ),
    inference(superposition,[status(thm),theory(equality)],[c_224,c_140])).

tff(c_68,plain,(
    ! [A_58] : k5_xboole_0(A_58,A_58) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_141,plain,(
    ! [A_58] : k5_xboole_0(A_58,A_58) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_138,c_68])).

tff(c_2083,plain,(
    ! [A_164,B_165,C_166] : k5_xboole_0(k5_xboole_0(A_164,B_165),C_166) = k5_xboole_0(A_164,k5_xboole_0(B_165,C_166)) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_2177,plain,(
    ! [A_58,C_166] : k5_xboole_0(A_58,k5_xboole_0(A_58,C_166)) = k5_xboole_0('#skF_1',C_166) ),
    inference(superposition,[status(thm),theory(equality)],[c_141,c_2083])).

tff(c_2229,plain,(
    ! [A_168,C_169] : k5_xboole_0(A_168,k5_xboole_0(A_168,C_169)) = C_169 ),
    inference(demodulation,[status(thm),theory(equality)],[c_240,c_2177])).

tff(c_4,plain,(
    ! [B_4,A_3] : k5_xboole_0(B_4,A_3) = k5_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_475,plain,(
    ! [A_96,B_97] : r1_xboole_0(k3_xboole_0(A_96,B_97),k5_xboole_0(A_96,B_97)) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_498,plain,(
    ! [B_4,A_3] : r1_xboole_0(k3_xboole_0(B_4,A_3),k5_xboole_0(A_3,B_4)) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_475])).

tff(c_2251,plain,(
    ! [A_168,C_169] : r1_xboole_0(k3_xboole_0(k5_xboole_0(A_168,C_169),A_168),C_169) ),
    inference(superposition,[status(thm),theory(equality)],[c_2229,c_498])).

tff(c_3172,plain,(
    ! [A_190,C_191] : r1_xboole_0(k3_xboole_0(A_190,k5_xboole_0(A_190,C_191)),C_191) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_2251])).

tff(c_3205,plain,(
    ! [A_61,B_62] : r1_xboole_0(k3_xboole_0(A_61,k2_xboole_0(A_61,B_62)),k4_xboole_0(B_62,A_61)) ),
    inference(superposition,[status(thm),theory(equality)],[c_72,c_3172])).

tff(c_3231,plain,(
    ! [A_61,B_62] : r1_xboole_0(A_61,k4_xboole_0(B_62,A_61)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_3205])).

tff(c_3921,plain,(
    ! [A_206,B_207,C_208] :
      ( ~ r1_xboole_0(A_206,k4_xboole_0(B_207,C_208))
      | ~ r1_xboole_0(A_206,C_208)
      | r1_xboole_0(A_206,B_207) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_4883,plain,(
    ! [A_221,B_222] :
      ( ~ r1_xboole_0(A_221,A_221)
      | r1_xboole_0(A_221,B_222) ) ),
    inference(resolution,[status(thm)],[c_3231,c_3921])).

tff(c_4898,plain,(
    ! [A_122,B_222] :
      ( r1_xboole_0(A_122,B_222)
      | k3_xboole_0(A_122,A_122) != '#skF_1' ) ),
    inference(resolution,[status(thm)],[c_920,c_4883])).

tff(c_4922,plain,(
    ! [A_223,B_224] :
      ( r1_xboole_0(A_223,B_224)
      | A_223 != '#skF_1' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_4898])).

tff(c_8,plain,(
    ! [A_5,B_6] :
      ( k3_xboole_0(A_5,B_6) = k1_xboole_0
      | ~ r1_xboole_0(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_542,plain,(
    ! [A_5,B_6] :
      ( k3_xboole_0(A_5,B_6) = '#skF_1'
      | ~ r1_xboole_0(A_5,B_6) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_138,c_8])).

tff(c_5165,plain,(
    ! [B_224] : k3_xboole_0('#skF_1',B_224) = '#skF_1' ),
    inference(resolution,[status(thm)],[c_4922,c_542])).

tff(c_3272,plain,(
    ! [A_194,B_195,C_196] : k4_xboole_0(k3_xboole_0(A_194,B_195),C_196) = k3_xboole_0(A_194,k4_xboole_0(B_195,C_196)) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_6198,plain,(
    ! [A_238,C_239] : k3_xboole_0(A_238,k4_xboole_0(A_238,C_239)) = k4_xboole_0(A_238,C_239) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_3272])).

tff(c_36,plain,(
    ! [A_23,B_24] : r1_tarski(k3_xboole_0(A_23,B_24),A_23) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_28,plain,(
    ! [A_14,B_15] :
      ( k4_xboole_0(A_14,B_15) = k1_xboole_0
      | ~ r1_tarski(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_674,plain,(
    ! [A_112,B_113] :
      ( k4_xboole_0(A_112,B_113) = '#skF_1'
      | ~ r1_tarski(A_112,B_113) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_138,c_28])).

tff(c_714,plain,(
    ! [A_23,B_24] : k4_xboole_0(k3_xboole_0(A_23,B_24),A_23) = '#skF_1' ),
    inference(resolution,[status(thm)],[c_36,c_674])).

tff(c_6437,plain,(
    ! [A_242,C_243] : k4_xboole_0(k4_xboole_0(A_242,C_243),A_242) = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_6198,c_714])).

tff(c_76,plain,(
    r1_tarski('#skF_2',k4_xboole_0('#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_586,plain,(
    ! [A_109,B_110] :
      ( k3_xboole_0(A_109,B_110) = A_109
      | ~ r1_tarski(A_109,B_110) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_634,plain,(
    k3_xboole_0('#skF_2',k4_xboole_0('#skF_3','#skF_4')) = '#skF_2' ),
    inference(resolution,[status(thm)],[c_76,c_586])).

tff(c_3346,plain,(
    ! [C_196] : k3_xboole_0('#skF_2',k4_xboole_0(k4_xboole_0('#skF_3','#skF_4'),C_196)) = k4_xboole_0('#skF_2',C_196) ),
    inference(superposition,[status(thm),theory(equality)],[c_634,c_3272])).

tff(c_6452,plain,(
    k4_xboole_0('#skF_2','#skF_3') = k3_xboole_0('#skF_2','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_6437,c_3346])).

tff(c_6536,plain,(
    k4_xboole_0('#skF_2','#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5165,c_2,c_6452])).

tff(c_6538,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_566,c_6536])).

tff(c_6539,plain,(
    ~ r1_xboole_0('#skF_2','#skF_4') ),
    inference(splitRight,[status(thm)],[c_74])).

tff(c_6755,plain,(
    k3_xboole_0('#skF_2','#skF_4') != '#skF_1' ),
    inference(resolution,[status(thm)],[c_6750,c_6539])).

tff(c_6762,plain,(
    k3_xboole_0('#skF_4','#skF_2') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_6755])).

tff(c_6540,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_74])).

tff(c_6953,plain,(
    ! [A_276,B_277] :
      ( k3_xboole_0(A_276,B_277) = A_276
      | ~ r1_tarski(A_276,B_277) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_6982,plain,(
    k3_xboole_0('#skF_2','#skF_3') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_6540,c_6953])).

tff(c_9050,plain,(
    ! [A_334,B_335,C_336] : k4_xboole_0(k3_xboole_0(A_334,B_335),C_336) = k3_xboole_0(A_334,k4_xboole_0(B_335,C_336)) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_9932,plain,(
    ! [C_352] : k3_xboole_0('#skF_2',k4_xboole_0('#skF_3',C_352)) = k4_xboole_0('#skF_2',C_352) ),
    inference(superposition,[status(thm),theory(equality)],[c_6982,c_9050])).

tff(c_6984,plain,(
    k3_xboole_0('#skF_2',k4_xboole_0('#skF_3','#skF_4')) = '#skF_2' ),
    inference(resolution,[status(thm)],[c_76,c_6953])).

tff(c_9969,plain,(
    k4_xboole_0('#skF_2','#skF_4') = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_9932,c_6984])).

tff(c_6816,plain,(
    ! [A_266,B_267] :
      ( k4_xboole_0(A_266,B_267) = '#skF_1'
      | ~ r1_tarski(A_266,B_267) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_138,c_28])).

tff(c_6843,plain,(
    ! [A_23,B_24] : k4_xboole_0(k3_xboole_0(A_23,B_24),A_23) = '#skF_1' ),
    inference(resolution,[status(thm)],[c_36,c_6816])).

tff(c_9077,plain,(
    ! [C_336,B_335] : k3_xboole_0(C_336,k4_xboole_0(B_335,C_336)) = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_9050,c_6843])).

tff(c_10036,plain,(
    k3_xboole_0('#skF_4','#skF_2') = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_9969,c_9077])).

tff(c_10055,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_6762,c_10036])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n022.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 13:51:10 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.24/2.38  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.24/2.39  
% 6.24/2.39  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.24/2.39  %$ r2_xboole_0 > r1_xboole_0 > r1_tarski > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > o_0_0_xboole_0 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 6.24/2.39  
% 6.24/2.39  %Foreground sorts:
% 6.24/2.39  
% 6.24/2.39  
% 6.24/2.39  %Background operators:
% 6.24/2.39  
% 6.24/2.39  
% 6.24/2.39  %Foreground operators:
% 6.24/2.39  tff(o_0_0_xboole_0, type, o_0_0_xboole_0: $i).
% 6.24/2.39  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.24/2.39  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 6.24/2.39  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.24/2.39  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 6.24/2.39  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.24/2.39  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 6.24/2.39  tff('#skF_2', type, '#skF_2': $i).
% 6.24/2.39  tff('#skF_3', type, '#skF_3': $i).
% 6.24/2.39  tff('#skF_1', type, '#skF_1': $i).
% 6.24/2.39  tff(r2_xboole_0, type, r2_xboole_0: ($i * $i) > $o).
% 6.24/2.39  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.24/2.39  tff('#skF_4', type, '#skF_4': $i).
% 6.24/2.39  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.24/2.39  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 6.24/2.39  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 6.24/2.39  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 6.24/2.39  
% 6.59/2.41  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 6.59/2.41  tff(f_49, axiom, (?[A]: v1_xboole_0(A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', rc1_xboole_0)).
% 6.59/2.41  tff(f_47, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 6.59/2.41  tff(f_34, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 6.59/2.41  tff(f_57, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 6.59/2.41  tff(f_133, negated_conjecture, ~(![A, B, C]: (r1_tarski(A, k4_xboole_0(B, C)) => (r1_tarski(A, B) & r1_xboole_0(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t106_xboole_1)).
% 6.59/2.41  tff(f_43, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 6.59/2.41  tff(f_53, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 6.59/2.41  tff(f_67, axiom, (![A, B]: (k3_xboole_0(A, k2_xboole_0(A, B)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_xboole_1)).
% 6.59/2.41  tff(f_126, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 6.59/2.41  tff(f_29, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 6.59/2.41  tff(f_83, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 6.59/2.41  tff(f_122, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_xboole_1)).
% 6.59/2.41  tff(f_120, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_xboole_1)).
% 6.59/2.41  tff(f_59, axiom, (![A, B]: r1_xboole_0(k3_xboole_0(A, B), k5_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l97_xboole_1)).
% 6.59/2.41  tff(f_114, axiom, (![A, B, C]: ~((~r1_xboole_0(A, B) & r1_xboole_0(A, C)) & r1_xboole_0(A, k4_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t84_xboole_1)).
% 6.59/2.41  tff(f_79, axiom, (![A, B, C]: (k3_xboole_0(A, k4_xboole_0(B, C)) = k4_xboole_0(k3_xboole_0(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_xboole_1)).
% 6.59/2.41  tff(f_65, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 6.59/2.41  tff(f_75, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 6.59/2.41  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 6.59/2.41  tff(c_22, plain, (v1_xboole_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_49])).
% 6.59/2.41  tff(c_134, plain, (![A_68]: (k1_xboole_0=A_68 | ~v1_xboole_0(A_68))), inference(cnfTransformation, [status(thm)], [f_47])).
% 6.59/2.41  tff(c_138, plain, (k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_22, c_134])).
% 6.59/2.41  tff(c_10, plain, (![A_5, B_6]: (r1_xboole_0(A_5, B_6) | k3_xboole_0(A_5, B_6)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_34])).
% 6.59/2.41  tff(c_6750, plain, (![A_263, B_264]: (r1_xboole_0(A_263, B_264) | k3_xboole_0(A_263, B_264)!='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_138, c_10])).
% 6.59/2.41  tff(c_26, plain, (![A_14, B_15]: (r1_tarski(A_14, B_15) | k4_xboole_0(A_14, B_15)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_57])).
% 6.59/2.41  tff(c_562, plain, (![A_102, B_103]: (r1_tarski(A_102, B_103) | k4_xboole_0(A_102, B_103)!='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_138, c_26])).
% 6.59/2.41  tff(c_74, plain, (~r1_xboole_0('#skF_2', '#skF_4') | ~r1_tarski('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_133])).
% 6.59/2.41  tff(c_216, plain, (~r1_tarski('#skF_2', '#skF_3')), inference(splitLeft, [status(thm)], [c_74])).
% 6.59/2.41  tff(c_566, plain, (k4_xboole_0('#skF_2', '#skF_3')!='#skF_1'), inference(resolution, [status(thm)], [c_562, c_216])).
% 6.59/2.41  tff(c_18, plain, (![A_9]: (k3_xboole_0(A_9, A_9)=A_9)), inference(cnfTransformation, [status(thm)], [f_43])).
% 6.59/2.41  tff(c_909, plain, (![A_122, B_123]: (r1_xboole_0(A_122, B_123) | k3_xboole_0(A_122, B_123)!='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_138, c_10])).
% 6.59/2.41  tff(c_24, plain, (![B_13, A_12]: (r1_xboole_0(B_13, A_12) | ~r1_xboole_0(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_53])).
% 6.59/2.41  tff(c_920, plain, (![B_123, A_122]: (r1_xboole_0(B_123, A_122) | k3_xboole_0(A_122, B_123)!='#skF_1')), inference(resolution, [status(thm)], [c_909, c_24])).
% 6.59/2.41  tff(c_38, plain, (![A_25, B_26]: (k3_xboole_0(A_25, k2_xboole_0(A_25, B_26))=A_25)), inference(cnfTransformation, [status(thm)], [f_67])).
% 6.59/2.41  tff(c_72, plain, (![A_61, B_62]: (k5_xboole_0(A_61, k4_xboole_0(B_62, A_61))=k2_xboole_0(A_61, B_62))), inference(cnfTransformation, [status(thm)], [f_126])).
% 6.59/2.41  tff(c_224, plain, (![B_80, A_81]: (k5_xboole_0(B_80, A_81)=k5_xboole_0(A_81, B_80))), inference(cnfTransformation, [status(thm)], [f_29])).
% 6.59/2.41  tff(c_52, plain, (![A_42]: (k5_xboole_0(A_42, k1_xboole_0)=A_42)), inference(cnfTransformation, [status(thm)], [f_83])).
% 6.59/2.41  tff(c_140, plain, (![A_42]: (k5_xboole_0(A_42, '#skF_1')=A_42)), inference(demodulation, [status(thm), theory('equality')], [c_138, c_52])).
% 6.59/2.41  tff(c_240, plain, (![A_81]: (k5_xboole_0('#skF_1', A_81)=A_81)), inference(superposition, [status(thm), theory('equality')], [c_224, c_140])).
% 6.59/2.41  tff(c_68, plain, (![A_58]: (k5_xboole_0(A_58, A_58)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_122])).
% 6.59/2.41  tff(c_141, plain, (![A_58]: (k5_xboole_0(A_58, A_58)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_138, c_68])).
% 6.59/2.41  tff(c_2083, plain, (![A_164, B_165, C_166]: (k5_xboole_0(k5_xboole_0(A_164, B_165), C_166)=k5_xboole_0(A_164, k5_xboole_0(B_165, C_166)))), inference(cnfTransformation, [status(thm)], [f_120])).
% 6.59/2.41  tff(c_2177, plain, (![A_58, C_166]: (k5_xboole_0(A_58, k5_xboole_0(A_58, C_166))=k5_xboole_0('#skF_1', C_166))), inference(superposition, [status(thm), theory('equality')], [c_141, c_2083])).
% 6.59/2.41  tff(c_2229, plain, (![A_168, C_169]: (k5_xboole_0(A_168, k5_xboole_0(A_168, C_169))=C_169)), inference(demodulation, [status(thm), theory('equality')], [c_240, c_2177])).
% 6.59/2.41  tff(c_4, plain, (![B_4, A_3]: (k5_xboole_0(B_4, A_3)=k5_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 6.59/2.41  tff(c_475, plain, (![A_96, B_97]: (r1_xboole_0(k3_xboole_0(A_96, B_97), k5_xboole_0(A_96, B_97)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 6.59/2.41  tff(c_498, plain, (![B_4, A_3]: (r1_xboole_0(k3_xboole_0(B_4, A_3), k5_xboole_0(A_3, B_4)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_475])).
% 6.59/2.41  tff(c_2251, plain, (![A_168, C_169]: (r1_xboole_0(k3_xboole_0(k5_xboole_0(A_168, C_169), A_168), C_169))), inference(superposition, [status(thm), theory('equality')], [c_2229, c_498])).
% 6.59/2.41  tff(c_3172, plain, (![A_190, C_191]: (r1_xboole_0(k3_xboole_0(A_190, k5_xboole_0(A_190, C_191)), C_191))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_2251])).
% 6.59/2.41  tff(c_3205, plain, (![A_61, B_62]: (r1_xboole_0(k3_xboole_0(A_61, k2_xboole_0(A_61, B_62)), k4_xboole_0(B_62, A_61)))), inference(superposition, [status(thm), theory('equality')], [c_72, c_3172])).
% 6.59/2.41  tff(c_3231, plain, (![A_61, B_62]: (r1_xboole_0(A_61, k4_xboole_0(B_62, A_61)))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_3205])).
% 6.59/2.41  tff(c_3921, plain, (![A_206, B_207, C_208]: (~r1_xboole_0(A_206, k4_xboole_0(B_207, C_208)) | ~r1_xboole_0(A_206, C_208) | r1_xboole_0(A_206, B_207))), inference(cnfTransformation, [status(thm)], [f_114])).
% 6.59/2.41  tff(c_4883, plain, (![A_221, B_222]: (~r1_xboole_0(A_221, A_221) | r1_xboole_0(A_221, B_222))), inference(resolution, [status(thm)], [c_3231, c_3921])).
% 6.59/2.41  tff(c_4898, plain, (![A_122, B_222]: (r1_xboole_0(A_122, B_222) | k3_xboole_0(A_122, A_122)!='#skF_1')), inference(resolution, [status(thm)], [c_920, c_4883])).
% 6.59/2.41  tff(c_4922, plain, (![A_223, B_224]: (r1_xboole_0(A_223, B_224) | A_223!='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_18, c_4898])).
% 6.59/2.41  tff(c_8, plain, (![A_5, B_6]: (k3_xboole_0(A_5, B_6)=k1_xboole_0 | ~r1_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_34])).
% 6.59/2.41  tff(c_542, plain, (![A_5, B_6]: (k3_xboole_0(A_5, B_6)='#skF_1' | ~r1_xboole_0(A_5, B_6))), inference(demodulation, [status(thm), theory('equality')], [c_138, c_8])).
% 6.59/2.41  tff(c_5165, plain, (![B_224]: (k3_xboole_0('#skF_1', B_224)='#skF_1')), inference(resolution, [status(thm)], [c_4922, c_542])).
% 6.59/2.41  tff(c_3272, plain, (![A_194, B_195, C_196]: (k4_xboole_0(k3_xboole_0(A_194, B_195), C_196)=k3_xboole_0(A_194, k4_xboole_0(B_195, C_196)))), inference(cnfTransformation, [status(thm)], [f_79])).
% 6.59/2.41  tff(c_6198, plain, (![A_238, C_239]: (k3_xboole_0(A_238, k4_xboole_0(A_238, C_239))=k4_xboole_0(A_238, C_239))), inference(superposition, [status(thm), theory('equality')], [c_18, c_3272])).
% 6.59/2.41  tff(c_36, plain, (![A_23, B_24]: (r1_tarski(k3_xboole_0(A_23, B_24), A_23))), inference(cnfTransformation, [status(thm)], [f_65])).
% 6.59/2.41  tff(c_28, plain, (![A_14, B_15]: (k4_xboole_0(A_14, B_15)=k1_xboole_0 | ~r1_tarski(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_57])).
% 6.59/2.41  tff(c_674, plain, (![A_112, B_113]: (k4_xboole_0(A_112, B_113)='#skF_1' | ~r1_tarski(A_112, B_113))), inference(demodulation, [status(thm), theory('equality')], [c_138, c_28])).
% 6.59/2.41  tff(c_714, plain, (![A_23, B_24]: (k4_xboole_0(k3_xboole_0(A_23, B_24), A_23)='#skF_1')), inference(resolution, [status(thm)], [c_36, c_674])).
% 6.59/2.41  tff(c_6437, plain, (![A_242, C_243]: (k4_xboole_0(k4_xboole_0(A_242, C_243), A_242)='#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_6198, c_714])).
% 6.59/2.41  tff(c_76, plain, (r1_tarski('#skF_2', k4_xboole_0('#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_133])).
% 6.59/2.41  tff(c_586, plain, (![A_109, B_110]: (k3_xboole_0(A_109, B_110)=A_109 | ~r1_tarski(A_109, B_110))), inference(cnfTransformation, [status(thm)], [f_75])).
% 6.59/2.41  tff(c_634, plain, (k3_xboole_0('#skF_2', k4_xboole_0('#skF_3', '#skF_4'))='#skF_2'), inference(resolution, [status(thm)], [c_76, c_586])).
% 6.59/2.41  tff(c_3346, plain, (![C_196]: (k3_xboole_0('#skF_2', k4_xboole_0(k4_xboole_0('#skF_3', '#skF_4'), C_196))=k4_xboole_0('#skF_2', C_196))), inference(superposition, [status(thm), theory('equality')], [c_634, c_3272])).
% 6.59/2.41  tff(c_6452, plain, (k4_xboole_0('#skF_2', '#skF_3')=k3_xboole_0('#skF_2', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_6437, c_3346])).
% 6.59/2.41  tff(c_6536, plain, (k4_xboole_0('#skF_2', '#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_5165, c_2, c_6452])).
% 6.59/2.41  tff(c_6538, plain, $false, inference(negUnitSimplification, [status(thm)], [c_566, c_6536])).
% 6.59/2.41  tff(c_6539, plain, (~r1_xboole_0('#skF_2', '#skF_4')), inference(splitRight, [status(thm)], [c_74])).
% 6.59/2.41  tff(c_6755, plain, (k3_xboole_0('#skF_2', '#skF_4')!='#skF_1'), inference(resolution, [status(thm)], [c_6750, c_6539])).
% 6.59/2.41  tff(c_6762, plain, (k3_xboole_0('#skF_4', '#skF_2')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_2, c_6755])).
% 6.59/2.41  tff(c_6540, plain, (r1_tarski('#skF_2', '#skF_3')), inference(splitRight, [status(thm)], [c_74])).
% 6.59/2.41  tff(c_6953, plain, (![A_276, B_277]: (k3_xboole_0(A_276, B_277)=A_276 | ~r1_tarski(A_276, B_277))), inference(cnfTransformation, [status(thm)], [f_75])).
% 6.59/2.41  tff(c_6982, plain, (k3_xboole_0('#skF_2', '#skF_3')='#skF_2'), inference(resolution, [status(thm)], [c_6540, c_6953])).
% 6.59/2.41  tff(c_9050, plain, (![A_334, B_335, C_336]: (k4_xboole_0(k3_xboole_0(A_334, B_335), C_336)=k3_xboole_0(A_334, k4_xboole_0(B_335, C_336)))), inference(cnfTransformation, [status(thm)], [f_79])).
% 6.59/2.41  tff(c_9932, plain, (![C_352]: (k3_xboole_0('#skF_2', k4_xboole_0('#skF_3', C_352))=k4_xboole_0('#skF_2', C_352))), inference(superposition, [status(thm), theory('equality')], [c_6982, c_9050])).
% 6.59/2.41  tff(c_6984, plain, (k3_xboole_0('#skF_2', k4_xboole_0('#skF_3', '#skF_4'))='#skF_2'), inference(resolution, [status(thm)], [c_76, c_6953])).
% 6.59/2.41  tff(c_9969, plain, (k4_xboole_0('#skF_2', '#skF_4')='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_9932, c_6984])).
% 6.59/2.41  tff(c_6816, plain, (![A_266, B_267]: (k4_xboole_0(A_266, B_267)='#skF_1' | ~r1_tarski(A_266, B_267))), inference(demodulation, [status(thm), theory('equality')], [c_138, c_28])).
% 6.59/2.41  tff(c_6843, plain, (![A_23, B_24]: (k4_xboole_0(k3_xboole_0(A_23, B_24), A_23)='#skF_1')), inference(resolution, [status(thm)], [c_36, c_6816])).
% 6.59/2.41  tff(c_9077, plain, (![C_336, B_335]: (k3_xboole_0(C_336, k4_xboole_0(B_335, C_336))='#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_9050, c_6843])).
% 6.59/2.41  tff(c_10036, plain, (k3_xboole_0('#skF_4', '#skF_2')='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_9969, c_9077])).
% 6.59/2.41  tff(c_10055, plain, $false, inference(negUnitSimplification, [status(thm)], [c_6762, c_10036])).
% 6.59/2.41  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.59/2.41  
% 6.59/2.41  Inference rules
% 6.59/2.41  ----------------------
% 6.59/2.41  #Ref     : 0
% 6.59/2.41  #Sup     : 2508
% 6.59/2.41  #Fact    : 0
% 6.59/2.41  #Define  : 0
% 6.59/2.41  #Split   : 4
% 6.59/2.41  #Chain   : 0
% 6.59/2.41  #Close   : 0
% 6.59/2.41  
% 6.59/2.41  Ordering : KBO
% 6.59/2.41  
% 6.59/2.41  Simplification rules
% 6.59/2.41  ----------------------
% 6.59/2.41  #Subsume      : 37
% 6.59/2.41  #Demod        : 1834
% 6.59/2.41  #Tautology    : 1620
% 6.59/2.41  #SimpNegUnit  : 2
% 6.59/2.41  #BackRed      : 20
% 6.59/2.41  
% 6.59/2.41  #Partial instantiations: 0
% 6.59/2.41  #Strategies tried      : 1
% 6.59/2.41  
% 6.59/2.41  Timing (in seconds)
% 6.59/2.41  ----------------------
% 6.59/2.42  Preprocessing        : 0.35
% 6.59/2.42  Parsing              : 0.19
% 6.59/2.42  CNF conversion       : 0.02
% 6.59/2.42  Main loop            : 1.26
% 6.59/2.42  Inferencing          : 0.35
% 6.59/2.42  Reduction            : 0.58
% 6.59/2.42  Demodulation         : 0.46
% 6.59/2.42  BG Simplification    : 0.04
% 6.59/2.42  Subsumption          : 0.20
% 6.59/2.42  Abstraction          : 0.05
% 6.59/2.42  MUC search           : 0.00
% 6.59/2.42  Cooper               : 0.00
% 6.59/2.42  Total                : 1.65
% 6.59/2.42  Index Insertion      : 0.00
% 6.59/2.42  Index Deletion       : 0.00
% 6.59/2.42  Index Matching       : 0.00
% 6.59/2.42  BG Taut test         : 0.00
%------------------------------------------------------------------------------

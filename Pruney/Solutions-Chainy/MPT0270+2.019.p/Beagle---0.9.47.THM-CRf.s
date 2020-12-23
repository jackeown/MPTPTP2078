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
% DateTime   : Thu Dec  3 09:52:55 EST 2020

% Result     : Theorem 11.59s
% Output     : CNFRefutation 11.59s
% Verified   : 
% Statistics : Number of formulae       :  132 ( 389 expanded)
%              Number of leaves         :   38 ( 145 expanded)
%              Depth                    :   17
%              Number of atoms          :  139 ( 511 expanded)
%              Number of equality atoms :   75 ( 257 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_2',type,(
    '#skF_2': $i > $i )).

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

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

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

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_99,negated_conjecture,(
    ~ ! [A,B] :
        ( k4_xboole_0(k1_tarski(A),B) = k1_tarski(A)
      <=> ~ r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_zfmisc_1)).

tff(f_65,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_86,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_53,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_45,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_57,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_31,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_55,axiom,(
    ! [A,B] : r1_xboole_0(k3_xboole_0(A,B),k5_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l97_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_63,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_67,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_93,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k4_xboole_0(B,k1_tarski(C)))
    <=> ( r2_hidden(A,B)
        & A != C ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_zfmisc_1)).

tff(c_50,plain,
    ( ~ r2_hidden('#skF_3','#skF_4')
    | r2_hidden('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_202,plain,(
    ~ r2_hidden('#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_22,plain,(
    ! [A_22] : k5_xboole_0(A_22,k1_xboole_0) = A_22 ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_40,plain,(
    ! [A_54,B_55] :
      ( r1_xboole_0(k1_tarski(A_54),B_55)
      | r2_hidden(A_54,B_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_12,plain,(
    ! [A_12] :
      ( r2_hidden('#skF_2'(A_12),A_12)
      | k1_xboole_0 = A_12 ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_318,plain,(
    ! [A_85,B_86,C_87] :
      ( ~ r1_xboole_0(A_85,B_86)
      | ~ r2_hidden(C_87,k3_xboole_0(A_85,B_86)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_693,plain,(
    ! [A_114,B_115] :
      ( ~ r1_xboole_0(A_114,B_115)
      | k3_xboole_0(A_114,B_115) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_12,c_318])).

tff(c_4684,plain,(
    ! [A_224,B_225] :
      ( k3_xboole_0(k1_tarski(A_224),B_225) = k1_xboole_0
      | r2_hidden(A_224,B_225) ) ),
    inference(resolution,[status(thm)],[c_40,c_693])).

tff(c_16,plain,(
    ! [A_16,B_17] : k5_xboole_0(A_16,k3_xboole_0(A_16,B_17)) = k4_xboole_0(A_16,B_17) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_4739,plain,(
    ! [A_224,B_225] :
      ( k5_xboole_0(k1_tarski(A_224),k1_xboole_0) = k4_xboole_0(k1_tarski(A_224),B_225)
      | r2_hidden(A_224,B_225) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4684,c_16])).

tff(c_21039,plain,(
    ! [A_384,B_385] :
      ( k4_xboole_0(k1_tarski(A_384),B_385) = k1_tarski(A_384)
      | r2_hidden(A_384,B_385) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_4739])).

tff(c_48,plain,
    ( k4_xboole_0(k1_tarski('#skF_3'),'#skF_4') != k1_tarski('#skF_3')
    | r2_hidden('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_316,plain,(
    k4_xboole_0(k1_tarski('#skF_3'),'#skF_4') != k1_tarski('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_21156,plain,(
    r2_hidden('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_21039,c_316])).

tff(c_21224,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_202,c_21156])).

tff(c_21225,plain,(
    r2_hidden('#skF_5','#skF_6') ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_118,plain,(
    ! [B_69,A_70] : k5_xboole_0(B_69,A_70) = k5_xboole_0(A_70,B_69) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_134,plain,(
    ! [A_70] : k5_xboole_0(k1_xboole_0,A_70) = A_70 ),
    inference(superposition,[status(thm),theory(equality)],[c_118,c_22])).

tff(c_6,plain,(
    ! [A_5] : k3_xboole_0(A_5,A_5) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_21234,plain,(
    ! [A_386,B_387] : k5_xboole_0(A_386,k3_xboole_0(A_386,B_387)) = k4_xboole_0(A_386,B_387) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_21263,plain,(
    ! [A_5] : k5_xboole_0(A_5,A_5) = k4_xboole_0(A_5,A_5) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_21234])).

tff(c_216,plain,(
    ! [A_76,B_77] : r1_xboole_0(k3_xboole_0(A_76,B_77),k5_xboole_0(A_76,B_77)) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_234,plain,(
    ! [A_5] : r1_xboole_0(A_5,k5_xboole_0(A_5,A_5)) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_216])).

tff(c_21272,plain,(
    ! [A_5] : r1_xboole_0(A_5,k4_xboole_0(A_5,A_5)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_21263,c_234])).

tff(c_8,plain,(
    ! [A_7,B_8] :
      ( r2_hidden('#skF_1'(A_7,B_8),k3_xboole_0(A_7,B_8))
      | r1_xboole_0(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_21335,plain,(
    ! [A_390,B_391,C_392] :
      ( ~ r1_xboole_0(A_390,B_391)
      | ~ r2_hidden(C_392,k3_xboole_0(A_390,B_391)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_23250,plain,(
    ! [B_475,A_476,C_477] :
      ( ~ r1_xboole_0(B_475,A_476)
      | ~ r2_hidden(C_477,k3_xboole_0(A_476,B_475)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_21335])).

tff(c_23295,plain,(
    ! [B_478,A_479] :
      ( ~ r1_xboole_0(B_478,A_479)
      | r1_xboole_0(A_479,B_478) ) ),
    inference(resolution,[status(thm)],[c_8,c_23250])).

tff(c_23316,plain,(
    ! [A_480] : r1_xboole_0(k4_xboole_0(A_480,A_480),A_480) ),
    inference(resolution,[status(thm)],[c_21272,c_23295])).

tff(c_21349,plain,(
    ! [A_390,B_391] :
      ( ~ r1_xboole_0(A_390,B_391)
      | k3_xboole_0(A_390,B_391) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_12,c_21335])).

tff(c_23335,plain,(
    ! [A_481] : k3_xboole_0(k4_xboole_0(A_481,A_481),A_481) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_23316,c_21349])).

tff(c_20,plain,(
    ! [A_20,B_21] : r1_tarski(k4_xboole_0(A_20,B_21),A_20) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_280,plain,(
    ! [A_81,B_82] :
      ( k3_xboole_0(A_81,B_82) = A_81
      | ~ r1_tarski(A_81,B_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_284,plain,(
    ! [A_20,B_21] : k3_xboole_0(k4_xboole_0(A_20,B_21),A_20) = k4_xboole_0(A_20,B_21) ),
    inference(resolution,[status(thm)],[c_20,c_280])).

tff(c_23349,plain,(
    ! [A_481] : k4_xboole_0(A_481,A_481) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_23335,c_284])).

tff(c_23454,plain,(
    ! [A_5] : k5_xboole_0(A_5,A_5) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_23349,c_21263])).

tff(c_21226,plain,(
    k4_xboole_0(k1_tarski('#skF_3'),'#skF_4') = k1_tarski('#skF_3') ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_52,plain,
    ( k4_xboole_0(k1_tarski('#skF_3'),'#skF_4') != k1_tarski('#skF_3')
    | k4_xboole_0(k1_tarski('#skF_5'),'#skF_6') = k1_tarski('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_21314,plain,(
    k4_xboole_0(k1_tarski('#skF_5'),'#skF_6') = k1_tarski('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_21226,c_52])).

tff(c_21586,plain,(
    ! [A_415,B_416,C_417] : k5_xboole_0(k5_xboole_0(A_415,B_416),C_417) = k5_xboole_0(A_415,k5_xboole_0(B_416,C_417)) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_28209,plain,(
    ! [A_562,B_563,C_564] : k5_xboole_0(A_562,k5_xboole_0(k3_xboole_0(A_562,B_563),C_564)) = k5_xboole_0(k4_xboole_0(A_562,B_563),C_564) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_21586])).

tff(c_28390,plain,(
    ! [A_562,B_563] : k5_xboole_0(k4_xboole_0(A_562,B_563),k3_xboole_0(A_562,B_563)) = k5_xboole_0(A_562,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_23454,c_28209])).

tff(c_29153,plain,(
    ! [A_568,B_569] : k5_xboole_0(k4_xboole_0(A_568,B_569),k3_xboole_0(A_568,B_569)) = A_568 ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_28390])).

tff(c_29512,plain,(
    ! [B_575,A_576] : k5_xboole_0(k4_xboole_0(B_575,A_576),k3_xboole_0(A_576,B_575)) = B_575 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_29153])).

tff(c_29664,plain,(
    k5_xboole_0(k1_tarski('#skF_5'),k3_xboole_0('#skF_6',k1_tarski('#skF_5'))) = k1_tarski('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_21314,c_29512])).

tff(c_4,plain,(
    ! [B_4,A_3] : k5_xboole_0(B_4,A_3) = k5_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_23511,plain,(
    ! [A_486] : k5_xboole_0(A_486,A_486) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_23349,c_21263])).

tff(c_24,plain,(
    ! [A_23,B_24,C_25] : k5_xboole_0(k5_xboole_0(A_23,B_24),C_25) = k5_xboole_0(A_23,k5_xboole_0(B_24,C_25)) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_23516,plain,(
    ! [A_486,C_25] : k5_xboole_0(A_486,k5_xboole_0(A_486,C_25)) = k5_xboole_0(k1_xboole_0,C_25) ),
    inference(superposition,[status(thm),theory(equality)],[c_23511,c_24])).

tff(c_23628,plain,(
    ! [A_491,C_492] : k5_xboole_0(A_491,k5_xboole_0(A_491,C_492)) = C_492 ),
    inference(demodulation,[status(thm),theory(equality)],[c_134,c_23516])).

tff(c_23703,plain,(
    ! [A_493,B_494] : k5_xboole_0(A_493,k5_xboole_0(B_494,A_493)) = B_494 ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_23628])).

tff(c_23683,plain,(
    ! [A_3,B_4] : k5_xboole_0(A_3,k5_xboole_0(B_4,A_3)) = B_4 ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_23628])).

tff(c_23706,plain,(
    ! [B_494,A_493] : k5_xboole_0(k5_xboole_0(B_494,A_493),B_494) = A_493 ),
    inference(superposition,[status(thm),theory(equality)],[c_23703,c_23683])).

tff(c_29771,plain,(
    k5_xboole_0(k1_tarski('#skF_5'),k1_tarski('#skF_5')) = k3_xboole_0('#skF_6',k1_tarski('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_29664,c_23706])).

tff(c_29812,plain,(
    k3_xboole_0('#skF_6',k1_tarski('#skF_5')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_23454,c_29771])).

tff(c_24407,plain,(
    ! [B_508,A_509,B_510] : k5_xboole_0(B_508,k5_xboole_0(A_509,B_510)) = k5_xboole_0(A_509,k5_xboole_0(B_510,B_508)) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_21586])).

tff(c_25994,plain,(
    ! [A_533,B_534] : k5_xboole_0(k1_xboole_0,k5_xboole_0(A_533,B_534)) = k5_xboole_0(B_534,A_533) ),
    inference(superposition,[status(thm),theory(equality)],[c_134,c_24407])).

tff(c_26126,plain,(
    ! [A_16,B_17] : k5_xboole_0(k3_xboole_0(A_16,B_17),A_16) = k5_xboole_0(k1_xboole_0,k4_xboole_0(A_16,B_17)) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_25994])).

tff(c_26177,plain,(
    ! [A_16,B_17] : k5_xboole_0(k3_xboole_0(A_16,B_17),A_16) = k4_xboole_0(A_16,B_17) ),
    inference(demodulation,[status(thm),theory(equality)],[c_134,c_26126])).

tff(c_29848,plain,(
    k4_xboole_0('#skF_6',k1_tarski('#skF_5')) = k5_xboole_0(k1_xboole_0,'#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_29812,c_26177])).

tff(c_29918,plain,(
    k4_xboole_0('#skF_6',k1_tarski('#skF_5')) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_134,c_29848])).

tff(c_44,plain,(
    ! [C_58,B_57] : ~ r2_hidden(C_58,k4_xboole_0(B_57,k1_tarski(C_58))) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_30017,plain,(
    ~ r2_hidden('#skF_5','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_29918,c_44])).

tff(c_30042,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_21225,c_30017])).

tff(c_30043,plain,(
    r2_hidden('#skF_5','#skF_6') ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_30141,plain,(
    ! [A_588,B_589] : k5_xboole_0(A_588,k3_xboole_0(A_588,B_589)) = k4_xboole_0(A_588,B_589) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_30167,plain,(
    ! [A_5] : k5_xboole_0(A_5,A_5) = k4_xboole_0(A_5,A_5) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_30141])).

tff(c_30064,plain,(
    ! [A_583,B_584] : r1_xboole_0(k3_xboole_0(A_583,B_584),k5_xboole_0(A_583,B_584)) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_30082,plain,(
    ! [A_5] : r1_xboole_0(A_5,k5_xboole_0(A_5,A_5)) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_30064])).

tff(c_30171,plain,(
    ! [A_5] : r1_xboole_0(A_5,k4_xboole_0(A_5,A_5)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30167,c_30082])).

tff(c_30222,plain,(
    ! [A_592,B_593,C_594] :
      ( ~ r1_xboole_0(A_592,B_593)
      | ~ r2_hidden(C_594,k3_xboole_0(A_592,B_593)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_31956,plain,(
    ! [A_673,B_674,C_675] :
      ( ~ r1_xboole_0(A_673,B_674)
      | ~ r2_hidden(C_675,k3_xboole_0(B_674,A_673)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_30222])).

tff(c_32122,plain,(
    ! [B_679,A_680] :
      ( ~ r1_xboole_0(B_679,A_680)
      | r1_xboole_0(A_680,B_679) ) ),
    inference(resolution,[status(thm)],[c_8,c_31956])).

tff(c_32144,plain,(
    ! [A_681] : r1_xboole_0(k4_xboole_0(A_681,A_681),A_681) ),
    inference(resolution,[status(thm)],[c_30171,c_32122])).

tff(c_30236,plain,(
    ! [A_592,B_593] :
      ( ~ r1_xboole_0(A_592,B_593)
      | k3_xboole_0(A_592,B_593) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_12,c_30222])).

tff(c_32163,plain,(
    ! [A_682] : k3_xboole_0(k4_xboole_0(A_682,A_682),A_682) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_32144,c_30236])).

tff(c_30059,plain,(
    ! [A_581,B_582] :
      ( k3_xboole_0(A_581,B_582) = A_581
      | ~ r1_tarski(A_581,B_582) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_30063,plain,(
    ! [A_20,B_21] : k3_xboole_0(k4_xboole_0(A_20,B_21),A_20) = k4_xboole_0(A_20,B_21) ),
    inference(resolution,[status(thm)],[c_20,c_30059])).

tff(c_32174,plain,(
    ! [A_682] : k4_xboole_0(A_682,A_682) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_32163,c_30063])).

tff(c_32245,plain,(
    ! [A_5] : k5_xboole_0(A_5,A_5) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_32174,c_30167])).

tff(c_30044,plain,(
    r2_hidden('#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_54,plain,
    ( ~ r2_hidden('#skF_3','#skF_4')
    | k4_xboole_0(k1_tarski('#skF_5'),'#skF_6') = k1_tarski('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_30096,plain,(
    k4_xboole_0(k1_tarski('#skF_5'),'#skF_6') = k1_tarski('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30044,c_54])).

tff(c_32302,plain,(
    ! [A_685] : k5_xboole_0(A_685,A_685) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_32174,c_30167])).

tff(c_32310,plain,(
    ! [A_685,C_25] : k5_xboole_0(A_685,k5_xboole_0(A_685,C_25)) = k5_xboole_0(k1_xboole_0,C_25) ),
    inference(superposition,[status(thm),theory(equality)],[c_32302,c_24])).

tff(c_32383,plain,(
    ! [A_690,C_691] : k5_xboole_0(A_690,k5_xboole_0(A_690,C_691)) = C_691 ),
    inference(demodulation,[status(thm),theory(equality)],[c_134,c_32310])).

tff(c_36935,plain,(
    ! [A_768,B_769] : k5_xboole_0(A_768,k4_xboole_0(A_768,B_769)) = k3_xboole_0(A_768,B_769) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_32383])).

tff(c_37048,plain,(
    k5_xboole_0(k1_tarski('#skF_5'),k1_tarski('#skF_5')) = k3_xboole_0(k1_tarski('#skF_5'),'#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_30096,c_36935])).

tff(c_37075,plain,(
    k3_xboole_0('#skF_6',k1_tarski('#skF_5')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_32245,c_2,c_37048])).

tff(c_37148,plain,(
    k4_xboole_0('#skF_6',k1_tarski('#skF_5')) = k5_xboole_0('#skF_6',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_37075,c_16])).

tff(c_37176,plain,(
    k4_xboole_0('#skF_6',k1_tarski('#skF_5')) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_37148])).

tff(c_37507,plain,(
    ~ r2_hidden('#skF_5','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_37176,c_44])).

tff(c_37530,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30043,c_37507])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:37:37 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 11.59/4.83  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.59/4.84  
% 11.59/4.84  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.59/4.85  %$ r2_hidden > r1_xboole_0 > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_1
% 11.59/4.85  
% 11.59/4.85  %Foreground sorts:
% 11.59/4.85  
% 11.59/4.85  
% 11.59/4.85  %Background operators:
% 11.59/4.85  
% 11.59/4.85  
% 11.59/4.85  %Foreground operators:
% 11.59/4.85  tff('#skF_2', type, '#skF_2': $i > $i).
% 11.59/4.85  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 11.59/4.85  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 11.59/4.85  tff(k1_tarski, type, k1_tarski: $i > $i).
% 11.59/4.85  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 11.59/4.85  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 11.59/4.85  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 11.59/4.85  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 11.59/4.85  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 11.59/4.85  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 11.59/4.85  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 11.59/4.85  tff('#skF_5', type, '#skF_5': $i).
% 11.59/4.85  tff('#skF_6', type, '#skF_6': $i).
% 11.59/4.85  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 11.59/4.85  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 11.59/4.85  tff('#skF_3', type, '#skF_3': $i).
% 11.59/4.85  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 11.59/4.85  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 11.59/4.85  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 11.59/4.85  tff('#skF_4', type, '#skF_4': $i).
% 11.59/4.85  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 11.59/4.85  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 11.59/4.85  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 11.59/4.85  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 11.59/4.85  
% 11.59/4.87  tff(f_99, negated_conjecture, ~(![A, B]: ((k4_xboole_0(k1_tarski(A), B) = k1_tarski(A)) <=> ~r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t67_zfmisc_1)).
% 11.59/4.87  tff(f_65, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 11.59/4.87  tff(f_86, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 11.59/4.87  tff(f_53, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 11.59/4.87  tff(f_45, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 11.59/4.87  tff(f_57, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 11.59/4.87  tff(f_29, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 11.59/4.87  tff(f_31, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 11.59/4.87  tff(f_55, axiom, (![A, B]: r1_xboole_0(k3_xboole_0(A, B), k5_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l97_xboole_1)).
% 11.59/4.87  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 11.59/4.87  tff(f_63, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 11.59/4.87  tff(f_61, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 11.59/4.87  tff(f_67, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_xboole_1)).
% 11.59/4.87  tff(f_93, axiom, (![A, B, C]: (r2_hidden(A, k4_xboole_0(B, k1_tarski(C))) <=> (r2_hidden(A, B) & ~(A = C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_zfmisc_1)).
% 11.59/4.87  tff(c_50, plain, (~r2_hidden('#skF_3', '#skF_4') | r2_hidden('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_99])).
% 11.59/4.87  tff(c_202, plain, (~r2_hidden('#skF_3', '#skF_4')), inference(splitLeft, [status(thm)], [c_50])).
% 11.59/4.87  tff(c_22, plain, (![A_22]: (k5_xboole_0(A_22, k1_xboole_0)=A_22)), inference(cnfTransformation, [status(thm)], [f_65])).
% 11.59/4.87  tff(c_40, plain, (![A_54, B_55]: (r1_xboole_0(k1_tarski(A_54), B_55) | r2_hidden(A_54, B_55))), inference(cnfTransformation, [status(thm)], [f_86])).
% 11.59/4.87  tff(c_12, plain, (![A_12]: (r2_hidden('#skF_2'(A_12), A_12) | k1_xboole_0=A_12)), inference(cnfTransformation, [status(thm)], [f_53])).
% 11.59/4.87  tff(c_318, plain, (![A_85, B_86, C_87]: (~r1_xboole_0(A_85, B_86) | ~r2_hidden(C_87, k3_xboole_0(A_85, B_86)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 11.59/4.87  tff(c_693, plain, (![A_114, B_115]: (~r1_xboole_0(A_114, B_115) | k3_xboole_0(A_114, B_115)=k1_xboole_0)), inference(resolution, [status(thm)], [c_12, c_318])).
% 11.59/4.87  tff(c_4684, plain, (![A_224, B_225]: (k3_xboole_0(k1_tarski(A_224), B_225)=k1_xboole_0 | r2_hidden(A_224, B_225))), inference(resolution, [status(thm)], [c_40, c_693])).
% 11.59/4.87  tff(c_16, plain, (![A_16, B_17]: (k5_xboole_0(A_16, k3_xboole_0(A_16, B_17))=k4_xboole_0(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_57])).
% 11.59/4.87  tff(c_4739, plain, (![A_224, B_225]: (k5_xboole_0(k1_tarski(A_224), k1_xboole_0)=k4_xboole_0(k1_tarski(A_224), B_225) | r2_hidden(A_224, B_225))), inference(superposition, [status(thm), theory('equality')], [c_4684, c_16])).
% 11.59/4.87  tff(c_21039, plain, (![A_384, B_385]: (k4_xboole_0(k1_tarski(A_384), B_385)=k1_tarski(A_384) | r2_hidden(A_384, B_385))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_4739])).
% 11.59/4.87  tff(c_48, plain, (k4_xboole_0(k1_tarski('#skF_3'), '#skF_4')!=k1_tarski('#skF_3') | r2_hidden('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_99])).
% 11.59/4.87  tff(c_316, plain, (k4_xboole_0(k1_tarski('#skF_3'), '#skF_4')!=k1_tarski('#skF_3')), inference(splitLeft, [status(thm)], [c_48])).
% 11.59/4.87  tff(c_21156, plain, (r2_hidden('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_21039, c_316])).
% 11.59/4.87  tff(c_21224, plain, $false, inference(negUnitSimplification, [status(thm)], [c_202, c_21156])).
% 11.59/4.87  tff(c_21225, plain, (r2_hidden('#skF_5', '#skF_6')), inference(splitRight, [status(thm)], [c_48])).
% 11.59/4.87  tff(c_118, plain, (![B_69, A_70]: (k5_xboole_0(B_69, A_70)=k5_xboole_0(A_70, B_69))), inference(cnfTransformation, [status(thm)], [f_29])).
% 11.59/4.87  tff(c_134, plain, (![A_70]: (k5_xboole_0(k1_xboole_0, A_70)=A_70)), inference(superposition, [status(thm), theory('equality')], [c_118, c_22])).
% 11.59/4.87  tff(c_6, plain, (![A_5]: (k3_xboole_0(A_5, A_5)=A_5)), inference(cnfTransformation, [status(thm)], [f_31])).
% 11.59/4.87  tff(c_21234, plain, (![A_386, B_387]: (k5_xboole_0(A_386, k3_xboole_0(A_386, B_387))=k4_xboole_0(A_386, B_387))), inference(cnfTransformation, [status(thm)], [f_57])).
% 11.59/4.87  tff(c_21263, plain, (![A_5]: (k5_xboole_0(A_5, A_5)=k4_xboole_0(A_5, A_5))), inference(superposition, [status(thm), theory('equality')], [c_6, c_21234])).
% 11.59/4.87  tff(c_216, plain, (![A_76, B_77]: (r1_xboole_0(k3_xboole_0(A_76, B_77), k5_xboole_0(A_76, B_77)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 11.59/4.87  tff(c_234, plain, (![A_5]: (r1_xboole_0(A_5, k5_xboole_0(A_5, A_5)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_216])).
% 11.59/4.87  tff(c_21272, plain, (![A_5]: (r1_xboole_0(A_5, k4_xboole_0(A_5, A_5)))), inference(demodulation, [status(thm), theory('equality')], [c_21263, c_234])).
% 11.59/4.87  tff(c_8, plain, (![A_7, B_8]: (r2_hidden('#skF_1'(A_7, B_8), k3_xboole_0(A_7, B_8)) | r1_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_45])).
% 11.59/4.87  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 11.59/4.87  tff(c_21335, plain, (![A_390, B_391, C_392]: (~r1_xboole_0(A_390, B_391) | ~r2_hidden(C_392, k3_xboole_0(A_390, B_391)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 11.59/4.87  tff(c_23250, plain, (![B_475, A_476, C_477]: (~r1_xboole_0(B_475, A_476) | ~r2_hidden(C_477, k3_xboole_0(A_476, B_475)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_21335])).
% 11.59/4.87  tff(c_23295, plain, (![B_478, A_479]: (~r1_xboole_0(B_478, A_479) | r1_xboole_0(A_479, B_478))), inference(resolution, [status(thm)], [c_8, c_23250])).
% 11.59/4.87  tff(c_23316, plain, (![A_480]: (r1_xboole_0(k4_xboole_0(A_480, A_480), A_480))), inference(resolution, [status(thm)], [c_21272, c_23295])).
% 11.59/4.87  tff(c_21349, plain, (![A_390, B_391]: (~r1_xboole_0(A_390, B_391) | k3_xboole_0(A_390, B_391)=k1_xboole_0)), inference(resolution, [status(thm)], [c_12, c_21335])).
% 11.59/4.87  tff(c_23335, plain, (![A_481]: (k3_xboole_0(k4_xboole_0(A_481, A_481), A_481)=k1_xboole_0)), inference(resolution, [status(thm)], [c_23316, c_21349])).
% 11.59/4.87  tff(c_20, plain, (![A_20, B_21]: (r1_tarski(k4_xboole_0(A_20, B_21), A_20))), inference(cnfTransformation, [status(thm)], [f_63])).
% 11.59/4.87  tff(c_280, plain, (![A_81, B_82]: (k3_xboole_0(A_81, B_82)=A_81 | ~r1_tarski(A_81, B_82))), inference(cnfTransformation, [status(thm)], [f_61])).
% 11.59/4.87  tff(c_284, plain, (![A_20, B_21]: (k3_xboole_0(k4_xboole_0(A_20, B_21), A_20)=k4_xboole_0(A_20, B_21))), inference(resolution, [status(thm)], [c_20, c_280])).
% 11.59/4.87  tff(c_23349, plain, (![A_481]: (k4_xboole_0(A_481, A_481)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_23335, c_284])).
% 11.59/4.87  tff(c_23454, plain, (![A_5]: (k5_xboole_0(A_5, A_5)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_23349, c_21263])).
% 11.59/4.87  tff(c_21226, plain, (k4_xboole_0(k1_tarski('#skF_3'), '#skF_4')=k1_tarski('#skF_3')), inference(splitRight, [status(thm)], [c_48])).
% 11.59/4.87  tff(c_52, plain, (k4_xboole_0(k1_tarski('#skF_3'), '#skF_4')!=k1_tarski('#skF_3') | k4_xboole_0(k1_tarski('#skF_5'), '#skF_6')=k1_tarski('#skF_5')), inference(cnfTransformation, [status(thm)], [f_99])).
% 11.59/4.87  tff(c_21314, plain, (k4_xboole_0(k1_tarski('#skF_5'), '#skF_6')=k1_tarski('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_21226, c_52])).
% 11.59/4.87  tff(c_21586, plain, (![A_415, B_416, C_417]: (k5_xboole_0(k5_xboole_0(A_415, B_416), C_417)=k5_xboole_0(A_415, k5_xboole_0(B_416, C_417)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 11.59/4.87  tff(c_28209, plain, (![A_562, B_563, C_564]: (k5_xboole_0(A_562, k5_xboole_0(k3_xboole_0(A_562, B_563), C_564))=k5_xboole_0(k4_xboole_0(A_562, B_563), C_564))), inference(superposition, [status(thm), theory('equality')], [c_16, c_21586])).
% 11.59/4.87  tff(c_28390, plain, (![A_562, B_563]: (k5_xboole_0(k4_xboole_0(A_562, B_563), k3_xboole_0(A_562, B_563))=k5_xboole_0(A_562, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_23454, c_28209])).
% 11.59/4.87  tff(c_29153, plain, (![A_568, B_569]: (k5_xboole_0(k4_xboole_0(A_568, B_569), k3_xboole_0(A_568, B_569))=A_568)), inference(demodulation, [status(thm), theory('equality')], [c_22, c_28390])).
% 11.59/4.87  tff(c_29512, plain, (![B_575, A_576]: (k5_xboole_0(k4_xboole_0(B_575, A_576), k3_xboole_0(A_576, B_575))=B_575)), inference(superposition, [status(thm), theory('equality')], [c_2, c_29153])).
% 11.59/4.87  tff(c_29664, plain, (k5_xboole_0(k1_tarski('#skF_5'), k3_xboole_0('#skF_6', k1_tarski('#skF_5')))=k1_tarski('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_21314, c_29512])).
% 11.59/4.87  tff(c_4, plain, (![B_4, A_3]: (k5_xboole_0(B_4, A_3)=k5_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 11.59/4.87  tff(c_23511, plain, (![A_486]: (k5_xboole_0(A_486, A_486)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_23349, c_21263])).
% 11.59/4.87  tff(c_24, plain, (![A_23, B_24, C_25]: (k5_xboole_0(k5_xboole_0(A_23, B_24), C_25)=k5_xboole_0(A_23, k5_xboole_0(B_24, C_25)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 11.59/4.87  tff(c_23516, plain, (![A_486, C_25]: (k5_xboole_0(A_486, k5_xboole_0(A_486, C_25))=k5_xboole_0(k1_xboole_0, C_25))), inference(superposition, [status(thm), theory('equality')], [c_23511, c_24])).
% 11.59/4.87  tff(c_23628, plain, (![A_491, C_492]: (k5_xboole_0(A_491, k5_xboole_0(A_491, C_492))=C_492)), inference(demodulation, [status(thm), theory('equality')], [c_134, c_23516])).
% 11.59/4.87  tff(c_23703, plain, (![A_493, B_494]: (k5_xboole_0(A_493, k5_xboole_0(B_494, A_493))=B_494)), inference(superposition, [status(thm), theory('equality')], [c_4, c_23628])).
% 11.59/4.87  tff(c_23683, plain, (![A_3, B_4]: (k5_xboole_0(A_3, k5_xboole_0(B_4, A_3))=B_4)), inference(superposition, [status(thm), theory('equality')], [c_4, c_23628])).
% 11.59/4.87  tff(c_23706, plain, (![B_494, A_493]: (k5_xboole_0(k5_xboole_0(B_494, A_493), B_494)=A_493)), inference(superposition, [status(thm), theory('equality')], [c_23703, c_23683])).
% 11.59/4.87  tff(c_29771, plain, (k5_xboole_0(k1_tarski('#skF_5'), k1_tarski('#skF_5'))=k3_xboole_0('#skF_6', k1_tarski('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_29664, c_23706])).
% 11.59/4.87  tff(c_29812, plain, (k3_xboole_0('#skF_6', k1_tarski('#skF_5'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_23454, c_29771])).
% 11.59/4.87  tff(c_24407, plain, (![B_508, A_509, B_510]: (k5_xboole_0(B_508, k5_xboole_0(A_509, B_510))=k5_xboole_0(A_509, k5_xboole_0(B_510, B_508)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_21586])).
% 11.59/4.87  tff(c_25994, plain, (![A_533, B_534]: (k5_xboole_0(k1_xboole_0, k5_xboole_0(A_533, B_534))=k5_xboole_0(B_534, A_533))), inference(superposition, [status(thm), theory('equality')], [c_134, c_24407])).
% 11.59/4.87  tff(c_26126, plain, (![A_16, B_17]: (k5_xboole_0(k3_xboole_0(A_16, B_17), A_16)=k5_xboole_0(k1_xboole_0, k4_xboole_0(A_16, B_17)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_25994])).
% 11.59/4.87  tff(c_26177, plain, (![A_16, B_17]: (k5_xboole_0(k3_xboole_0(A_16, B_17), A_16)=k4_xboole_0(A_16, B_17))), inference(demodulation, [status(thm), theory('equality')], [c_134, c_26126])).
% 11.59/4.87  tff(c_29848, plain, (k4_xboole_0('#skF_6', k1_tarski('#skF_5'))=k5_xboole_0(k1_xboole_0, '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_29812, c_26177])).
% 11.59/4.87  tff(c_29918, plain, (k4_xboole_0('#skF_6', k1_tarski('#skF_5'))='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_134, c_29848])).
% 11.59/4.87  tff(c_44, plain, (![C_58, B_57]: (~r2_hidden(C_58, k4_xboole_0(B_57, k1_tarski(C_58))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 11.59/4.87  tff(c_30017, plain, (~r2_hidden('#skF_5', '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_29918, c_44])).
% 11.59/4.87  tff(c_30042, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_21225, c_30017])).
% 11.59/4.87  tff(c_30043, plain, (r2_hidden('#skF_5', '#skF_6')), inference(splitRight, [status(thm)], [c_50])).
% 11.59/4.87  tff(c_30141, plain, (![A_588, B_589]: (k5_xboole_0(A_588, k3_xboole_0(A_588, B_589))=k4_xboole_0(A_588, B_589))), inference(cnfTransformation, [status(thm)], [f_57])).
% 11.59/4.87  tff(c_30167, plain, (![A_5]: (k5_xboole_0(A_5, A_5)=k4_xboole_0(A_5, A_5))), inference(superposition, [status(thm), theory('equality')], [c_6, c_30141])).
% 11.59/4.87  tff(c_30064, plain, (![A_583, B_584]: (r1_xboole_0(k3_xboole_0(A_583, B_584), k5_xboole_0(A_583, B_584)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 11.59/4.87  tff(c_30082, plain, (![A_5]: (r1_xboole_0(A_5, k5_xboole_0(A_5, A_5)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_30064])).
% 11.59/4.87  tff(c_30171, plain, (![A_5]: (r1_xboole_0(A_5, k4_xboole_0(A_5, A_5)))), inference(demodulation, [status(thm), theory('equality')], [c_30167, c_30082])).
% 11.59/4.87  tff(c_30222, plain, (![A_592, B_593, C_594]: (~r1_xboole_0(A_592, B_593) | ~r2_hidden(C_594, k3_xboole_0(A_592, B_593)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 11.59/4.87  tff(c_31956, plain, (![A_673, B_674, C_675]: (~r1_xboole_0(A_673, B_674) | ~r2_hidden(C_675, k3_xboole_0(B_674, A_673)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_30222])).
% 11.59/4.87  tff(c_32122, plain, (![B_679, A_680]: (~r1_xboole_0(B_679, A_680) | r1_xboole_0(A_680, B_679))), inference(resolution, [status(thm)], [c_8, c_31956])).
% 11.59/4.87  tff(c_32144, plain, (![A_681]: (r1_xboole_0(k4_xboole_0(A_681, A_681), A_681))), inference(resolution, [status(thm)], [c_30171, c_32122])).
% 11.59/4.87  tff(c_30236, plain, (![A_592, B_593]: (~r1_xboole_0(A_592, B_593) | k3_xboole_0(A_592, B_593)=k1_xboole_0)), inference(resolution, [status(thm)], [c_12, c_30222])).
% 11.59/4.87  tff(c_32163, plain, (![A_682]: (k3_xboole_0(k4_xboole_0(A_682, A_682), A_682)=k1_xboole_0)), inference(resolution, [status(thm)], [c_32144, c_30236])).
% 11.59/4.87  tff(c_30059, plain, (![A_581, B_582]: (k3_xboole_0(A_581, B_582)=A_581 | ~r1_tarski(A_581, B_582))), inference(cnfTransformation, [status(thm)], [f_61])).
% 11.59/4.87  tff(c_30063, plain, (![A_20, B_21]: (k3_xboole_0(k4_xboole_0(A_20, B_21), A_20)=k4_xboole_0(A_20, B_21))), inference(resolution, [status(thm)], [c_20, c_30059])).
% 11.59/4.87  tff(c_32174, plain, (![A_682]: (k4_xboole_0(A_682, A_682)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_32163, c_30063])).
% 11.59/4.87  tff(c_32245, plain, (![A_5]: (k5_xboole_0(A_5, A_5)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_32174, c_30167])).
% 11.59/4.87  tff(c_30044, plain, (r2_hidden('#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_50])).
% 11.59/4.87  tff(c_54, plain, (~r2_hidden('#skF_3', '#skF_4') | k4_xboole_0(k1_tarski('#skF_5'), '#skF_6')=k1_tarski('#skF_5')), inference(cnfTransformation, [status(thm)], [f_99])).
% 11.59/4.87  tff(c_30096, plain, (k4_xboole_0(k1_tarski('#skF_5'), '#skF_6')=k1_tarski('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_30044, c_54])).
% 11.59/4.87  tff(c_32302, plain, (![A_685]: (k5_xboole_0(A_685, A_685)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_32174, c_30167])).
% 11.59/4.87  tff(c_32310, plain, (![A_685, C_25]: (k5_xboole_0(A_685, k5_xboole_0(A_685, C_25))=k5_xboole_0(k1_xboole_0, C_25))), inference(superposition, [status(thm), theory('equality')], [c_32302, c_24])).
% 11.59/4.87  tff(c_32383, plain, (![A_690, C_691]: (k5_xboole_0(A_690, k5_xboole_0(A_690, C_691))=C_691)), inference(demodulation, [status(thm), theory('equality')], [c_134, c_32310])).
% 11.59/4.87  tff(c_36935, plain, (![A_768, B_769]: (k5_xboole_0(A_768, k4_xboole_0(A_768, B_769))=k3_xboole_0(A_768, B_769))), inference(superposition, [status(thm), theory('equality')], [c_16, c_32383])).
% 11.59/4.87  tff(c_37048, plain, (k5_xboole_0(k1_tarski('#skF_5'), k1_tarski('#skF_5'))=k3_xboole_0(k1_tarski('#skF_5'), '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_30096, c_36935])).
% 11.59/4.87  tff(c_37075, plain, (k3_xboole_0('#skF_6', k1_tarski('#skF_5'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_32245, c_2, c_37048])).
% 11.59/4.87  tff(c_37148, plain, (k4_xboole_0('#skF_6', k1_tarski('#skF_5'))=k5_xboole_0('#skF_6', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_37075, c_16])).
% 11.59/4.87  tff(c_37176, plain, (k4_xboole_0('#skF_6', k1_tarski('#skF_5'))='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_22, c_37148])).
% 11.59/4.87  tff(c_37507, plain, (~r2_hidden('#skF_5', '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_37176, c_44])).
% 11.59/4.87  tff(c_37530, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30043, c_37507])).
% 11.59/4.87  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.59/4.87  
% 11.59/4.87  Inference rules
% 11.59/4.87  ----------------------
% 11.59/4.87  #Ref     : 0
% 11.59/4.87  #Sup     : 9254
% 11.59/4.87  #Fact    : 0
% 11.59/4.87  #Define  : 0
% 11.59/4.87  #Split   : 2
% 11.59/4.87  #Chain   : 0
% 11.59/4.87  #Close   : 0
% 11.59/4.87  
% 11.59/4.87  Ordering : KBO
% 11.59/4.87  
% 11.59/4.87  Simplification rules
% 11.59/4.87  ----------------------
% 11.59/4.87  #Subsume      : 676
% 11.59/4.87  #Demod        : 10360
% 11.59/4.87  #Tautology    : 5754
% 11.59/4.87  #SimpNegUnit  : 183
% 11.59/4.87  #BackRed      : 83
% 11.59/4.87  
% 11.59/4.87  #Partial instantiations: 0
% 11.59/4.87  #Strategies tried      : 1
% 11.59/4.87  
% 11.59/4.87  Timing (in seconds)
% 11.59/4.87  ----------------------
% 11.59/4.87  Preprocessing        : 0.32
% 11.59/4.87  Parsing              : 0.18
% 11.59/4.87  CNF conversion       : 0.02
% 11.59/4.87  Main loop            : 3.76
% 11.59/4.87  Inferencing          : 0.77
% 11.59/4.87  Reduction            : 2.17
% 11.59/4.87  Demodulation         : 1.91
% 11.59/4.87  BG Simplification    : 0.11
% 11.59/4.87  Subsumption          : 0.50
% 11.59/4.87  Abstraction          : 0.15
% 11.59/4.87  MUC search           : 0.00
% 11.59/4.87  Cooper               : 0.00
% 11.59/4.87  Total                : 4.13
% 11.59/4.87  Index Insertion      : 0.00
% 11.59/4.87  Index Deletion       : 0.00
% 11.59/4.87  Index Matching       : 0.00
% 11.59/4.87  BG Taut test         : 0.00
%------------------------------------------------------------------------------

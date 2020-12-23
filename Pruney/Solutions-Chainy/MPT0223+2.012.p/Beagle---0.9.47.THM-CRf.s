%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:48:18 EST 2020

% Result     : Theorem 13.22s
% Output     : CNFRefutation 13.27s
% Verified   : 
% Statistics : Number of formulae       :  113 ( 487 expanded)
%              Number of leaves         :   36 ( 190 expanded)
%              Depth                    :   20
%              Number of atoms          :  107 ( 491 expanded)
%              Number of equality atoms :  100 ( 483 expanded)
%              Maximal formula depth    :   12 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i ) > $i )).

tff(f_81,negated_conjecture,(
    ~ ! [A,B] :
        ( k3_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
       => A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_zfmisc_1)).

tff(f_68,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_66,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_62,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k1_enumset1(A,B,C),k1_tarski(D)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_enumset1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_64,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_35,axiom,(
    ! [A,B] : k3_xboole_0(A,k2_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_xboole_1)).

tff(f_39,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_37,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_43,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(k5_xboole_0(A,B),k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t93_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k2_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

tff(f_31,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_33,axiom,(
    ! [A,B,C] : k5_xboole_0(k3_xboole_0(A,B),k3_xboole_0(C,B)) = k3_xboole_0(k5_xboole_0(A,C),B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t112_xboole_1)).

tff(f_60,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

tff(c_62,plain,(
    '#skF_3' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_52,plain,(
    ! [A_34,B_35,C_36] : k2_enumset1(A_34,A_34,B_35,C_36) = k1_enumset1(A_34,B_35,C_36) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_50,plain,(
    ! [A_32,B_33] : k1_enumset1(A_32,A_32,B_33) = k2_tarski(A_32,B_33) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_2595,plain,(
    ! [A_146,B_147,C_148,D_149] : k2_xboole_0(k1_enumset1(A_146,B_147,C_148),k1_tarski(D_149)) = k2_enumset1(A_146,B_147,C_148,D_149) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_2655,plain,(
    ! [A_32,B_33,D_149] : k2_xboole_0(k2_tarski(A_32,B_33),k1_tarski(D_149)) = k2_enumset1(A_32,A_32,B_33,D_149) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_2595])).

tff(c_2666,plain,(
    ! [A_150,B_151,D_152] : k2_xboole_0(k2_tarski(A_150,B_151),k1_tarski(D_152)) = k1_enumset1(A_150,B_151,D_152) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_2655])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_2717,plain,(
    ! [D_152,A_150,B_151] : k2_xboole_0(k1_tarski(D_152),k2_tarski(A_150,B_151)) = k1_enumset1(A_150,B_151,D_152) ),
    inference(superposition,[status(thm),theory(equality)],[c_2666,c_2])).

tff(c_48,plain,(
    ! [A_31] : k2_tarski(A_31,A_31) = k1_tarski(A_31) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_2732,plain,(
    ! [A_31,D_152] : k2_xboole_0(k1_tarski(A_31),k1_tarski(D_152)) = k1_enumset1(A_31,A_31,D_152) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_2666])).

tff(c_2738,plain,(
    ! [A_153,D_154] : k2_xboole_0(k1_tarski(A_153),k1_tarski(D_154)) = k2_tarski(A_153,D_154) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_2732])).

tff(c_10,plain,(
    ! [A_10,B_11] : k3_xboole_0(A_10,k2_xboole_0(A_10,B_11)) = A_10 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_2792,plain,(
    ! [A_153,D_154] : k3_xboole_0(k1_tarski(A_153),k2_tarski(A_153,D_154)) = k1_tarski(A_153) ),
    inference(superposition,[status(thm),theory(equality)],[c_2738,c_10])).

tff(c_14,plain,(
    ! [A_13] : k5_xboole_0(A_13,k1_xboole_0) = A_13 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_12,plain,(
    ! [A_12] : k3_xboole_0(A_12,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_246,plain,(
    ! [A_89,B_90] : k5_xboole_0(k5_xboole_0(A_89,B_90),k3_xboole_0(A_89,B_90)) = k2_xboole_0(A_89,B_90) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_273,plain,(
    ! [A_12] : k5_xboole_0(k5_xboole_0(A_12,k1_xboole_0),k1_xboole_0) = k2_xboole_0(A_12,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_246])).

tff(c_283,plain,(
    ! [A_12] : k2_xboole_0(A_12,k1_xboole_0) = A_12 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_14,c_273])).

tff(c_430,plain,(
    ! [A_94,B_95] : k5_xboole_0(k5_xboole_0(A_94,B_95),k2_xboole_0(A_94,B_95)) = k3_xboole_0(A_94,B_95) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_466,plain,(
    ! [A_13] : k5_xboole_0(A_13,k2_xboole_0(A_13,k1_xboole_0)) = k3_xboole_0(A_13,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_430])).

tff(c_476,plain,(
    ! [A_13] : k5_xboole_0(A_13,A_13) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_283,c_12,c_466])).

tff(c_18,plain,(
    ! [A_16,B_17] : k5_xboole_0(k5_xboole_0(A_16,B_17),k3_xboole_0(A_16,B_17)) = k2_xboole_0(A_16,B_17) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_557,plain,(
    ! [A_98,B_99] : k2_xboole_0(k5_xboole_0(A_98,B_99),k3_xboole_0(A_98,B_99)) = k2_xboole_0(A_98,B_99) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_20,plain,(
    ! [A_18,B_19] : k5_xboole_0(k5_xboole_0(A_18,B_19),k2_xboole_0(A_18,B_19)) = k3_xboole_0(A_18,B_19) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_563,plain,(
    ! [A_98,B_99] : k5_xboole_0(k5_xboole_0(k5_xboole_0(A_98,B_99),k3_xboole_0(A_98,B_99)),k2_xboole_0(A_98,B_99)) = k3_xboole_0(k5_xboole_0(A_98,B_99),k3_xboole_0(A_98,B_99)) ),
    inference(superposition,[status(thm),theory(equality)],[c_557,c_20])).

tff(c_636,plain,(
    ! [A_100,B_101] : k3_xboole_0(k5_xboole_0(A_100,B_101),k3_xboole_0(A_100,B_101)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_476,c_18,c_563])).

tff(c_679,plain,(
    ! [A_10,B_11] : k3_xboole_0(k5_xboole_0(A_10,k2_xboole_0(A_10,B_11)),A_10) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_636])).

tff(c_2777,plain,(
    ! [A_153,D_154] : k3_xboole_0(k5_xboole_0(k1_tarski(A_153),k2_tarski(A_153,D_154)),k1_tarski(A_153)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2738,c_679])).

tff(c_2736,plain,(
    ! [A_31,D_152] : k2_xboole_0(k1_tarski(A_31),k1_tarski(D_152)) = k2_tarski(A_31,D_152) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_2732])).

tff(c_64,plain,(
    k3_xboole_0(k1_tarski('#skF_3'),k1_tarski('#skF_4')) = k1_tarski('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_569,plain,(
    ! [A_98,B_99] : k2_xboole_0(k3_xboole_0(A_98,B_99),k5_xboole_0(A_98,B_99)) = k2_xboole_0(A_98,B_99) ),
    inference(superposition,[status(thm),theory(equality)],[c_557,c_2])).

tff(c_4,plain,(
    ! [A_3] : k2_xboole_0(A_3,A_3) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_6,plain,(
    ! [A_5] : k3_xboole_0(A_5,A_5) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_477,plain,(
    ! [A_96] : k5_xboole_0(A_96,A_96) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_283,c_12,c_466])).

tff(c_482,plain,(
    ! [A_96] : k5_xboole_0(k1_xboole_0,k2_xboole_0(A_96,A_96)) = k3_xboole_0(A_96,A_96) ),
    inference(superposition,[status(thm),theory(equality)],[c_477,c_20])).

tff(c_497,plain,(
    ! [A_96] : k5_xboole_0(k1_xboole_0,A_96) = A_96 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_6,c_482])).

tff(c_16,plain,(
    ! [A_14,B_15] : k2_xboole_0(k5_xboole_0(A_14,B_15),k3_xboole_0(A_14,B_15)) = k2_xboole_0(A_14,B_15) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_718,plain,(
    ! [A_102,B_103] : k3_xboole_0(k5_xboole_0(A_102,k2_xboole_0(A_102,B_103)),A_102) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_636])).

tff(c_737,plain,(
    ! [A_14,B_15] : k3_xboole_0(k5_xboole_0(k5_xboole_0(A_14,B_15),k2_xboole_0(A_14,B_15)),k5_xboole_0(A_14,B_15)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_718])).

tff(c_766,plain,(
    ! [A_14,B_15] : k3_xboole_0(k3_xboole_0(A_14,B_15),k5_xboole_0(A_14,B_15)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_737])).

tff(c_575,plain,(
    ! [A_98,B_99] : k3_xboole_0(k5_xboole_0(A_98,B_99),k2_xboole_0(A_98,B_99)) = k5_xboole_0(A_98,B_99) ),
    inference(superposition,[status(thm),theory(equality)],[c_557,c_10])).

tff(c_1279,plain,(
    ! [A_120,B_121] : k3_xboole_0(k5_xboole_0(A_120,B_121),k2_xboole_0(A_120,B_121)) = k5_xboole_0(A_120,B_121) ),
    inference(superposition,[status(thm),theory(equality)],[c_557,c_10])).

tff(c_1294,plain,(
    ! [A_120,B_121] : k2_xboole_0(k5_xboole_0(k5_xboole_0(A_120,B_121),k2_xboole_0(A_120,B_121)),k5_xboole_0(A_120,B_121)) = k2_xboole_0(k5_xboole_0(A_120,B_121),k2_xboole_0(A_120,B_121)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1279,c_16])).

tff(c_2457,plain,(
    ! [A_144,B_145] : k2_xboole_0(k2_xboole_0(A_144,B_145),k5_xboole_0(A_144,B_145)) = k2_xboole_0(A_144,B_145) ),
    inference(demodulation,[status(thm),theory(equality)],[c_569,c_20,c_2,c_1294])).

tff(c_460,plain,(
    ! [B_2,A_1] : k5_xboole_0(k5_xboole_0(B_2,A_1),k2_xboole_0(A_1,B_2)) = k3_xboole_0(B_2,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_430])).

tff(c_2484,plain,(
    ! [A_144,B_145] : k5_xboole_0(k5_xboole_0(k5_xboole_0(A_144,B_145),k2_xboole_0(A_144,B_145)),k2_xboole_0(A_144,B_145)) = k3_xboole_0(k5_xboole_0(A_144,B_145),k2_xboole_0(A_144,B_145)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2457,c_460])).

tff(c_5254,plain,(
    ! [A_221,B_222] : k5_xboole_0(k3_xboole_0(A_221,B_222),k2_xboole_0(A_221,B_222)) = k5_xboole_0(A_221,B_222) ),
    inference(demodulation,[status(thm),theory(equality)],[c_575,c_20,c_2484])).

tff(c_5401,plain,(
    ! [A_14,B_15] : k5_xboole_0(k1_xboole_0,k2_xboole_0(k3_xboole_0(A_14,B_15),k5_xboole_0(A_14,B_15))) = k5_xboole_0(k3_xboole_0(A_14,B_15),k5_xboole_0(A_14,B_15)) ),
    inference(superposition,[status(thm),theory(equality)],[c_766,c_5254])).

tff(c_7391,plain,(
    ! [A_251,B_252] : k5_xboole_0(k3_xboole_0(A_251,B_252),k5_xboole_0(A_251,B_252)) = k2_xboole_0(A_251,B_252) ),
    inference(demodulation,[status(thm),theory(equality)],[c_569,c_497,c_5401])).

tff(c_7601,plain,(
    k5_xboole_0(k1_tarski('#skF_3'),k5_xboole_0(k1_tarski('#skF_3'),k1_tarski('#skF_4'))) = k2_xboole_0(k1_tarski('#skF_3'),k1_tarski('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_64,c_7391])).

tff(c_7672,plain,(
    k5_xboole_0(k1_tarski('#skF_3'),k5_xboole_0(k1_tarski('#skF_3'),k1_tarski('#skF_4'))) = k2_tarski('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2736,c_2,c_7601])).

tff(c_1361,plain,(
    ! [A_122,B_123,C_124] : k5_xboole_0(k3_xboole_0(A_122,B_123),k3_xboole_0(C_124,B_123)) = k3_xboole_0(k5_xboole_0(A_122,C_124),B_123) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_1577,plain,(
    ! [A_126,A_127] : k5_xboole_0(k3_xboole_0(A_126,A_127),A_127) = k3_xboole_0(k5_xboole_0(A_126,A_127),A_127) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_1361])).

tff(c_1647,plain,(
    k3_xboole_0(k5_xboole_0(k1_tarski('#skF_3'),k1_tarski('#skF_4')),k1_tarski('#skF_4')) = k5_xboole_0(k1_tarski('#skF_3'),k1_tarski('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_64,c_1577])).

tff(c_1468,plain,(
    ! [C_124] : k5_xboole_0(k1_tarski('#skF_3'),k3_xboole_0(C_124,k1_tarski('#skF_4'))) = k3_xboole_0(k5_xboole_0(k1_tarski('#skF_3'),C_124),k1_tarski('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_64,c_1361])).

tff(c_2878,plain,(
    k3_xboole_0(k5_xboole_0(k1_tarski('#skF_3'),k5_xboole_0(k1_tarski('#skF_3'),k1_tarski('#skF_4'))),k1_tarski('#skF_4')) = k5_xboole_0(k1_tarski('#skF_3'),k5_xboole_0(k1_tarski('#skF_3'),k1_tarski('#skF_4'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_1647,c_1468])).

tff(c_23164,plain,(
    k3_xboole_0(k2_tarski('#skF_4','#skF_3'),k1_tarski('#skF_4')) = k2_tarski('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7672,c_7672,c_2878])).

tff(c_1480,plain,(
    ! [A_5,C_124] : k5_xboole_0(A_5,k3_xboole_0(C_124,A_5)) = k3_xboole_0(k5_xboole_0(A_5,C_124),A_5) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_1361])).

tff(c_23234,plain,(
    k3_xboole_0(k5_xboole_0(k1_tarski('#skF_4'),k2_tarski('#skF_4','#skF_3')),k1_tarski('#skF_4')) = k5_xboole_0(k1_tarski('#skF_4'),k2_tarski('#skF_4','#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_23164,c_1480])).

tff(c_23286,plain,(
    k5_xboole_0(k1_tarski('#skF_4'),k2_tarski('#skF_4','#skF_3')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2777,c_23234])).

tff(c_1347,plain,(
    ! [A_120,B_121] : k2_xboole_0(k2_xboole_0(A_120,B_121),k5_xboole_0(A_120,B_121)) = k2_xboole_0(A_120,B_121) ),
    inference(demodulation,[status(thm),theory(equality)],[c_569,c_20,c_2,c_1294])).

tff(c_1682,plain,(
    ! [A_128,C_129] : k5_xboole_0(A_128,k3_xboole_0(C_129,A_128)) = k3_xboole_0(k5_xboole_0(A_128,C_129),A_128) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_1361])).

tff(c_1731,plain,(
    ! [A_14,B_15] : k3_xboole_0(k5_xboole_0(k5_xboole_0(A_14,B_15),k3_xboole_0(A_14,B_15)),k5_xboole_0(A_14,B_15)) = k5_xboole_0(k5_xboole_0(A_14,B_15),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_766,c_1682])).

tff(c_1774,plain,(
    ! [A_14,B_15] : k3_xboole_0(k2_xboole_0(A_14,B_15),k5_xboole_0(A_14,B_15)) = k5_xboole_0(A_14,B_15) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_14,c_1731])).

tff(c_6627,plain,(
    ! [A_241,B_242] : k5_xboole_0(k3_xboole_0(A_241,B_242),k2_xboole_0(B_242,A_241)) = k5_xboole_0(A_241,B_242) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_5254])).

tff(c_6685,plain,(
    ! [A_14,B_15] : k5_xboole_0(k5_xboole_0(A_14,B_15),k2_xboole_0(k5_xboole_0(A_14,B_15),k2_xboole_0(A_14,B_15))) = k5_xboole_0(k2_xboole_0(A_14,B_15),k5_xboole_0(A_14,B_15)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1774,c_6627])).

tff(c_10127,plain,(
    ! [A_293,B_294] : k5_xboole_0(k2_xboole_0(A_293,B_294),k5_xboole_0(A_293,B_294)) = k3_xboole_0(A_293,B_294) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_1347,c_2,c_6685])).

tff(c_10292,plain,(
    ! [A_1,B_2] : k5_xboole_0(k2_xboole_0(A_1,B_2),k5_xboole_0(B_2,A_1)) = k3_xboole_0(B_2,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_10127])).

tff(c_23304,plain,(
    k5_xboole_0(k2_xboole_0(k2_tarski('#skF_4','#skF_3'),k1_tarski('#skF_4')),k1_xboole_0) = k3_xboole_0(k1_tarski('#skF_4'),k2_tarski('#skF_4','#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_23286,c_10292])).

tff(c_23361,plain,(
    k1_enumset1('#skF_4','#skF_3','#skF_4') = k1_tarski('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2717,c_2792,c_2,c_14,c_23304])).

tff(c_26,plain,(
    ! [E_26,A_20,C_22] : r2_hidden(E_26,k1_enumset1(A_20,E_26,C_22)) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_23449,plain,(
    r2_hidden('#skF_3',k1_tarski('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_23361,c_26])).

tff(c_2056,plain,(
    ! [E_134,C_135,B_136,A_137] :
      ( E_134 = C_135
      | E_134 = B_136
      | E_134 = A_137
      | ~ r2_hidden(E_134,k1_enumset1(A_137,B_136,C_135)) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_9197,plain,(
    ! [E_277,B_278,A_279] :
      ( E_277 = B_278
      | E_277 = A_279
      | E_277 = A_279
      | ~ r2_hidden(E_277,k2_tarski(A_279,B_278)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_2056])).

tff(c_9220,plain,(
    ! [E_277,A_31] :
      ( E_277 = A_31
      | E_277 = A_31
      | E_277 = A_31
      | ~ r2_hidden(E_277,k1_tarski(A_31)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_9197])).

tff(c_23480,plain,(
    '#skF_3' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_23449,c_9220])).

tff(c_23484,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_62,c_62,c_23480])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n004.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 15:15:53 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 13.22/5.71  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 13.27/5.72  
% 13.27/5.72  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 13.27/5.72  %$ r2_hidden > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 13.27/5.72  
% 13.27/5.72  %Foreground sorts:
% 13.27/5.72  
% 13.27/5.72  
% 13.27/5.72  %Background operators:
% 13.27/5.72  
% 13.27/5.72  
% 13.27/5.72  %Foreground operators:
% 13.27/5.72  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 13.27/5.72  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 13.27/5.72  tff(k1_tarski, type, k1_tarski: $i > $i).
% 13.27/5.72  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 13.27/5.72  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 13.27/5.72  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 13.27/5.72  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 13.27/5.72  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 13.27/5.72  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 13.27/5.72  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 13.27/5.72  tff('#skF_3', type, '#skF_3': $i).
% 13.27/5.72  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 13.27/5.72  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 13.27/5.72  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 13.27/5.72  tff('#skF_4', type, '#skF_4': $i).
% 13.27/5.72  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 13.27/5.72  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 13.27/5.72  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 13.27/5.72  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 13.27/5.72  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 13.27/5.72  
% 13.27/5.74  tff(f_81, negated_conjecture, ~(![A, B]: ((k3_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) => (A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t18_zfmisc_1)).
% 13.27/5.74  tff(f_68, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 13.27/5.74  tff(f_66, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 13.27/5.74  tff(f_62, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k1_enumset1(A, B, C), k1_tarski(D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_enumset1)).
% 13.27/5.74  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 13.27/5.74  tff(f_64, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 13.27/5.74  tff(f_35, axiom, (![A, B]: (k3_xboole_0(A, k2_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_xboole_1)).
% 13.27/5.74  tff(f_39, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 13.27/5.74  tff(f_37, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 13.27/5.74  tff(f_43, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_xboole_1)).
% 13.27/5.74  tff(f_45, axiom, (![A, B]: (k3_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k2_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t95_xboole_1)).
% 13.27/5.74  tff(f_41, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(k5_xboole_0(A, B), k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t93_xboole_1)).
% 13.27/5.74  tff(f_29, axiom, (![A, B]: (k2_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 13.27/5.74  tff(f_31, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 13.27/5.74  tff(f_33, axiom, (![A, B, C]: (k5_xboole_0(k3_xboole_0(A, B), k3_xboole_0(C, B)) = k3_xboole_0(k5_xboole_0(A, C), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t112_xboole_1)).
% 13.27/5.74  tff(f_60, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_enumset1)).
% 13.27/5.74  tff(c_62, plain, ('#skF_3'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_81])).
% 13.27/5.74  tff(c_52, plain, (![A_34, B_35, C_36]: (k2_enumset1(A_34, A_34, B_35, C_36)=k1_enumset1(A_34, B_35, C_36))), inference(cnfTransformation, [status(thm)], [f_68])).
% 13.27/5.74  tff(c_50, plain, (![A_32, B_33]: (k1_enumset1(A_32, A_32, B_33)=k2_tarski(A_32, B_33))), inference(cnfTransformation, [status(thm)], [f_66])).
% 13.27/5.74  tff(c_2595, plain, (![A_146, B_147, C_148, D_149]: (k2_xboole_0(k1_enumset1(A_146, B_147, C_148), k1_tarski(D_149))=k2_enumset1(A_146, B_147, C_148, D_149))), inference(cnfTransformation, [status(thm)], [f_62])).
% 13.27/5.74  tff(c_2655, plain, (![A_32, B_33, D_149]: (k2_xboole_0(k2_tarski(A_32, B_33), k1_tarski(D_149))=k2_enumset1(A_32, A_32, B_33, D_149))), inference(superposition, [status(thm), theory('equality')], [c_50, c_2595])).
% 13.27/5.74  tff(c_2666, plain, (![A_150, B_151, D_152]: (k2_xboole_0(k2_tarski(A_150, B_151), k1_tarski(D_152))=k1_enumset1(A_150, B_151, D_152))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_2655])).
% 13.27/5.74  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 13.27/5.74  tff(c_2717, plain, (![D_152, A_150, B_151]: (k2_xboole_0(k1_tarski(D_152), k2_tarski(A_150, B_151))=k1_enumset1(A_150, B_151, D_152))), inference(superposition, [status(thm), theory('equality')], [c_2666, c_2])).
% 13.27/5.74  tff(c_48, plain, (![A_31]: (k2_tarski(A_31, A_31)=k1_tarski(A_31))), inference(cnfTransformation, [status(thm)], [f_64])).
% 13.27/5.74  tff(c_2732, plain, (![A_31, D_152]: (k2_xboole_0(k1_tarski(A_31), k1_tarski(D_152))=k1_enumset1(A_31, A_31, D_152))), inference(superposition, [status(thm), theory('equality')], [c_48, c_2666])).
% 13.27/5.74  tff(c_2738, plain, (![A_153, D_154]: (k2_xboole_0(k1_tarski(A_153), k1_tarski(D_154))=k2_tarski(A_153, D_154))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_2732])).
% 13.27/5.74  tff(c_10, plain, (![A_10, B_11]: (k3_xboole_0(A_10, k2_xboole_0(A_10, B_11))=A_10)), inference(cnfTransformation, [status(thm)], [f_35])).
% 13.27/5.74  tff(c_2792, plain, (![A_153, D_154]: (k3_xboole_0(k1_tarski(A_153), k2_tarski(A_153, D_154))=k1_tarski(A_153))), inference(superposition, [status(thm), theory('equality')], [c_2738, c_10])).
% 13.27/5.74  tff(c_14, plain, (![A_13]: (k5_xboole_0(A_13, k1_xboole_0)=A_13)), inference(cnfTransformation, [status(thm)], [f_39])).
% 13.27/5.74  tff(c_12, plain, (![A_12]: (k3_xboole_0(A_12, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 13.27/5.74  tff(c_246, plain, (![A_89, B_90]: (k5_xboole_0(k5_xboole_0(A_89, B_90), k3_xboole_0(A_89, B_90))=k2_xboole_0(A_89, B_90))), inference(cnfTransformation, [status(thm)], [f_43])).
% 13.27/5.74  tff(c_273, plain, (![A_12]: (k5_xboole_0(k5_xboole_0(A_12, k1_xboole_0), k1_xboole_0)=k2_xboole_0(A_12, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_12, c_246])).
% 13.27/5.74  tff(c_283, plain, (![A_12]: (k2_xboole_0(A_12, k1_xboole_0)=A_12)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_14, c_273])).
% 13.27/5.74  tff(c_430, plain, (![A_94, B_95]: (k5_xboole_0(k5_xboole_0(A_94, B_95), k2_xboole_0(A_94, B_95))=k3_xboole_0(A_94, B_95))), inference(cnfTransformation, [status(thm)], [f_45])).
% 13.27/5.74  tff(c_466, plain, (![A_13]: (k5_xboole_0(A_13, k2_xboole_0(A_13, k1_xboole_0))=k3_xboole_0(A_13, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_14, c_430])).
% 13.27/5.74  tff(c_476, plain, (![A_13]: (k5_xboole_0(A_13, A_13)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_283, c_12, c_466])).
% 13.27/5.74  tff(c_18, plain, (![A_16, B_17]: (k5_xboole_0(k5_xboole_0(A_16, B_17), k3_xboole_0(A_16, B_17))=k2_xboole_0(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_43])).
% 13.27/5.74  tff(c_557, plain, (![A_98, B_99]: (k2_xboole_0(k5_xboole_0(A_98, B_99), k3_xboole_0(A_98, B_99))=k2_xboole_0(A_98, B_99))), inference(cnfTransformation, [status(thm)], [f_41])).
% 13.27/5.74  tff(c_20, plain, (![A_18, B_19]: (k5_xboole_0(k5_xboole_0(A_18, B_19), k2_xboole_0(A_18, B_19))=k3_xboole_0(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_45])).
% 13.27/5.74  tff(c_563, plain, (![A_98, B_99]: (k5_xboole_0(k5_xboole_0(k5_xboole_0(A_98, B_99), k3_xboole_0(A_98, B_99)), k2_xboole_0(A_98, B_99))=k3_xboole_0(k5_xboole_0(A_98, B_99), k3_xboole_0(A_98, B_99)))), inference(superposition, [status(thm), theory('equality')], [c_557, c_20])).
% 13.27/5.74  tff(c_636, plain, (![A_100, B_101]: (k3_xboole_0(k5_xboole_0(A_100, B_101), k3_xboole_0(A_100, B_101))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_476, c_18, c_563])).
% 13.27/5.74  tff(c_679, plain, (![A_10, B_11]: (k3_xboole_0(k5_xboole_0(A_10, k2_xboole_0(A_10, B_11)), A_10)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_10, c_636])).
% 13.27/5.74  tff(c_2777, plain, (![A_153, D_154]: (k3_xboole_0(k5_xboole_0(k1_tarski(A_153), k2_tarski(A_153, D_154)), k1_tarski(A_153))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2738, c_679])).
% 13.27/5.74  tff(c_2736, plain, (![A_31, D_152]: (k2_xboole_0(k1_tarski(A_31), k1_tarski(D_152))=k2_tarski(A_31, D_152))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_2732])).
% 13.27/5.74  tff(c_64, plain, (k3_xboole_0(k1_tarski('#skF_3'), k1_tarski('#skF_4'))=k1_tarski('#skF_3')), inference(cnfTransformation, [status(thm)], [f_81])).
% 13.27/5.74  tff(c_569, plain, (![A_98, B_99]: (k2_xboole_0(k3_xboole_0(A_98, B_99), k5_xboole_0(A_98, B_99))=k2_xboole_0(A_98, B_99))), inference(superposition, [status(thm), theory('equality')], [c_557, c_2])).
% 13.27/5.74  tff(c_4, plain, (![A_3]: (k2_xboole_0(A_3, A_3)=A_3)), inference(cnfTransformation, [status(thm)], [f_29])).
% 13.27/5.74  tff(c_6, plain, (![A_5]: (k3_xboole_0(A_5, A_5)=A_5)), inference(cnfTransformation, [status(thm)], [f_31])).
% 13.27/5.74  tff(c_477, plain, (![A_96]: (k5_xboole_0(A_96, A_96)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_283, c_12, c_466])).
% 13.27/5.74  tff(c_482, plain, (![A_96]: (k5_xboole_0(k1_xboole_0, k2_xboole_0(A_96, A_96))=k3_xboole_0(A_96, A_96))), inference(superposition, [status(thm), theory('equality')], [c_477, c_20])).
% 13.27/5.74  tff(c_497, plain, (![A_96]: (k5_xboole_0(k1_xboole_0, A_96)=A_96)), inference(demodulation, [status(thm), theory('equality')], [c_4, c_6, c_482])).
% 13.27/5.74  tff(c_16, plain, (![A_14, B_15]: (k2_xboole_0(k5_xboole_0(A_14, B_15), k3_xboole_0(A_14, B_15))=k2_xboole_0(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_41])).
% 13.27/5.74  tff(c_718, plain, (![A_102, B_103]: (k3_xboole_0(k5_xboole_0(A_102, k2_xboole_0(A_102, B_103)), A_102)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_10, c_636])).
% 13.27/5.74  tff(c_737, plain, (![A_14, B_15]: (k3_xboole_0(k5_xboole_0(k5_xboole_0(A_14, B_15), k2_xboole_0(A_14, B_15)), k5_xboole_0(A_14, B_15))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_16, c_718])).
% 13.27/5.74  tff(c_766, plain, (![A_14, B_15]: (k3_xboole_0(k3_xboole_0(A_14, B_15), k5_xboole_0(A_14, B_15))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_20, c_737])).
% 13.27/5.74  tff(c_575, plain, (![A_98, B_99]: (k3_xboole_0(k5_xboole_0(A_98, B_99), k2_xboole_0(A_98, B_99))=k5_xboole_0(A_98, B_99))), inference(superposition, [status(thm), theory('equality')], [c_557, c_10])).
% 13.27/5.74  tff(c_1279, plain, (![A_120, B_121]: (k3_xboole_0(k5_xboole_0(A_120, B_121), k2_xboole_0(A_120, B_121))=k5_xboole_0(A_120, B_121))), inference(superposition, [status(thm), theory('equality')], [c_557, c_10])).
% 13.27/5.74  tff(c_1294, plain, (![A_120, B_121]: (k2_xboole_0(k5_xboole_0(k5_xboole_0(A_120, B_121), k2_xboole_0(A_120, B_121)), k5_xboole_0(A_120, B_121))=k2_xboole_0(k5_xboole_0(A_120, B_121), k2_xboole_0(A_120, B_121)))), inference(superposition, [status(thm), theory('equality')], [c_1279, c_16])).
% 13.27/5.74  tff(c_2457, plain, (![A_144, B_145]: (k2_xboole_0(k2_xboole_0(A_144, B_145), k5_xboole_0(A_144, B_145))=k2_xboole_0(A_144, B_145))), inference(demodulation, [status(thm), theory('equality')], [c_569, c_20, c_2, c_1294])).
% 13.27/5.74  tff(c_460, plain, (![B_2, A_1]: (k5_xboole_0(k5_xboole_0(B_2, A_1), k2_xboole_0(A_1, B_2))=k3_xboole_0(B_2, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_430])).
% 13.27/5.74  tff(c_2484, plain, (![A_144, B_145]: (k5_xboole_0(k5_xboole_0(k5_xboole_0(A_144, B_145), k2_xboole_0(A_144, B_145)), k2_xboole_0(A_144, B_145))=k3_xboole_0(k5_xboole_0(A_144, B_145), k2_xboole_0(A_144, B_145)))), inference(superposition, [status(thm), theory('equality')], [c_2457, c_460])).
% 13.27/5.74  tff(c_5254, plain, (![A_221, B_222]: (k5_xboole_0(k3_xboole_0(A_221, B_222), k2_xboole_0(A_221, B_222))=k5_xboole_0(A_221, B_222))), inference(demodulation, [status(thm), theory('equality')], [c_575, c_20, c_2484])).
% 13.27/5.74  tff(c_5401, plain, (![A_14, B_15]: (k5_xboole_0(k1_xboole_0, k2_xboole_0(k3_xboole_0(A_14, B_15), k5_xboole_0(A_14, B_15)))=k5_xboole_0(k3_xboole_0(A_14, B_15), k5_xboole_0(A_14, B_15)))), inference(superposition, [status(thm), theory('equality')], [c_766, c_5254])).
% 13.27/5.74  tff(c_7391, plain, (![A_251, B_252]: (k5_xboole_0(k3_xboole_0(A_251, B_252), k5_xboole_0(A_251, B_252))=k2_xboole_0(A_251, B_252))), inference(demodulation, [status(thm), theory('equality')], [c_569, c_497, c_5401])).
% 13.27/5.74  tff(c_7601, plain, (k5_xboole_0(k1_tarski('#skF_3'), k5_xboole_0(k1_tarski('#skF_3'), k1_tarski('#skF_4')))=k2_xboole_0(k1_tarski('#skF_3'), k1_tarski('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_64, c_7391])).
% 13.27/5.74  tff(c_7672, plain, (k5_xboole_0(k1_tarski('#skF_3'), k5_xboole_0(k1_tarski('#skF_3'), k1_tarski('#skF_4')))=k2_tarski('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2736, c_2, c_7601])).
% 13.27/5.74  tff(c_1361, plain, (![A_122, B_123, C_124]: (k5_xboole_0(k3_xboole_0(A_122, B_123), k3_xboole_0(C_124, B_123))=k3_xboole_0(k5_xboole_0(A_122, C_124), B_123))), inference(cnfTransformation, [status(thm)], [f_33])).
% 13.27/5.74  tff(c_1577, plain, (![A_126, A_127]: (k5_xboole_0(k3_xboole_0(A_126, A_127), A_127)=k3_xboole_0(k5_xboole_0(A_126, A_127), A_127))), inference(superposition, [status(thm), theory('equality')], [c_6, c_1361])).
% 13.27/5.74  tff(c_1647, plain, (k3_xboole_0(k5_xboole_0(k1_tarski('#skF_3'), k1_tarski('#skF_4')), k1_tarski('#skF_4'))=k5_xboole_0(k1_tarski('#skF_3'), k1_tarski('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_64, c_1577])).
% 13.27/5.74  tff(c_1468, plain, (![C_124]: (k5_xboole_0(k1_tarski('#skF_3'), k3_xboole_0(C_124, k1_tarski('#skF_4')))=k3_xboole_0(k5_xboole_0(k1_tarski('#skF_3'), C_124), k1_tarski('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_64, c_1361])).
% 13.27/5.74  tff(c_2878, plain, (k3_xboole_0(k5_xboole_0(k1_tarski('#skF_3'), k5_xboole_0(k1_tarski('#skF_3'), k1_tarski('#skF_4'))), k1_tarski('#skF_4'))=k5_xboole_0(k1_tarski('#skF_3'), k5_xboole_0(k1_tarski('#skF_3'), k1_tarski('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_1647, c_1468])).
% 13.27/5.74  tff(c_23164, plain, (k3_xboole_0(k2_tarski('#skF_4', '#skF_3'), k1_tarski('#skF_4'))=k2_tarski('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_7672, c_7672, c_2878])).
% 13.27/5.74  tff(c_1480, plain, (![A_5, C_124]: (k5_xboole_0(A_5, k3_xboole_0(C_124, A_5))=k3_xboole_0(k5_xboole_0(A_5, C_124), A_5))), inference(superposition, [status(thm), theory('equality')], [c_6, c_1361])).
% 13.27/5.74  tff(c_23234, plain, (k3_xboole_0(k5_xboole_0(k1_tarski('#skF_4'), k2_tarski('#skF_4', '#skF_3')), k1_tarski('#skF_4'))=k5_xboole_0(k1_tarski('#skF_4'), k2_tarski('#skF_4', '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_23164, c_1480])).
% 13.27/5.74  tff(c_23286, plain, (k5_xboole_0(k1_tarski('#skF_4'), k2_tarski('#skF_4', '#skF_3'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_2777, c_23234])).
% 13.27/5.74  tff(c_1347, plain, (![A_120, B_121]: (k2_xboole_0(k2_xboole_0(A_120, B_121), k5_xboole_0(A_120, B_121))=k2_xboole_0(A_120, B_121))), inference(demodulation, [status(thm), theory('equality')], [c_569, c_20, c_2, c_1294])).
% 13.27/5.74  tff(c_1682, plain, (![A_128, C_129]: (k5_xboole_0(A_128, k3_xboole_0(C_129, A_128))=k3_xboole_0(k5_xboole_0(A_128, C_129), A_128))), inference(superposition, [status(thm), theory('equality')], [c_6, c_1361])).
% 13.27/5.74  tff(c_1731, plain, (![A_14, B_15]: (k3_xboole_0(k5_xboole_0(k5_xboole_0(A_14, B_15), k3_xboole_0(A_14, B_15)), k5_xboole_0(A_14, B_15))=k5_xboole_0(k5_xboole_0(A_14, B_15), k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_766, c_1682])).
% 13.27/5.74  tff(c_1774, plain, (![A_14, B_15]: (k3_xboole_0(k2_xboole_0(A_14, B_15), k5_xboole_0(A_14, B_15))=k5_xboole_0(A_14, B_15))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_14, c_1731])).
% 13.27/5.74  tff(c_6627, plain, (![A_241, B_242]: (k5_xboole_0(k3_xboole_0(A_241, B_242), k2_xboole_0(B_242, A_241))=k5_xboole_0(A_241, B_242))), inference(superposition, [status(thm), theory('equality')], [c_2, c_5254])).
% 13.27/5.74  tff(c_6685, plain, (![A_14, B_15]: (k5_xboole_0(k5_xboole_0(A_14, B_15), k2_xboole_0(k5_xboole_0(A_14, B_15), k2_xboole_0(A_14, B_15)))=k5_xboole_0(k2_xboole_0(A_14, B_15), k5_xboole_0(A_14, B_15)))), inference(superposition, [status(thm), theory('equality')], [c_1774, c_6627])).
% 13.27/5.74  tff(c_10127, plain, (![A_293, B_294]: (k5_xboole_0(k2_xboole_0(A_293, B_294), k5_xboole_0(A_293, B_294))=k3_xboole_0(A_293, B_294))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_1347, c_2, c_6685])).
% 13.27/5.74  tff(c_10292, plain, (![A_1, B_2]: (k5_xboole_0(k2_xboole_0(A_1, B_2), k5_xboole_0(B_2, A_1))=k3_xboole_0(B_2, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_10127])).
% 13.27/5.74  tff(c_23304, plain, (k5_xboole_0(k2_xboole_0(k2_tarski('#skF_4', '#skF_3'), k1_tarski('#skF_4')), k1_xboole_0)=k3_xboole_0(k1_tarski('#skF_4'), k2_tarski('#skF_4', '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_23286, c_10292])).
% 13.27/5.74  tff(c_23361, plain, (k1_enumset1('#skF_4', '#skF_3', '#skF_4')=k1_tarski('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2717, c_2792, c_2, c_14, c_23304])).
% 13.27/5.74  tff(c_26, plain, (![E_26, A_20, C_22]: (r2_hidden(E_26, k1_enumset1(A_20, E_26, C_22)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 13.27/5.74  tff(c_23449, plain, (r2_hidden('#skF_3', k1_tarski('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_23361, c_26])).
% 13.27/5.74  tff(c_2056, plain, (![E_134, C_135, B_136, A_137]: (E_134=C_135 | E_134=B_136 | E_134=A_137 | ~r2_hidden(E_134, k1_enumset1(A_137, B_136, C_135)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 13.27/5.74  tff(c_9197, plain, (![E_277, B_278, A_279]: (E_277=B_278 | E_277=A_279 | E_277=A_279 | ~r2_hidden(E_277, k2_tarski(A_279, B_278)))), inference(superposition, [status(thm), theory('equality')], [c_50, c_2056])).
% 13.27/5.74  tff(c_9220, plain, (![E_277, A_31]: (E_277=A_31 | E_277=A_31 | E_277=A_31 | ~r2_hidden(E_277, k1_tarski(A_31)))), inference(superposition, [status(thm), theory('equality')], [c_48, c_9197])).
% 13.27/5.74  tff(c_23480, plain, ('#skF_3'='#skF_4'), inference(resolution, [status(thm)], [c_23449, c_9220])).
% 13.27/5.74  tff(c_23484, plain, $false, inference(negUnitSimplification, [status(thm)], [c_62, c_62, c_62, c_23480])).
% 13.27/5.74  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 13.27/5.74  
% 13.27/5.74  Inference rules
% 13.27/5.74  ----------------------
% 13.27/5.74  #Ref     : 0
% 13.27/5.74  #Sup     : 6004
% 13.27/5.74  #Fact    : 6
% 13.27/5.74  #Define  : 0
% 13.27/5.74  #Split   : 0
% 13.27/5.74  #Chain   : 0
% 13.27/5.74  #Close   : 0
% 13.27/5.74  
% 13.27/5.74  Ordering : KBO
% 13.27/5.74  
% 13.27/5.74  Simplification rules
% 13.27/5.74  ----------------------
% 13.27/5.74  #Subsume      : 161
% 13.27/5.74  #Demod        : 9928
% 13.27/5.74  #Tautology    : 2838
% 13.27/5.74  #SimpNegUnit  : 3
% 13.27/5.74  #BackRed      : 4
% 13.27/5.74  
% 13.27/5.74  #Partial instantiations: 0
% 13.27/5.74  #Strategies tried      : 1
% 13.27/5.74  
% 13.27/5.74  Timing (in seconds)
% 13.27/5.74  ----------------------
% 13.27/5.75  Preprocessing        : 0.34
% 13.27/5.75  Parsing              : 0.18
% 13.27/5.75  CNF conversion       : 0.02
% 13.27/5.75  Main loop            : 4.63
% 13.27/5.75  Inferencing          : 0.76
% 13.27/5.75  Reduction            : 3.02
% 13.27/5.75  Demodulation         : 2.77
% 13.27/5.75  BG Simplification    : 0.12
% 13.27/5.75  Subsumption          : 0.55
% 13.27/5.75  Abstraction          : 0.24
% 13.27/5.75  MUC search           : 0.00
% 13.27/5.75  Cooper               : 0.00
% 13.27/5.75  Total                : 5.01
% 13.27/5.75  Index Insertion      : 0.00
% 13.27/5.75  Index Deletion       : 0.00
% 13.27/5.75  Index Matching       : 0.00
% 13.27/5.75  BG Taut test         : 0.00
%------------------------------------------------------------------------------

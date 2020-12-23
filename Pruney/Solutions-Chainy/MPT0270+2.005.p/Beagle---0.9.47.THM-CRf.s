%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:52:53 EST 2020

% Result     : Theorem 11.60s
% Output     : CNFRefutation 11.91s
% Verified   : 
% Statistics : Number of formulae       :  120 ( 184 expanded)
%              Number of leaves         :   46 (  78 expanded)
%              Depth                    :   23
%              Number of atoms          :  121 ( 207 expanded)
%              Number of equality atoms :   71 ( 130 expanded)
%              Maximal formula depth    :   12 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_7 > #skF_5 > #skF_2 > #skF_6 > #skF_4 > #skF_3 > #skF_1

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

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

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

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_123,negated_conjecture,(
    ~ ! [A,B] :
        ( k4_xboole_0(k1_tarski(A),B) = k1_tarski(A)
      <=> ~ r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_zfmisc_1)).

tff(f_113,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_71,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_115,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_59,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_57,axiom,(
    ! [A,B] : k2_xboole_0(A,k2_xboole_0(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_xboole_1)).

tff(f_53,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_51,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_67,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_117,axiom,(
    ! [A] : k3_tarski(k1_tarski(A)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_zfmisc_1)).

tff(f_96,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_29,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_69,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_xboole_1)).

tff(f_65,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_49,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => k4_xboole_0(k2_xboole_0(A,B),B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_xboole_1)).

tff(f_98,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_86,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

tff(c_88,plain,
    ( ~ r2_hidden('#skF_4','#skF_5')
    | r2_hidden('#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_172,plain,(
    ~ r2_hidden('#skF_4','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_88])).

tff(c_80,plain,(
    ! [A_89,B_90] :
      ( r1_xboole_0(k1_tarski(A_89),B_90)
      | r2_hidden(A_89,B_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_32,plain,(
    ! [B_31,A_30] : k2_tarski(B_31,A_30) = k2_tarski(A_30,B_31) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_235,plain,(
    ! [A_118,B_119] : k3_tarski(k2_tarski(A_118,B_119)) = k2_xboole_0(A_118,B_119) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_293,plain,(
    ! [A_128,B_129] : k3_tarski(k2_tarski(A_128,B_129)) = k2_xboole_0(B_129,A_128) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_235])).

tff(c_82,plain,(
    ! [A_91,B_92] : k3_tarski(k2_tarski(A_91,B_92)) = k2_xboole_0(A_91,B_92) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_299,plain,(
    ! [B_129,A_128] : k2_xboole_0(B_129,A_128) = k2_xboole_0(A_128,B_129) ),
    inference(superposition,[status(thm),theory(equality)],[c_293,c_82])).

tff(c_22,plain,(
    ! [A_20,B_21] : r1_xboole_0(k4_xboole_0(A_20,B_21),B_21) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_20,plain,(
    ! [A_18,B_19] : k2_xboole_0(A_18,k2_xboole_0(A_18,B_19)) = k2_xboole_0(A_18,B_19) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_16,plain,(
    ! [A_13,B_14] : k2_xboole_0(A_13,k4_xboole_0(B_14,A_13)) = k2_xboole_0(A_13,B_14) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_14,plain,(
    ! [A_12] : k2_xboole_0(A_12,k1_xboole_0) = A_12 ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_28,plain,(
    ! [A_27] : k5_xboole_0(A_27,A_27) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_2,plain,(
    ! [B_2,A_1] : k5_xboole_0(B_2,A_1) = k5_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_84,plain,(
    ! [A_93] : k3_tarski(k1_tarski(A_93)) = A_93 ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_66,plain,(
    ! [A_61] : k2_tarski(A_61,A_61) = k1_tarski(A_61) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_250,plain,(
    ! [A_61] : k3_tarski(k1_tarski(A_61)) = k2_xboole_0(A_61,A_61) ),
    inference(superposition,[status(thm),theory(equality)],[c_66,c_235])).

tff(c_253,plain,(
    ! [A_61] : k2_xboole_0(A_61,A_61) = A_61 ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_250])).

tff(c_4,plain,(
    ! [A_3] : k3_xboole_0(A_3,A_3) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_1382,plain,(
    ! [A_184,B_185] : k5_xboole_0(k5_xboole_0(A_184,B_185),k2_xboole_0(A_184,B_185)) = k3_xboole_0(A_184,B_185) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_1473,plain,(
    ! [A_27] : k5_xboole_0(k1_xboole_0,k2_xboole_0(A_27,A_27)) = k3_xboole_0(A_27,A_27) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_1382])).

tff(c_1480,plain,(
    ! [A_27] : k5_xboole_0(k1_xboole_0,A_27) = A_27 ),
    inference(demodulation,[status(thm),theory(equality)],[c_253,c_4,c_1473])).

tff(c_748,plain,(
    ! [A_161,B_162,C_163] : k5_xboole_0(k5_xboole_0(A_161,B_162),C_163) = k5_xboole_0(A_161,k5_xboole_0(B_162,C_163)) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_798,plain,(
    ! [A_27,C_163] : k5_xboole_0(A_27,k5_xboole_0(A_27,C_163)) = k5_xboole_0(k1_xboole_0,C_163) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_748])).

tff(c_1827,plain,(
    ! [A_198,C_199] : k5_xboole_0(A_198,k5_xboole_0(A_198,C_199)) = C_199 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1480,c_798])).

tff(c_1882,plain,(
    ! [B_2,A_1] : k5_xboole_0(B_2,k5_xboole_0(A_1,B_2)) = A_1 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_1827])).

tff(c_9617,plain,(
    ! [A_15578,B_15579] : k5_xboole_0(k2_xboole_0(A_15578,B_15579),k5_xboole_0(A_15578,B_15579)) = k3_xboole_0(A_15578,B_15579) ),
    inference(superposition,[status(thm),theory(equality)],[c_1382,c_2])).

tff(c_9757,plain,(
    ! [A_18,B_19] : k5_xboole_0(k2_xboole_0(A_18,B_19),k5_xboole_0(A_18,k2_xboole_0(A_18,B_19))) = k3_xboole_0(A_18,k2_xboole_0(A_18,B_19)) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_9617])).

tff(c_9817,plain,(
    ! [A_15745,B_15746] : k3_xboole_0(A_15745,k2_xboole_0(A_15745,B_15746)) = A_15745 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1882,c_9757])).

tff(c_9982,plain,(
    ! [A_16079,B_16080] : k3_xboole_0(A_16079,k2_xboole_0(B_16080,A_16079)) = A_16079 ),
    inference(superposition,[status(thm),theory(equality)],[c_299,c_9817])).

tff(c_12,plain,(
    ! [A_10,B_11] : k5_xboole_0(A_10,k3_xboole_0(A_10,B_11)) = k4_xboole_0(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_10005,plain,(
    ! [A_16079,B_16080] : k4_xboole_0(A_16079,k2_xboole_0(B_16080,A_16079)) = k5_xboole_0(A_16079,A_16079) ),
    inference(superposition,[status(thm),theory(equality)],[c_9982,c_12])).

tff(c_10192,plain,(
    ! [A_16414,B_16415] : k4_xboole_0(A_16414,k2_xboole_0(B_16415,A_16414)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_10005])).

tff(c_10218,plain,(
    ! [B_16415,A_16414] : k2_xboole_0(k2_xboole_0(B_16415,A_16414),k1_xboole_0) = k2_xboole_0(k2_xboole_0(B_16415,A_16414),A_16414) ),
    inference(superposition,[status(thm),theory(equality)],[c_10192,c_16])).

tff(c_11557,plain,(
    ! [B_17922,A_17923] : k2_xboole_0(k2_xboole_0(B_17922,A_17923),A_17923) = k2_xboole_0(B_17922,A_17923) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_10218])).

tff(c_12701,plain,(
    ! [A_18926,B_18927] : k2_xboole_0(A_18926,k2_xboole_0(B_18927,A_18926)) = k2_xboole_0(B_18927,A_18926) ),
    inference(superposition,[status(thm),theory(equality)],[c_299,c_11557])).

tff(c_13594,plain,(
    ! [B_19595,A_19596] : k2_xboole_0(B_19595,k2_xboole_0(B_19595,A_19596)) = k2_xboole_0(A_19596,B_19595) ),
    inference(superposition,[status(thm),theory(equality)],[c_299,c_12701])).

tff(c_13781,plain,(
    ! [B_14,A_13] : k2_xboole_0(k4_xboole_0(B_14,A_13),A_13) = k2_xboole_0(A_13,k2_xboole_0(A_13,B_14)) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_13594])).

tff(c_13858,plain,(
    ! [B_19762,A_19763] : k2_xboole_0(k4_xboole_0(B_19762,A_19763),A_19763) = k2_xboole_0(A_19763,B_19762) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_13781])).

tff(c_24,plain,(
    ! [A_22,B_23] :
      ( k4_xboole_0(k2_xboole_0(A_22,B_23),B_23) = A_22
      | ~ r1_xboole_0(A_22,B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_13968,plain,(
    ! [A_19763,B_19762] :
      ( k4_xboole_0(k2_xboole_0(A_19763,B_19762),A_19763) = k4_xboole_0(B_19762,A_19763)
      | ~ r1_xboole_0(k4_xboole_0(B_19762,A_19763),A_19763) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_13858,c_24])).

tff(c_14281,plain,(
    ! [A_20097,B_20098] : k4_xboole_0(k2_xboole_0(A_20097,B_20098),A_20097) = k4_xboole_0(B_20098,A_20097) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_13968])).

tff(c_14387,plain,(
    ! [A_128,B_129] : k4_xboole_0(k2_xboole_0(A_128,B_129),B_129) = k4_xboole_0(A_128,B_129) ),
    inference(superposition,[status(thm),theory(equality)],[c_299,c_14281])).

tff(c_15692,plain,(
    ! [A_21934,B_21935] :
      ( k4_xboole_0(A_21934,B_21935) = A_21934
      | ~ r1_xboole_0(A_21934,B_21935) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14387,c_24])).

tff(c_25486,plain,(
    ! [A_30300,B_30301] :
      ( k4_xboole_0(k1_tarski(A_30300),B_30301) = k1_tarski(A_30300)
      | r2_hidden(A_30300,B_30301) ) ),
    inference(resolution,[status(thm)],[c_80,c_15692])).

tff(c_86,plain,
    ( k4_xboole_0(k1_tarski('#skF_4'),'#skF_5') != k1_tarski('#skF_4')
    | r2_hidden('#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_287,plain,(
    k4_xboole_0(k1_tarski('#skF_4'),'#skF_5') != k1_tarski('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_86])).

tff(c_25618,plain,(
    r2_hidden('#skF_4','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_25486,c_287])).

tff(c_25693,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_172,c_25618])).

tff(c_25694,plain,(
    r2_hidden('#skF_6','#skF_7') ),
    inference(splitRight,[status(thm)],[c_86])).

tff(c_207,plain,(
    ! [A_114,B_115] : k1_enumset1(A_114,A_114,B_115) = k2_tarski(A_114,B_115) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_40,plain,(
    ! [E_38,B_33,C_34] : r2_hidden(E_38,k1_enumset1(E_38,B_33,C_34)) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_225,plain,(
    ! [A_116,B_117] : r2_hidden(A_116,k2_tarski(A_116,B_117)) ),
    inference(superposition,[status(thm),theory(equality)],[c_207,c_40])).

tff(c_234,plain,(
    ! [A_61] : r2_hidden(A_61,k1_tarski(A_61)) ),
    inference(superposition,[status(thm),theory(equality)],[c_66,c_225])).

tff(c_25695,plain,(
    k4_xboole_0(k1_tarski('#skF_4'),'#skF_5') = k1_tarski('#skF_4') ),
    inference(splitRight,[status(thm)],[c_86])).

tff(c_90,plain,
    ( k4_xboole_0(k1_tarski('#skF_4'),'#skF_5') != k1_tarski('#skF_4')
    | k4_xboole_0(k1_tarski('#skF_6'),'#skF_7') = k1_tarski('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_25857,plain,(
    k4_xboole_0(k1_tarski('#skF_6'),'#skF_7') = k1_tarski('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_25695,c_90])).

tff(c_25861,plain,(
    r1_xboole_0(k1_tarski('#skF_6'),'#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_25857,c_22])).

tff(c_25947,plain,(
    ! [A_30486,B_30487,C_30488] :
      ( ~ r1_xboole_0(A_30486,B_30487)
      | ~ r2_hidden(C_30488,B_30487)
      | ~ r2_hidden(C_30488,A_30486) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_25994,plain,(
    ! [C_30491] :
      ( ~ r2_hidden(C_30491,'#skF_7')
      | ~ r2_hidden(C_30491,k1_tarski('#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_25861,c_25947])).

tff(c_26006,plain,(
    ~ r2_hidden('#skF_6','#skF_7') ),
    inference(resolution,[status(thm)],[c_234,c_25994])).

tff(c_26012,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_25694,c_26006])).

tff(c_26013,plain,(
    r2_hidden('#skF_6','#skF_7') ),
    inference(splitRight,[status(thm)],[c_88])).

tff(c_26049,plain,(
    ! [A_30497,B_30498] : k1_enumset1(A_30497,A_30497,B_30498) = k2_tarski(A_30497,B_30498) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_26105,plain,(
    ! [A_30502,B_30503] : r2_hidden(A_30502,k2_tarski(A_30502,B_30503)) ),
    inference(superposition,[status(thm),theory(equality)],[c_26049,c_40])).

tff(c_26114,plain,(
    ! [A_61] : r2_hidden(A_61,k1_tarski(A_61)) ),
    inference(superposition,[status(thm),theory(equality)],[c_66,c_26105])).

tff(c_26014,plain,(
    r2_hidden('#skF_4','#skF_5') ),
    inference(splitRight,[status(thm)],[c_88])).

tff(c_92,plain,
    ( ~ r2_hidden('#skF_4','#skF_5')
    | k4_xboole_0(k1_tarski('#skF_6'),'#skF_7') = k1_tarski('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_26257,plain,(
    k4_xboole_0(k1_tarski('#skF_6'),'#skF_7') = k1_tarski('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26014,c_92])).

tff(c_26261,plain,(
    r1_xboole_0(k1_tarski('#skF_6'),'#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_26257,c_22])).

tff(c_26398,plain,(
    ! [A_30528,B_30529,C_30530] :
      ( ~ r1_xboole_0(A_30528,B_30529)
      | ~ r2_hidden(C_30530,B_30529)
      | ~ r2_hidden(C_30530,A_30528) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_26468,plain,(
    ! [C_30537] :
      ( ~ r2_hidden(C_30537,'#skF_7')
      | ~ r2_hidden(C_30537,k1_tarski('#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_26261,c_26398])).

tff(c_26480,plain,(
    ~ r2_hidden('#skF_6','#skF_7') ),
    inference(resolution,[status(thm)],[c_26114,c_26468])).

tff(c_26486,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26013,c_26480])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:22:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 11.60/4.68  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.60/4.69  
% 11.60/4.69  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.60/4.70  %$ r2_hidden > r1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_7 > #skF_5 > #skF_2 > #skF_6 > #skF_4 > #skF_3 > #skF_1
% 11.60/4.70  
% 11.60/4.70  %Foreground sorts:
% 11.60/4.70  
% 11.60/4.70  
% 11.60/4.70  %Background operators:
% 11.60/4.70  
% 11.60/4.70  
% 11.60/4.70  %Foreground operators:
% 11.60/4.70  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 11.60/4.70  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 11.60/4.70  tff(k1_tarski, type, k1_tarski: $i > $i).
% 11.60/4.70  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 11.60/4.70  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 11.60/4.70  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 11.60/4.70  tff('#skF_7', type, '#skF_7': $i).
% 11.60/4.70  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 11.60/4.70  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 11.60/4.70  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 11.60/4.70  tff('#skF_5', type, '#skF_5': $i).
% 11.60/4.70  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 11.60/4.70  tff('#skF_6', type, '#skF_6': $i).
% 11.60/4.70  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 11.60/4.70  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 11.60/4.70  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 11.60/4.70  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 11.60/4.70  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 11.60/4.70  tff(k3_tarski, type, k3_tarski: $i > $i).
% 11.60/4.70  tff('#skF_4', type, '#skF_4': $i).
% 11.60/4.70  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 11.60/4.70  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 11.60/4.70  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 11.60/4.70  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 11.60/4.70  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 11.60/4.70  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 11.60/4.70  
% 11.91/4.71  tff(f_123, negated_conjecture, ~(![A, B]: ((k4_xboole_0(k1_tarski(A), B) = k1_tarski(A)) <=> ~r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t67_zfmisc_1)).
% 11.91/4.71  tff(f_113, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 11.91/4.71  tff(f_71, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 11.91/4.71  tff(f_115, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 11.91/4.71  tff(f_59, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_xboole_1)).
% 11.91/4.71  tff(f_57, axiom, (![A, B]: (k2_xboole_0(A, k2_xboole_0(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_xboole_1)).
% 11.91/4.71  tff(f_53, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 11.91/4.71  tff(f_51, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 11.91/4.71  tff(f_67, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_xboole_1)).
% 11.91/4.71  tff(f_27, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 11.91/4.71  tff(f_117, axiom, (![A]: (k3_tarski(k1_tarski(A)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_zfmisc_1)).
% 11.91/4.71  tff(f_96, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 11.91/4.71  tff(f_29, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 11.91/4.71  tff(f_69, axiom, (![A, B]: (k3_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k2_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t95_xboole_1)).
% 11.91/4.71  tff(f_65, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_xboole_1)).
% 11.91/4.71  tff(f_49, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 11.91/4.71  tff(f_63, axiom, (![A, B]: (r1_xboole_0(A, B) => (k4_xboole_0(k2_xboole_0(A, B), B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t88_xboole_1)).
% 11.91/4.71  tff(f_98, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 11.91/4.71  tff(f_86, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 11.91/4.71  tff(f_47, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 11.91/4.71  tff(c_88, plain, (~r2_hidden('#skF_4', '#skF_5') | r2_hidden('#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_123])).
% 11.91/4.71  tff(c_172, plain, (~r2_hidden('#skF_4', '#skF_5')), inference(splitLeft, [status(thm)], [c_88])).
% 11.91/4.71  tff(c_80, plain, (![A_89, B_90]: (r1_xboole_0(k1_tarski(A_89), B_90) | r2_hidden(A_89, B_90))), inference(cnfTransformation, [status(thm)], [f_113])).
% 11.91/4.71  tff(c_32, plain, (![B_31, A_30]: (k2_tarski(B_31, A_30)=k2_tarski(A_30, B_31))), inference(cnfTransformation, [status(thm)], [f_71])).
% 11.91/4.71  tff(c_235, plain, (![A_118, B_119]: (k3_tarski(k2_tarski(A_118, B_119))=k2_xboole_0(A_118, B_119))), inference(cnfTransformation, [status(thm)], [f_115])).
% 11.91/4.71  tff(c_293, plain, (![A_128, B_129]: (k3_tarski(k2_tarski(A_128, B_129))=k2_xboole_0(B_129, A_128))), inference(superposition, [status(thm), theory('equality')], [c_32, c_235])).
% 11.91/4.71  tff(c_82, plain, (![A_91, B_92]: (k3_tarski(k2_tarski(A_91, B_92))=k2_xboole_0(A_91, B_92))), inference(cnfTransformation, [status(thm)], [f_115])).
% 11.91/4.71  tff(c_299, plain, (![B_129, A_128]: (k2_xboole_0(B_129, A_128)=k2_xboole_0(A_128, B_129))), inference(superposition, [status(thm), theory('equality')], [c_293, c_82])).
% 11.91/4.71  tff(c_22, plain, (![A_20, B_21]: (r1_xboole_0(k4_xboole_0(A_20, B_21), B_21))), inference(cnfTransformation, [status(thm)], [f_59])).
% 11.91/4.71  tff(c_20, plain, (![A_18, B_19]: (k2_xboole_0(A_18, k2_xboole_0(A_18, B_19))=k2_xboole_0(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_57])).
% 11.91/4.71  tff(c_16, plain, (![A_13, B_14]: (k2_xboole_0(A_13, k4_xboole_0(B_14, A_13))=k2_xboole_0(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_53])).
% 11.91/4.71  tff(c_14, plain, (![A_12]: (k2_xboole_0(A_12, k1_xboole_0)=A_12)), inference(cnfTransformation, [status(thm)], [f_51])).
% 11.91/4.71  tff(c_28, plain, (![A_27]: (k5_xboole_0(A_27, A_27)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_67])).
% 11.91/4.71  tff(c_2, plain, (![B_2, A_1]: (k5_xboole_0(B_2, A_1)=k5_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 11.91/4.71  tff(c_84, plain, (![A_93]: (k3_tarski(k1_tarski(A_93))=A_93)), inference(cnfTransformation, [status(thm)], [f_117])).
% 11.91/4.71  tff(c_66, plain, (![A_61]: (k2_tarski(A_61, A_61)=k1_tarski(A_61))), inference(cnfTransformation, [status(thm)], [f_96])).
% 11.91/4.71  tff(c_250, plain, (![A_61]: (k3_tarski(k1_tarski(A_61))=k2_xboole_0(A_61, A_61))), inference(superposition, [status(thm), theory('equality')], [c_66, c_235])).
% 11.91/4.71  tff(c_253, plain, (![A_61]: (k2_xboole_0(A_61, A_61)=A_61)), inference(demodulation, [status(thm), theory('equality')], [c_84, c_250])).
% 11.91/4.71  tff(c_4, plain, (![A_3]: (k3_xboole_0(A_3, A_3)=A_3)), inference(cnfTransformation, [status(thm)], [f_29])).
% 11.91/4.71  tff(c_1382, plain, (![A_184, B_185]: (k5_xboole_0(k5_xboole_0(A_184, B_185), k2_xboole_0(A_184, B_185))=k3_xboole_0(A_184, B_185))), inference(cnfTransformation, [status(thm)], [f_69])).
% 11.91/4.71  tff(c_1473, plain, (![A_27]: (k5_xboole_0(k1_xboole_0, k2_xboole_0(A_27, A_27))=k3_xboole_0(A_27, A_27))), inference(superposition, [status(thm), theory('equality')], [c_28, c_1382])).
% 11.91/4.71  tff(c_1480, plain, (![A_27]: (k5_xboole_0(k1_xboole_0, A_27)=A_27)), inference(demodulation, [status(thm), theory('equality')], [c_253, c_4, c_1473])).
% 11.91/4.71  tff(c_748, plain, (![A_161, B_162, C_163]: (k5_xboole_0(k5_xboole_0(A_161, B_162), C_163)=k5_xboole_0(A_161, k5_xboole_0(B_162, C_163)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 11.91/4.71  tff(c_798, plain, (![A_27, C_163]: (k5_xboole_0(A_27, k5_xboole_0(A_27, C_163))=k5_xboole_0(k1_xboole_0, C_163))), inference(superposition, [status(thm), theory('equality')], [c_28, c_748])).
% 11.91/4.71  tff(c_1827, plain, (![A_198, C_199]: (k5_xboole_0(A_198, k5_xboole_0(A_198, C_199))=C_199)), inference(demodulation, [status(thm), theory('equality')], [c_1480, c_798])).
% 11.91/4.71  tff(c_1882, plain, (![B_2, A_1]: (k5_xboole_0(B_2, k5_xboole_0(A_1, B_2))=A_1)), inference(superposition, [status(thm), theory('equality')], [c_2, c_1827])).
% 11.91/4.71  tff(c_9617, plain, (![A_15578, B_15579]: (k5_xboole_0(k2_xboole_0(A_15578, B_15579), k5_xboole_0(A_15578, B_15579))=k3_xboole_0(A_15578, B_15579))), inference(superposition, [status(thm), theory('equality')], [c_1382, c_2])).
% 11.91/4.71  tff(c_9757, plain, (![A_18, B_19]: (k5_xboole_0(k2_xboole_0(A_18, B_19), k5_xboole_0(A_18, k2_xboole_0(A_18, B_19)))=k3_xboole_0(A_18, k2_xboole_0(A_18, B_19)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_9617])).
% 11.91/4.71  tff(c_9817, plain, (![A_15745, B_15746]: (k3_xboole_0(A_15745, k2_xboole_0(A_15745, B_15746))=A_15745)), inference(demodulation, [status(thm), theory('equality')], [c_1882, c_9757])).
% 11.91/4.71  tff(c_9982, plain, (![A_16079, B_16080]: (k3_xboole_0(A_16079, k2_xboole_0(B_16080, A_16079))=A_16079)), inference(superposition, [status(thm), theory('equality')], [c_299, c_9817])).
% 11.91/4.71  tff(c_12, plain, (![A_10, B_11]: (k5_xboole_0(A_10, k3_xboole_0(A_10, B_11))=k4_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_49])).
% 11.91/4.71  tff(c_10005, plain, (![A_16079, B_16080]: (k4_xboole_0(A_16079, k2_xboole_0(B_16080, A_16079))=k5_xboole_0(A_16079, A_16079))), inference(superposition, [status(thm), theory('equality')], [c_9982, c_12])).
% 11.91/4.71  tff(c_10192, plain, (![A_16414, B_16415]: (k4_xboole_0(A_16414, k2_xboole_0(B_16415, A_16414))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_28, c_10005])).
% 11.91/4.71  tff(c_10218, plain, (![B_16415, A_16414]: (k2_xboole_0(k2_xboole_0(B_16415, A_16414), k1_xboole_0)=k2_xboole_0(k2_xboole_0(B_16415, A_16414), A_16414))), inference(superposition, [status(thm), theory('equality')], [c_10192, c_16])).
% 11.91/4.71  tff(c_11557, plain, (![B_17922, A_17923]: (k2_xboole_0(k2_xboole_0(B_17922, A_17923), A_17923)=k2_xboole_0(B_17922, A_17923))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_10218])).
% 11.91/4.71  tff(c_12701, plain, (![A_18926, B_18927]: (k2_xboole_0(A_18926, k2_xboole_0(B_18927, A_18926))=k2_xboole_0(B_18927, A_18926))), inference(superposition, [status(thm), theory('equality')], [c_299, c_11557])).
% 11.91/4.71  tff(c_13594, plain, (![B_19595, A_19596]: (k2_xboole_0(B_19595, k2_xboole_0(B_19595, A_19596))=k2_xboole_0(A_19596, B_19595))), inference(superposition, [status(thm), theory('equality')], [c_299, c_12701])).
% 11.91/4.71  tff(c_13781, plain, (![B_14, A_13]: (k2_xboole_0(k4_xboole_0(B_14, A_13), A_13)=k2_xboole_0(A_13, k2_xboole_0(A_13, B_14)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_13594])).
% 11.91/4.71  tff(c_13858, plain, (![B_19762, A_19763]: (k2_xboole_0(k4_xboole_0(B_19762, A_19763), A_19763)=k2_xboole_0(A_19763, B_19762))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_13781])).
% 11.91/4.71  tff(c_24, plain, (![A_22, B_23]: (k4_xboole_0(k2_xboole_0(A_22, B_23), B_23)=A_22 | ~r1_xboole_0(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_63])).
% 11.91/4.71  tff(c_13968, plain, (![A_19763, B_19762]: (k4_xboole_0(k2_xboole_0(A_19763, B_19762), A_19763)=k4_xboole_0(B_19762, A_19763) | ~r1_xboole_0(k4_xboole_0(B_19762, A_19763), A_19763))), inference(superposition, [status(thm), theory('equality')], [c_13858, c_24])).
% 11.91/4.71  tff(c_14281, plain, (![A_20097, B_20098]: (k4_xboole_0(k2_xboole_0(A_20097, B_20098), A_20097)=k4_xboole_0(B_20098, A_20097))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_13968])).
% 11.91/4.71  tff(c_14387, plain, (![A_128, B_129]: (k4_xboole_0(k2_xboole_0(A_128, B_129), B_129)=k4_xboole_0(A_128, B_129))), inference(superposition, [status(thm), theory('equality')], [c_299, c_14281])).
% 11.91/4.71  tff(c_15692, plain, (![A_21934, B_21935]: (k4_xboole_0(A_21934, B_21935)=A_21934 | ~r1_xboole_0(A_21934, B_21935))), inference(demodulation, [status(thm), theory('equality')], [c_14387, c_24])).
% 11.91/4.71  tff(c_25486, plain, (![A_30300, B_30301]: (k4_xboole_0(k1_tarski(A_30300), B_30301)=k1_tarski(A_30300) | r2_hidden(A_30300, B_30301))), inference(resolution, [status(thm)], [c_80, c_15692])).
% 11.91/4.71  tff(c_86, plain, (k4_xboole_0(k1_tarski('#skF_4'), '#skF_5')!=k1_tarski('#skF_4') | r2_hidden('#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_123])).
% 11.91/4.71  tff(c_287, plain, (k4_xboole_0(k1_tarski('#skF_4'), '#skF_5')!=k1_tarski('#skF_4')), inference(splitLeft, [status(thm)], [c_86])).
% 11.91/4.71  tff(c_25618, plain, (r2_hidden('#skF_4', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_25486, c_287])).
% 11.91/4.71  tff(c_25693, plain, $false, inference(negUnitSimplification, [status(thm)], [c_172, c_25618])).
% 11.91/4.71  tff(c_25694, plain, (r2_hidden('#skF_6', '#skF_7')), inference(splitRight, [status(thm)], [c_86])).
% 11.91/4.71  tff(c_207, plain, (![A_114, B_115]: (k1_enumset1(A_114, A_114, B_115)=k2_tarski(A_114, B_115))), inference(cnfTransformation, [status(thm)], [f_98])).
% 11.91/4.71  tff(c_40, plain, (![E_38, B_33, C_34]: (r2_hidden(E_38, k1_enumset1(E_38, B_33, C_34)))), inference(cnfTransformation, [status(thm)], [f_86])).
% 11.91/4.71  tff(c_225, plain, (![A_116, B_117]: (r2_hidden(A_116, k2_tarski(A_116, B_117)))), inference(superposition, [status(thm), theory('equality')], [c_207, c_40])).
% 11.91/4.71  tff(c_234, plain, (![A_61]: (r2_hidden(A_61, k1_tarski(A_61)))), inference(superposition, [status(thm), theory('equality')], [c_66, c_225])).
% 11.91/4.71  tff(c_25695, plain, (k4_xboole_0(k1_tarski('#skF_4'), '#skF_5')=k1_tarski('#skF_4')), inference(splitRight, [status(thm)], [c_86])).
% 11.91/4.71  tff(c_90, plain, (k4_xboole_0(k1_tarski('#skF_4'), '#skF_5')!=k1_tarski('#skF_4') | k4_xboole_0(k1_tarski('#skF_6'), '#skF_7')=k1_tarski('#skF_6')), inference(cnfTransformation, [status(thm)], [f_123])).
% 11.91/4.71  tff(c_25857, plain, (k4_xboole_0(k1_tarski('#skF_6'), '#skF_7')=k1_tarski('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_25695, c_90])).
% 11.91/4.71  tff(c_25861, plain, (r1_xboole_0(k1_tarski('#skF_6'), '#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_25857, c_22])).
% 11.91/4.71  tff(c_25947, plain, (![A_30486, B_30487, C_30488]: (~r1_xboole_0(A_30486, B_30487) | ~r2_hidden(C_30488, B_30487) | ~r2_hidden(C_30488, A_30486))), inference(cnfTransformation, [status(thm)], [f_47])).
% 11.91/4.71  tff(c_25994, plain, (![C_30491]: (~r2_hidden(C_30491, '#skF_7') | ~r2_hidden(C_30491, k1_tarski('#skF_6')))), inference(resolution, [status(thm)], [c_25861, c_25947])).
% 11.91/4.71  tff(c_26006, plain, (~r2_hidden('#skF_6', '#skF_7')), inference(resolution, [status(thm)], [c_234, c_25994])).
% 11.91/4.71  tff(c_26012, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_25694, c_26006])).
% 11.91/4.71  tff(c_26013, plain, (r2_hidden('#skF_6', '#skF_7')), inference(splitRight, [status(thm)], [c_88])).
% 11.91/4.71  tff(c_26049, plain, (![A_30497, B_30498]: (k1_enumset1(A_30497, A_30497, B_30498)=k2_tarski(A_30497, B_30498))), inference(cnfTransformation, [status(thm)], [f_98])).
% 11.91/4.71  tff(c_26105, plain, (![A_30502, B_30503]: (r2_hidden(A_30502, k2_tarski(A_30502, B_30503)))), inference(superposition, [status(thm), theory('equality')], [c_26049, c_40])).
% 11.91/4.71  tff(c_26114, plain, (![A_61]: (r2_hidden(A_61, k1_tarski(A_61)))), inference(superposition, [status(thm), theory('equality')], [c_66, c_26105])).
% 11.91/4.71  tff(c_26014, plain, (r2_hidden('#skF_4', '#skF_5')), inference(splitRight, [status(thm)], [c_88])).
% 11.91/4.71  tff(c_92, plain, (~r2_hidden('#skF_4', '#skF_5') | k4_xboole_0(k1_tarski('#skF_6'), '#skF_7')=k1_tarski('#skF_6')), inference(cnfTransformation, [status(thm)], [f_123])).
% 11.91/4.71  tff(c_26257, plain, (k4_xboole_0(k1_tarski('#skF_6'), '#skF_7')=k1_tarski('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_26014, c_92])).
% 11.91/4.71  tff(c_26261, plain, (r1_xboole_0(k1_tarski('#skF_6'), '#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_26257, c_22])).
% 11.91/4.71  tff(c_26398, plain, (![A_30528, B_30529, C_30530]: (~r1_xboole_0(A_30528, B_30529) | ~r2_hidden(C_30530, B_30529) | ~r2_hidden(C_30530, A_30528))), inference(cnfTransformation, [status(thm)], [f_47])).
% 11.91/4.71  tff(c_26468, plain, (![C_30537]: (~r2_hidden(C_30537, '#skF_7') | ~r2_hidden(C_30537, k1_tarski('#skF_6')))), inference(resolution, [status(thm)], [c_26261, c_26398])).
% 11.91/4.71  tff(c_26480, plain, (~r2_hidden('#skF_6', '#skF_7')), inference(resolution, [status(thm)], [c_26114, c_26468])).
% 11.91/4.71  tff(c_26486, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26013, c_26480])).
% 11.91/4.71  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.91/4.71  
% 11.91/4.71  Inference rules
% 11.91/4.71  ----------------------
% 11.91/4.71  #Ref     : 0
% 11.91/4.71  #Sup     : 5590
% 11.91/4.71  #Fact    : 18
% 11.91/4.71  #Define  : 0
% 11.91/4.71  #Split   : 2
% 11.91/4.71  #Chain   : 0
% 11.91/4.71  #Close   : 0
% 11.91/4.71  
% 11.91/4.71  Ordering : KBO
% 11.91/4.71  
% 11.91/4.71  Simplification rules
% 11.91/4.71  ----------------------
% 11.91/4.71  #Subsume      : 515
% 11.91/4.71  #Demod        : 6252
% 11.91/4.71  #Tautology    : 3086
% 11.91/4.71  #SimpNegUnit  : 17
% 11.91/4.71  #BackRed      : 7
% 11.91/4.71  
% 11.91/4.71  #Partial instantiations: 11403
% 11.91/4.72  #Strategies tried      : 1
% 11.91/4.72  
% 11.91/4.72  Timing (in seconds)
% 11.91/4.72  ----------------------
% 11.91/4.72  Preprocessing        : 0.47
% 11.91/4.72  Parsing              : 0.25
% 11.91/4.72  CNF conversion       : 0.03
% 11.91/4.72  Main loop            : 3.39
% 11.91/4.72  Inferencing          : 1.02
% 11.91/4.72  Reduction            : 1.69
% 11.91/4.72  Demodulation         : 1.51
% 11.91/4.72  BG Simplification    : 0.10
% 11.91/4.72  Subsumption          : 0.43
% 11.91/4.72  Abstraction          : 0.15
% 11.91/4.72  MUC search           : 0.00
% 11.91/4.72  Cooper               : 0.00
% 11.91/4.72  Total                : 3.91
% 11.91/4.72  Index Insertion      : 0.00
% 11.91/4.72  Index Deletion       : 0.00
% 11.91/4.72  Index Matching       : 0.00
% 11.91/4.72  BG Taut test         : 0.00
%------------------------------------------------------------------------------

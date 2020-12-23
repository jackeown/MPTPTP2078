%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:49:46 EST 2020

% Result     : Theorem 6.28s
% Output     : CNFRefutation 6.28s
% Verified   : 
% Statistics : Number of formulae       :  124 ( 564 expanded)
%              Number of leaves         :   44 ( 205 expanded)
%              Depth                    :   15
%              Number of atoms          :  143 ( 841 expanded)
%              Number of equality atoms :   89 ( 389 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_5 > #skF_6 > #skF_4 > #skF_3 > #skF_1

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

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

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

tff(f_84,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_112,axiom,(
    ! [A] : k3_tarski(k1_tarski(A)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_zfmisc_1)).

tff(f_100,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_86,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_82,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_110,axiom,(
    ! [A,B] :
      ( A != B
     => k5_xboole_0(k1_tarski(A),k1_tarski(B)) = k2_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_zfmisc_1)).

tff(f_105,axiom,(
    ! [A,B] :
      ( A != B
     => r1_xboole_0(k1_tarski(A),k1_tarski(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_zfmisc_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_67,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_115,negated_conjecture,(
    ~ ! [A,B] : k3_tarski(k2_tarski(k1_tarski(A),k1_tarski(B))) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_zfmisc_1)).

tff(f_61,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_51,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_43,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_53,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_59,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_98,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => k3_xboole_0(B,k1_tarski(A)) = k1_tarski(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l31_zfmisc_1)).

tff(c_50,plain,(
    ! [A_31] : k2_tarski(A_31,A_31) = k1_tarski(A_31) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_70,plain,(
    ! [A_60] : k3_tarski(k1_tarski(A_60)) = A_60 ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_145,plain,(
    ! [A_82,B_83] : k3_tarski(k2_tarski(A_82,B_83)) = k2_xboole_0(A_82,B_83) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_154,plain,(
    ! [A_31] : k3_tarski(k1_tarski(A_31)) = k2_xboole_0(A_31,A_31) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_145])).

tff(c_157,plain,(
    ! [A_31] : k2_xboole_0(A_31,A_31) = A_31 ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_154])).

tff(c_167,plain,(
    ! [A_85,B_86] : k1_enumset1(A_85,A_85,B_86) = k2_tarski(A_85,B_86) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_30,plain,(
    ! [E_30,A_24,C_26] : r2_hidden(E_30,k1_enumset1(A_24,E_30,C_26)) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_186,plain,(
    ! [A_89,B_90] : r2_hidden(A_89,k2_tarski(A_89,B_90)) ),
    inference(superposition,[status(thm),theory(equality)],[c_167,c_30])).

tff(c_189,plain,(
    ! [A_31] : r2_hidden(A_31,k1_tarski(A_31)) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_186])).

tff(c_68,plain,(
    ! [A_58,B_59] :
      ( k5_xboole_0(k1_tarski(A_58),k1_tarski(B_59)) = k2_tarski(A_58,B_59)
      | B_59 = A_58 ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_66,plain,(
    ! [A_56,B_57] :
      ( r1_xboole_0(k1_tarski(A_56),k1_tarski(B_57))
      | B_57 = A_56 ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_198,plain,(
    ! [A_96,B_97] :
      ( k4_xboole_0(A_96,B_97) = A_96
      | ~ r1_xboole_0(A_96,B_97) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_1918,plain,(
    ! [A_237,B_238] :
      ( k4_xboole_0(k1_tarski(A_237),k1_tarski(B_238)) = k1_tarski(A_237)
      | B_238 = A_237 ) ),
    inference(resolution,[status(thm)],[c_66,c_198])).

tff(c_24,plain,(
    ! [A_22,B_23] : k5_xboole_0(A_22,k4_xboole_0(B_23,A_22)) = k2_xboole_0(A_22,B_23) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_8106,plain,(
    ! [B_386,A_387] :
      ( k5_xboole_0(k1_tarski(B_386),k1_tarski(A_387)) = k2_xboole_0(k1_tarski(B_386),k1_tarski(A_387))
      | B_386 = A_387 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1918,c_24])).

tff(c_8986,plain,(
    ! [A_418,B_419] :
      ( k2_xboole_0(k1_tarski(A_418),k1_tarski(B_419)) = k2_tarski(A_418,B_419)
      | B_419 = A_418
      | B_419 = A_418 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_68,c_8106])).

tff(c_64,plain,(
    ! [A_54,B_55] : k3_tarski(k2_tarski(A_54,B_55)) = k2_xboole_0(A_54,B_55) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_72,plain,(
    k3_tarski(k2_tarski(k1_tarski('#skF_5'),k1_tarski('#skF_6'))) != k2_tarski('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_73,plain,(
    k2_xboole_0(k1_tarski('#skF_5'),k1_tarski('#skF_6')) != k2_tarski('#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_72])).

tff(c_9014,plain,(
    '#skF_5' = '#skF_6' ),
    inference(superposition,[status(thm),theory(equality)],[c_8986,c_73])).

tff(c_18,plain,(
    ! [A_18,B_19] : r1_xboole_0(k4_xboole_0(A_18,B_19),B_19) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_10,plain,(
    ! [A_10] :
      ( r2_hidden('#skF_2'(A_10),A_10)
      | k1_xboole_0 = A_10 ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_247,plain,(
    ! [A_103,B_104,C_105] :
      ( ~ r1_xboole_0(A_103,B_104)
      | ~ r2_hidden(C_105,k3_xboole_0(A_103,B_104)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_272,plain,(
    ! [A_108,B_109] :
      ( ~ r1_xboole_0(A_108,B_109)
      | k3_xboole_0(A_108,B_109) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_10,c_247])).

tff(c_285,plain,(
    ! [A_110,B_111] : k3_xboole_0(k4_xboole_0(A_110,B_111),B_111) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_18,c_272])).

tff(c_8,plain,(
    ! [A_5,B_6,C_9] :
      ( ~ r1_xboole_0(A_5,B_6)
      | ~ r2_hidden(C_9,k3_xboole_0(A_5,B_6)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_290,plain,(
    ! [A_110,B_111,C_9] :
      ( ~ r1_xboole_0(k4_xboole_0(A_110,B_111),B_111)
      | ~ r2_hidden(C_9,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_285,c_8])).

tff(c_312,plain,(
    ! [C_9] : ~ r2_hidden(C_9,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_290])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_296,plain,(
    ! [B_111,A_110] : k3_xboole_0(B_111,k4_xboole_0(A_110,B_111)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_285,c_2])).

tff(c_421,plain,(
    ! [A_124,B_125] :
      ( r2_hidden('#skF_1'(A_124,B_125),k3_xboole_0(A_124,B_125))
      | r1_xboole_0(A_124,B_125) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_432,plain,(
    ! [B_111,A_110] :
      ( r2_hidden('#skF_1'(B_111,k4_xboole_0(A_110,B_111)),k1_xboole_0)
      | r1_xboole_0(B_111,k4_xboole_0(A_110,B_111)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_296,c_421])).

tff(c_450,plain,(
    ! [B_126,A_127] : r1_xboole_0(B_126,k4_xboole_0(A_127,B_126)) ),
    inference(negUnitSimplification,[status(thm)],[c_312,c_432])).

tff(c_20,plain,(
    ! [A_20,B_21] :
      ( k4_xboole_0(A_20,B_21) = A_20
      | ~ r1_xboole_0(A_20,B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_459,plain,(
    ! [B_126,A_127] : k4_xboole_0(B_126,k4_xboole_0(A_127,B_126)) = B_126 ),
    inference(resolution,[status(thm)],[c_450,c_20])).

tff(c_284,plain,(
    ! [A_18,B_19] : k3_xboole_0(k4_xboole_0(A_18,B_19),B_19) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_18,c_272])).

tff(c_220,plain,(
    ! [A_100,B_101] : k5_xboole_0(A_100,k3_xboole_0(A_100,B_101)) = k4_xboole_0(A_100,B_101) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_552,plain,(
    ! [B_133,A_134] : k5_xboole_0(B_133,k3_xboole_0(A_134,B_133)) = k4_xboole_0(B_133,A_134) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_220])).

tff(c_571,plain,(
    ! [B_19,A_18] : k4_xboole_0(B_19,k4_xboole_0(A_18,B_19)) = k5_xboole_0(B_19,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_284,c_552])).

tff(c_590,plain,(
    ! [B_19] : k5_xboole_0(B_19,k1_xboole_0) = B_19 ),
    inference(demodulation,[status(thm),theory(equality)],[c_459,c_571])).

tff(c_16,plain,(
    ! [A_16,B_17] : r1_tarski(k4_xboole_0(A_16,B_17),A_16) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_140,plain,(
    ! [A_80,B_81] :
      ( k3_xboole_0(A_80,B_81) = A_80
      | ~ r1_tarski(A_80,B_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_698,plain,(
    ! [A_142,B_143] : k3_xboole_0(k4_xboole_0(A_142,B_143),A_142) = k4_xboole_0(A_142,B_143) ),
    inference(resolution,[status(thm)],[c_16,c_140])).

tff(c_715,plain,(
    ! [A_142] : k4_xboole_0(A_142,A_142) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_698,c_284])).

tff(c_766,plain,(
    ! [A_144] : k4_xboole_0(A_144,A_144) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_698,c_284])).

tff(c_210,plain,(
    ! [A_18,B_19] : k4_xboole_0(k4_xboole_0(A_18,B_19),B_19) = k4_xboole_0(A_18,B_19) ),
    inference(resolution,[status(thm)],[c_18,c_198])).

tff(c_774,plain,(
    ! [A_144] : k4_xboole_0(k1_xboole_0,A_144) = k4_xboole_0(A_144,A_144) ),
    inference(superposition,[status(thm),theory(equality)],[c_766,c_210])).

tff(c_968,plain,(
    ! [A_160] : k4_xboole_0(k1_xboole_0,A_160) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_715,c_774])).

tff(c_998,plain,(
    ! [A_160] : k5_xboole_0(A_160,k1_xboole_0) = k2_xboole_0(A_160,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_968,c_24])).

tff(c_1021,plain,(
    ! [A_160] : k2_xboole_0(A_160,k1_xboole_0) = A_160 ),
    inference(demodulation,[status(thm),theory(equality)],[c_590,c_998])).

tff(c_4,plain,(
    ! [A_3] : k3_xboole_0(A_3,A_3) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_235,plain,(
    ! [A_3] : k5_xboole_0(A_3,A_3) = k4_xboole_0(A_3,A_3) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_220])).

tff(c_765,plain,(
    ! [A_3] : k5_xboole_0(A_3,A_3) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_715,c_235])).

tff(c_346,plain,(
    ! [B_118,A_119] :
      ( k3_xboole_0(B_118,k1_tarski(A_119)) = k1_tarski(A_119)
      | ~ r2_hidden(A_119,B_118) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_2093,plain,(
    ! [A_246,A_247] :
      ( k3_xboole_0(k1_tarski(A_246),A_247) = k1_tarski(A_246)
      | ~ r2_hidden(A_246,A_247) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_346])).

tff(c_12,plain,(
    ! [A_12,B_13] : k5_xboole_0(A_12,k3_xboole_0(A_12,B_13)) = k4_xboole_0(A_12,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_2131,plain,(
    ! [A_246,A_247] :
      ( k5_xboole_0(k1_tarski(A_246),k1_tarski(A_246)) = k4_xboole_0(k1_tarski(A_246),A_247)
      | ~ r2_hidden(A_246,A_247) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2093,c_12])).

tff(c_2208,plain,(
    ! [A_250,A_251] :
      ( k4_xboole_0(k1_tarski(A_250),A_251) = k1_xboole_0
      | ~ r2_hidden(A_250,A_251) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_765,c_2131])).

tff(c_503,plain,(
    ! [A_131,B_132] : k4_xboole_0(k4_xboole_0(A_131,B_132),B_132) = k4_xboole_0(A_131,B_132) ),
    inference(resolution,[status(thm)],[c_18,c_198])).

tff(c_524,plain,(
    ! [B_132,A_131] : k5_xboole_0(B_132,k4_xboole_0(A_131,B_132)) = k2_xboole_0(B_132,k4_xboole_0(A_131,B_132)) ),
    inference(superposition,[status(thm),theory(equality)],[c_503,c_24])).

tff(c_546,plain,(
    ! [B_132,A_131] : k2_xboole_0(B_132,k4_xboole_0(A_131,B_132)) = k2_xboole_0(B_132,A_131) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_524])).

tff(c_2239,plain,(
    ! [A_251,A_250] :
      ( k2_xboole_0(A_251,k1_tarski(A_250)) = k2_xboole_0(A_251,k1_xboole_0)
      | ~ r2_hidden(A_250,A_251) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2208,c_546])).

tff(c_2483,plain,(
    ! [A_254,A_255] :
      ( k2_xboole_0(A_254,k1_tarski(A_255)) = A_254
      | ~ r2_hidden(A_255,A_254) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1021,c_2239])).

tff(c_2493,plain,
    ( k2_tarski('#skF_5','#skF_6') != k1_tarski('#skF_5')
    | ~ r2_hidden('#skF_6',k1_tarski('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_2483,c_73])).

tff(c_2586,plain,(
    ~ r2_hidden('#skF_6',k1_tarski('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_2493])).

tff(c_9018,plain,(
    ~ r2_hidden('#skF_6',k1_tarski('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9014,c_2586])).

tff(c_9022,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_189,c_9018])).

tff(c_9024,plain,(
    r2_hidden('#skF_6',k1_tarski('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_2493])).

tff(c_22,plain,(
    ! [A_20,B_21] :
      ( r1_xboole_0(A_20,B_21)
      | k4_xboole_0(A_20,B_21) != A_20 ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_262,plain,(
    ! [A_106,C_107] :
      ( ~ r1_xboole_0(A_106,A_106)
      | ~ r2_hidden(C_107,A_106) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_247])).

tff(c_397,plain,(
    ! [C_120,B_121] :
      ( ~ r2_hidden(C_120,B_121)
      | k4_xboole_0(B_121,B_121) != B_121 ) ),
    inference(resolution,[status(thm)],[c_22,c_262])).

tff(c_413,plain,(
    ! [A_31] : k4_xboole_0(k1_tarski(A_31),k1_tarski(A_31)) != k1_tarski(A_31) ),
    inference(resolution,[status(thm)],[c_189,c_397])).

tff(c_762,plain,(
    ! [A_31] : k1_tarski(A_31) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_715,c_413])).

tff(c_1829,plain,(
    ! [A_233,B_234] :
      ( k3_xboole_0(k1_tarski(A_233),k1_tarski(B_234)) = k1_xboole_0
      | B_234 = A_233 ) ),
    inference(resolution,[status(thm)],[c_66,c_272])).

tff(c_62,plain,(
    ! [B_53,A_52] :
      ( k3_xboole_0(B_53,k1_tarski(A_52)) = k1_tarski(A_52)
      | ~ r2_hidden(A_52,B_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_1844,plain,(
    ! [B_234,A_233] :
      ( k1_tarski(B_234) = k1_xboole_0
      | ~ r2_hidden(B_234,k1_tarski(A_233))
      | B_234 = A_233 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1829,c_62])).

tff(c_1881,plain,(
    ! [B_234,A_233] :
      ( ~ r2_hidden(B_234,k1_tarski(A_233))
      | B_234 = A_233 ) ),
    inference(negUnitSimplification,[status(thm)],[c_762,c_1844])).

tff(c_9031,plain,(
    '#skF_5' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_9024,c_1881])).

tff(c_9034,plain,(
    k2_xboole_0(k1_tarski('#skF_6'),k1_tarski('#skF_6')) != k2_tarski('#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9031,c_9031,c_73])).

tff(c_9038,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_157,c_9034])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:13:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.28/2.34  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.28/2.35  
% 6.28/2.35  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.28/2.35  %$ r2_hidden > r1_xboole_0 > r1_tarski > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_5 > #skF_6 > #skF_4 > #skF_3 > #skF_1
% 6.28/2.35  
% 6.28/2.35  %Foreground sorts:
% 6.28/2.35  
% 6.28/2.35  
% 6.28/2.35  %Background operators:
% 6.28/2.35  
% 6.28/2.35  
% 6.28/2.35  %Foreground operators:
% 6.28/2.35  tff('#skF_2', type, '#skF_2': $i > $i).
% 6.28/2.35  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.28/2.35  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.28/2.35  tff(k1_tarski, type, k1_tarski: $i > $i).
% 6.28/2.35  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 6.28/2.35  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.28/2.35  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 6.28/2.35  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 6.28/2.35  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.28/2.35  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 6.28/2.35  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 6.28/2.35  tff('#skF_5', type, '#skF_5': $i).
% 6.28/2.35  tff('#skF_6', type, '#skF_6': $i).
% 6.28/2.35  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 6.28/2.35  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 6.28/2.35  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 6.28/2.35  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 6.28/2.35  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.28/2.35  tff(k3_tarski, type, k3_tarski: $i > $i).
% 6.28/2.35  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.28/2.35  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 6.28/2.35  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 6.28/2.35  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 6.28/2.35  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 6.28/2.35  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 6.28/2.35  
% 6.28/2.37  tff(f_84, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 6.28/2.37  tff(f_112, axiom, (![A]: (k3_tarski(k1_tarski(A)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_zfmisc_1)).
% 6.28/2.37  tff(f_100, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 6.28/2.37  tff(f_86, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 6.28/2.37  tff(f_82, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 6.28/2.37  tff(f_110, axiom, (![A, B]: (~(A = B) => (k5_xboole_0(k1_tarski(A), k1_tarski(B)) = k2_tarski(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_zfmisc_1)).
% 6.28/2.37  tff(f_105, axiom, (![A, B]: (~(A = B) => r1_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_zfmisc_1)).
% 6.28/2.37  tff(f_65, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 6.28/2.37  tff(f_67, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 6.28/2.37  tff(f_115, negated_conjecture, ~(![A, B]: (k3_tarski(k2_tarski(k1_tarski(A), k1_tarski(B))) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t32_zfmisc_1)).
% 6.28/2.37  tff(f_61, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_xboole_1)).
% 6.28/2.37  tff(f_51, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 6.28/2.37  tff(f_43, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 6.28/2.37  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 6.28/2.37  tff(f_53, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 6.28/2.37  tff(f_59, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 6.28/2.37  tff(f_57, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 6.28/2.37  tff(f_29, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 6.28/2.37  tff(f_98, axiom, (![A, B]: (r2_hidden(A, B) => (k3_xboole_0(B, k1_tarski(A)) = k1_tarski(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l31_zfmisc_1)).
% 6.28/2.37  tff(c_50, plain, (![A_31]: (k2_tarski(A_31, A_31)=k1_tarski(A_31))), inference(cnfTransformation, [status(thm)], [f_84])).
% 6.28/2.37  tff(c_70, plain, (![A_60]: (k3_tarski(k1_tarski(A_60))=A_60)), inference(cnfTransformation, [status(thm)], [f_112])).
% 6.28/2.37  tff(c_145, plain, (![A_82, B_83]: (k3_tarski(k2_tarski(A_82, B_83))=k2_xboole_0(A_82, B_83))), inference(cnfTransformation, [status(thm)], [f_100])).
% 6.28/2.37  tff(c_154, plain, (![A_31]: (k3_tarski(k1_tarski(A_31))=k2_xboole_0(A_31, A_31))), inference(superposition, [status(thm), theory('equality')], [c_50, c_145])).
% 6.28/2.37  tff(c_157, plain, (![A_31]: (k2_xboole_0(A_31, A_31)=A_31)), inference(demodulation, [status(thm), theory('equality')], [c_70, c_154])).
% 6.28/2.37  tff(c_167, plain, (![A_85, B_86]: (k1_enumset1(A_85, A_85, B_86)=k2_tarski(A_85, B_86))), inference(cnfTransformation, [status(thm)], [f_86])).
% 6.28/2.37  tff(c_30, plain, (![E_30, A_24, C_26]: (r2_hidden(E_30, k1_enumset1(A_24, E_30, C_26)))), inference(cnfTransformation, [status(thm)], [f_82])).
% 6.28/2.37  tff(c_186, plain, (![A_89, B_90]: (r2_hidden(A_89, k2_tarski(A_89, B_90)))), inference(superposition, [status(thm), theory('equality')], [c_167, c_30])).
% 6.28/2.37  tff(c_189, plain, (![A_31]: (r2_hidden(A_31, k1_tarski(A_31)))), inference(superposition, [status(thm), theory('equality')], [c_50, c_186])).
% 6.28/2.37  tff(c_68, plain, (![A_58, B_59]: (k5_xboole_0(k1_tarski(A_58), k1_tarski(B_59))=k2_tarski(A_58, B_59) | B_59=A_58)), inference(cnfTransformation, [status(thm)], [f_110])).
% 6.28/2.37  tff(c_66, plain, (![A_56, B_57]: (r1_xboole_0(k1_tarski(A_56), k1_tarski(B_57)) | B_57=A_56)), inference(cnfTransformation, [status(thm)], [f_105])).
% 6.28/2.37  tff(c_198, plain, (![A_96, B_97]: (k4_xboole_0(A_96, B_97)=A_96 | ~r1_xboole_0(A_96, B_97))), inference(cnfTransformation, [status(thm)], [f_65])).
% 6.28/2.37  tff(c_1918, plain, (![A_237, B_238]: (k4_xboole_0(k1_tarski(A_237), k1_tarski(B_238))=k1_tarski(A_237) | B_238=A_237)), inference(resolution, [status(thm)], [c_66, c_198])).
% 6.28/2.37  tff(c_24, plain, (![A_22, B_23]: (k5_xboole_0(A_22, k4_xboole_0(B_23, A_22))=k2_xboole_0(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_67])).
% 6.28/2.37  tff(c_8106, plain, (![B_386, A_387]: (k5_xboole_0(k1_tarski(B_386), k1_tarski(A_387))=k2_xboole_0(k1_tarski(B_386), k1_tarski(A_387)) | B_386=A_387)), inference(superposition, [status(thm), theory('equality')], [c_1918, c_24])).
% 6.28/2.37  tff(c_8986, plain, (![A_418, B_419]: (k2_xboole_0(k1_tarski(A_418), k1_tarski(B_419))=k2_tarski(A_418, B_419) | B_419=A_418 | B_419=A_418)), inference(superposition, [status(thm), theory('equality')], [c_68, c_8106])).
% 6.28/2.37  tff(c_64, plain, (![A_54, B_55]: (k3_tarski(k2_tarski(A_54, B_55))=k2_xboole_0(A_54, B_55))), inference(cnfTransformation, [status(thm)], [f_100])).
% 6.28/2.37  tff(c_72, plain, (k3_tarski(k2_tarski(k1_tarski('#skF_5'), k1_tarski('#skF_6')))!=k2_tarski('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_115])).
% 6.28/2.37  tff(c_73, plain, (k2_xboole_0(k1_tarski('#skF_5'), k1_tarski('#skF_6'))!=k2_tarski('#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_72])).
% 6.28/2.37  tff(c_9014, plain, ('#skF_5'='#skF_6'), inference(superposition, [status(thm), theory('equality')], [c_8986, c_73])).
% 6.28/2.37  tff(c_18, plain, (![A_18, B_19]: (r1_xboole_0(k4_xboole_0(A_18, B_19), B_19))), inference(cnfTransformation, [status(thm)], [f_61])).
% 6.28/2.37  tff(c_10, plain, (![A_10]: (r2_hidden('#skF_2'(A_10), A_10) | k1_xboole_0=A_10)), inference(cnfTransformation, [status(thm)], [f_51])).
% 6.28/2.37  tff(c_247, plain, (![A_103, B_104, C_105]: (~r1_xboole_0(A_103, B_104) | ~r2_hidden(C_105, k3_xboole_0(A_103, B_104)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 6.28/2.37  tff(c_272, plain, (![A_108, B_109]: (~r1_xboole_0(A_108, B_109) | k3_xboole_0(A_108, B_109)=k1_xboole_0)), inference(resolution, [status(thm)], [c_10, c_247])).
% 6.28/2.37  tff(c_285, plain, (![A_110, B_111]: (k3_xboole_0(k4_xboole_0(A_110, B_111), B_111)=k1_xboole_0)), inference(resolution, [status(thm)], [c_18, c_272])).
% 6.28/2.37  tff(c_8, plain, (![A_5, B_6, C_9]: (~r1_xboole_0(A_5, B_6) | ~r2_hidden(C_9, k3_xboole_0(A_5, B_6)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 6.28/2.37  tff(c_290, plain, (![A_110, B_111, C_9]: (~r1_xboole_0(k4_xboole_0(A_110, B_111), B_111) | ~r2_hidden(C_9, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_285, c_8])).
% 6.28/2.37  tff(c_312, plain, (![C_9]: (~r2_hidden(C_9, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_290])).
% 6.28/2.37  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 6.28/2.37  tff(c_296, plain, (![B_111, A_110]: (k3_xboole_0(B_111, k4_xboole_0(A_110, B_111))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_285, c_2])).
% 6.28/2.37  tff(c_421, plain, (![A_124, B_125]: (r2_hidden('#skF_1'(A_124, B_125), k3_xboole_0(A_124, B_125)) | r1_xboole_0(A_124, B_125))), inference(cnfTransformation, [status(thm)], [f_43])).
% 6.28/2.37  tff(c_432, plain, (![B_111, A_110]: (r2_hidden('#skF_1'(B_111, k4_xboole_0(A_110, B_111)), k1_xboole_0) | r1_xboole_0(B_111, k4_xboole_0(A_110, B_111)))), inference(superposition, [status(thm), theory('equality')], [c_296, c_421])).
% 6.28/2.37  tff(c_450, plain, (![B_126, A_127]: (r1_xboole_0(B_126, k4_xboole_0(A_127, B_126)))), inference(negUnitSimplification, [status(thm)], [c_312, c_432])).
% 6.28/2.37  tff(c_20, plain, (![A_20, B_21]: (k4_xboole_0(A_20, B_21)=A_20 | ~r1_xboole_0(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_65])).
% 6.28/2.37  tff(c_459, plain, (![B_126, A_127]: (k4_xboole_0(B_126, k4_xboole_0(A_127, B_126))=B_126)), inference(resolution, [status(thm)], [c_450, c_20])).
% 6.28/2.37  tff(c_284, plain, (![A_18, B_19]: (k3_xboole_0(k4_xboole_0(A_18, B_19), B_19)=k1_xboole_0)), inference(resolution, [status(thm)], [c_18, c_272])).
% 6.28/2.37  tff(c_220, plain, (![A_100, B_101]: (k5_xboole_0(A_100, k3_xboole_0(A_100, B_101))=k4_xboole_0(A_100, B_101))), inference(cnfTransformation, [status(thm)], [f_53])).
% 6.28/2.37  tff(c_552, plain, (![B_133, A_134]: (k5_xboole_0(B_133, k3_xboole_0(A_134, B_133))=k4_xboole_0(B_133, A_134))), inference(superposition, [status(thm), theory('equality')], [c_2, c_220])).
% 6.28/2.37  tff(c_571, plain, (![B_19, A_18]: (k4_xboole_0(B_19, k4_xboole_0(A_18, B_19))=k5_xboole_0(B_19, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_284, c_552])).
% 6.28/2.37  tff(c_590, plain, (![B_19]: (k5_xboole_0(B_19, k1_xboole_0)=B_19)), inference(demodulation, [status(thm), theory('equality')], [c_459, c_571])).
% 6.28/2.37  tff(c_16, plain, (![A_16, B_17]: (r1_tarski(k4_xboole_0(A_16, B_17), A_16))), inference(cnfTransformation, [status(thm)], [f_59])).
% 6.28/2.37  tff(c_140, plain, (![A_80, B_81]: (k3_xboole_0(A_80, B_81)=A_80 | ~r1_tarski(A_80, B_81))), inference(cnfTransformation, [status(thm)], [f_57])).
% 6.28/2.37  tff(c_698, plain, (![A_142, B_143]: (k3_xboole_0(k4_xboole_0(A_142, B_143), A_142)=k4_xboole_0(A_142, B_143))), inference(resolution, [status(thm)], [c_16, c_140])).
% 6.28/2.37  tff(c_715, plain, (![A_142]: (k4_xboole_0(A_142, A_142)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_698, c_284])).
% 6.28/2.37  tff(c_766, plain, (![A_144]: (k4_xboole_0(A_144, A_144)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_698, c_284])).
% 6.28/2.37  tff(c_210, plain, (![A_18, B_19]: (k4_xboole_0(k4_xboole_0(A_18, B_19), B_19)=k4_xboole_0(A_18, B_19))), inference(resolution, [status(thm)], [c_18, c_198])).
% 6.28/2.37  tff(c_774, plain, (![A_144]: (k4_xboole_0(k1_xboole_0, A_144)=k4_xboole_0(A_144, A_144))), inference(superposition, [status(thm), theory('equality')], [c_766, c_210])).
% 6.28/2.37  tff(c_968, plain, (![A_160]: (k4_xboole_0(k1_xboole_0, A_160)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_715, c_774])).
% 6.28/2.37  tff(c_998, plain, (![A_160]: (k5_xboole_0(A_160, k1_xboole_0)=k2_xboole_0(A_160, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_968, c_24])).
% 6.28/2.37  tff(c_1021, plain, (![A_160]: (k2_xboole_0(A_160, k1_xboole_0)=A_160)), inference(demodulation, [status(thm), theory('equality')], [c_590, c_998])).
% 6.28/2.37  tff(c_4, plain, (![A_3]: (k3_xboole_0(A_3, A_3)=A_3)), inference(cnfTransformation, [status(thm)], [f_29])).
% 6.28/2.37  tff(c_235, plain, (![A_3]: (k5_xboole_0(A_3, A_3)=k4_xboole_0(A_3, A_3))), inference(superposition, [status(thm), theory('equality')], [c_4, c_220])).
% 6.28/2.37  tff(c_765, plain, (![A_3]: (k5_xboole_0(A_3, A_3)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_715, c_235])).
% 6.28/2.37  tff(c_346, plain, (![B_118, A_119]: (k3_xboole_0(B_118, k1_tarski(A_119))=k1_tarski(A_119) | ~r2_hidden(A_119, B_118))), inference(cnfTransformation, [status(thm)], [f_98])).
% 6.28/2.37  tff(c_2093, plain, (![A_246, A_247]: (k3_xboole_0(k1_tarski(A_246), A_247)=k1_tarski(A_246) | ~r2_hidden(A_246, A_247))), inference(superposition, [status(thm), theory('equality')], [c_2, c_346])).
% 6.28/2.37  tff(c_12, plain, (![A_12, B_13]: (k5_xboole_0(A_12, k3_xboole_0(A_12, B_13))=k4_xboole_0(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_53])).
% 6.28/2.37  tff(c_2131, plain, (![A_246, A_247]: (k5_xboole_0(k1_tarski(A_246), k1_tarski(A_246))=k4_xboole_0(k1_tarski(A_246), A_247) | ~r2_hidden(A_246, A_247))), inference(superposition, [status(thm), theory('equality')], [c_2093, c_12])).
% 6.28/2.37  tff(c_2208, plain, (![A_250, A_251]: (k4_xboole_0(k1_tarski(A_250), A_251)=k1_xboole_0 | ~r2_hidden(A_250, A_251))), inference(demodulation, [status(thm), theory('equality')], [c_765, c_2131])).
% 6.28/2.37  tff(c_503, plain, (![A_131, B_132]: (k4_xboole_0(k4_xboole_0(A_131, B_132), B_132)=k4_xboole_0(A_131, B_132))), inference(resolution, [status(thm)], [c_18, c_198])).
% 6.28/2.37  tff(c_524, plain, (![B_132, A_131]: (k5_xboole_0(B_132, k4_xboole_0(A_131, B_132))=k2_xboole_0(B_132, k4_xboole_0(A_131, B_132)))), inference(superposition, [status(thm), theory('equality')], [c_503, c_24])).
% 6.28/2.37  tff(c_546, plain, (![B_132, A_131]: (k2_xboole_0(B_132, k4_xboole_0(A_131, B_132))=k2_xboole_0(B_132, A_131))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_524])).
% 6.28/2.37  tff(c_2239, plain, (![A_251, A_250]: (k2_xboole_0(A_251, k1_tarski(A_250))=k2_xboole_0(A_251, k1_xboole_0) | ~r2_hidden(A_250, A_251))), inference(superposition, [status(thm), theory('equality')], [c_2208, c_546])).
% 6.28/2.37  tff(c_2483, plain, (![A_254, A_255]: (k2_xboole_0(A_254, k1_tarski(A_255))=A_254 | ~r2_hidden(A_255, A_254))), inference(demodulation, [status(thm), theory('equality')], [c_1021, c_2239])).
% 6.28/2.37  tff(c_2493, plain, (k2_tarski('#skF_5', '#skF_6')!=k1_tarski('#skF_5') | ~r2_hidden('#skF_6', k1_tarski('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_2483, c_73])).
% 6.28/2.37  tff(c_2586, plain, (~r2_hidden('#skF_6', k1_tarski('#skF_5'))), inference(splitLeft, [status(thm)], [c_2493])).
% 6.28/2.37  tff(c_9018, plain, (~r2_hidden('#skF_6', k1_tarski('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_9014, c_2586])).
% 6.28/2.37  tff(c_9022, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_189, c_9018])).
% 6.28/2.37  tff(c_9024, plain, (r2_hidden('#skF_6', k1_tarski('#skF_5'))), inference(splitRight, [status(thm)], [c_2493])).
% 6.28/2.37  tff(c_22, plain, (![A_20, B_21]: (r1_xboole_0(A_20, B_21) | k4_xboole_0(A_20, B_21)!=A_20)), inference(cnfTransformation, [status(thm)], [f_65])).
% 6.28/2.37  tff(c_262, plain, (![A_106, C_107]: (~r1_xboole_0(A_106, A_106) | ~r2_hidden(C_107, A_106))), inference(superposition, [status(thm), theory('equality')], [c_4, c_247])).
% 6.28/2.37  tff(c_397, plain, (![C_120, B_121]: (~r2_hidden(C_120, B_121) | k4_xboole_0(B_121, B_121)!=B_121)), inference(resolution, [status(thm)], [c_22, c_262])).
% 6.28/2.37  tff(c_413, plain, (![A_31]: (k4_xboole_0(k1_tarski(A_31), k1_tarski(A_31))!=k1_tarski(A_31))), inference(resolution, [status(thm)], [c_189, c_397])).
% 6.28/2.37  tff(c_762, plain, (![A_31]: (k1_tarski(A_31)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_715, c_413])).
% 6.28/2.37  tff(c_1829, plain, (![A_233, B_234]: (k3_xboole_0(k1_tarski(A_233), k1_tarski(B_234))=k1_xboole_0 | B_234=A_233)), inference(resolution, [status(thm)], [c_66, c_272])).
% 6.28/2.37  tff(c_62, plain, (![B_53, A_52]: (k3_xboole_0(B_53, k1_tarski(A_52))=k1_tarski(A_52) | ~r2_hidden(A_52, B_53))), inference(cnfTransformation, [status(thm)], [f_98])).
% 6.28/2.37  tff(c_1844, plain, (![B_234, A_233]: (k1_tarski(B_234)=k1_xboole_0 | ~r2_hidden(B_234, k1_tarski(A_233)) | B_234=A_233)), inference(superposition, [status(thm), theory('equality')], [c_1829, c_62])).
% 6.28/2.37  tff(c_1881, plain, (![B_234, A_233]: (~r2_hidden(B_234, k1_tarski(A_233)) | B_234=A_233)), inference(negUnitSimplification, [status(thm)], [c_762, c_1844])).
% 6.28/2.37  tff(c_9031, plain, ('#skF_5'='#skF_6'), inference(resolution, [status(thm)], [c_9024, c_1881])).
% 6.28/2.37  tff(c_9034, plain, (k2_xboole_0(k1_tarski('#skF_6'), k1_tarski('#skF_6'))!=k2_tarski('#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_9031, c_9031, c_73])).
% 6.28/2.37  tff(c_9038, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_50, c_157, c_9034])).
% 6.28/2.37  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.28/2.37  
% 6.28/2.37  Inference rules
% 6.28/2.37  ----------------------
% 6.28/2.37  #Ref     : 0
% 6.28/2.37  #Sup     : 2057
% 6.28/2.37  #Fact    : 24
% 6.28/2.37  #Define  : 0
% 6.28/2.37  #Split   : 1
% 6.28/2.37  #Chain   : 0
% 6.28/2.37  #Close   : 0
% 6.28/2.37  
% 6.28/2.37  Ordering : KBO
% 6.28/2.37  
% 6.28/2.37  Simplification rules
% 6.28/2.37  ----------------------
% 6.28/2.37  #Subsume      : 770
% 6.28/2.37  #Demod        : 1673
% 6.28/2.37  #Tautology    : 929
% 6.28/2.37  #SimpNegUnit  : 109
% 6.28/2.37  #BackRed      : 7
% 6.28/2.37  
% 6.28/2.37  #Partial instantiations: 0
% 6.28/2.37  #Strategies tried      : 1
% 6.28/2.37  
% 6.28/2.37  Timing (in seconds)
% 6.28/2.37  ----------------------
% 6.28/2.38  Preprocessing        : 0.34
% 6.28/2.38  Parsing              : 0.18
% 6.28/2.38  CNF conversion       : 0.03
% 6.28/2.38  Main loop            : 1.25
% 6.28/2.38  Inferencing          : 0.39
% 6.28/2.38  Reduction            : 0.51
% 6.28/2.38  Demodulation         : 0.39
% 6.28/2.38  BG Simplification    : 0.05
% 6.28/2.38  Subsumption          : 0.23
% 6.28/2.38  Abstraction          : 0.09
% 6.28/2.38  MUC search           : 0.00
% 6.28/2.38  Cooper               : 0.00
% 6.28/2.38  Total                : 1.64
% 6.28/2.38  Index Insertion      : 0.00
% 6.28/2.38  Index Deletion       : 0.00
% 6.28/2.38  Index Matching       : 0.00
% 6.28/2.38  BG Taut test         : 0.00
%------------------------------------------------------------------------------

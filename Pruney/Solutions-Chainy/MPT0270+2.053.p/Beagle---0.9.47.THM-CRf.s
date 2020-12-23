%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:52:59 EST 2020

% Result     : Theorem 6.00s
% Output     : CNFRefutation 6.31s
% Verified   : 
% Statistics : Number of formulae       :  108 ( 202 expanded)
%              Number of leaves         :   38 (  83 expanded)
%              Depth                    :   14
%              Number of atoms          :  123 ( 270 expanded)
%              Number of equality atoms :   59 ( 126 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    3 (   2 average)

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

tff(f_63,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_51,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_43,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_61,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_57,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_59,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_87,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
    <=> A != B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).

tff(f_29,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_99,negated_conjecture,(
    ~ ! [A,B] :
        ( k4_xboole_0(k1_tarski(A),B) = k1_tarski(A)
      <=> ~ r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_zfmisc_1)).

tff(f_82,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_65,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_93,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(c_22,plain,(
    ! [A_19,B_20] : r1_xboole_0(k4_xboole_0(A_19,B_20),B_20) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_10,plain,(
    ! [A_10] :
      ( r2_hidden('#skF_2'(A_10),A_10)
      | k1_xboole_0 = A_10 ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_6707,plain,(
    ! [A_348,B_349,C_350] :
      ( ~ r1_xboole_0(A_348,B_349)
      | ~ r2_hidden(C_350,k3_xboole_0(A_348,B_349)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_6744,plain,(
    ! [A_356,B_357] :
      ( ~ r1_xboole_0(A_356,B_357)
      | k3_xboole_0(A_356,B_357) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_10,c_6707])).

tff(c_7063,plain,(
    ! [A_368,B_369] : k3_xboole_0(k4_xboole_0(A_368,B_369),B_369) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_22,c_6744])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_7074,plain,(
    ! [B_369,A_368] : k3_xboole_0(B_369,k4_xboole_0(A_368,B_369)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_7063,c_2])).

tff(c_20,plain,(
    ! [A_18] : k5_xboole_0(A_18,k1_xboole_0) = A_18 ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_7135,plain,(
    ! [B_370,A_371] : k3_xboole_0(B_370,k4_xboole_0(A_371,B_370)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_7063,c_2])).

tff(c_16,plain,(
    ! [A_14,B_15] : k5_xboole_0(A_14,k3_xboole_0(A_14,B_15)) = k4_xboole_0(A_14,B_15) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_7143,plain,(
    ! [B_370,A_371] : k4_xboole_0(B_370,k4_xboole_0(A_371,B_370)) = k5_xboole_0(B_370,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_7135,c_16])).

tff(c_7304,plain,(
    ! [B_380,A_381] : k4_xboole_0(B_380,k4_xboole_0(A_381,B_380)) = B_380 ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_7143])).

tff(c_18,plain,(
    ! [A_16,B_17] : k4_xboole_0(A_16,k4_xboole_0(A_16,B_17)) = k3_xboole_0(A_16,B_17) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_7322,plain,(
    ! [B_380,A_381] : k3_xboole_0(B_380,k4_xboole_0(A_381,B_380)) = k4_xboole_0(B_380,B_380) ),
    inference(superposition,[status(thm),theory(equality)],[c_7304,c_18])).

tff(c_7377,plain,(
    ! [B_380] : k4_xboole_0(B_380,B_380) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_7074,c_7322])).

tff(c_40,plain,(
    ! [B_52] : k4_xboole_0(k1_tarski(B_52),k1_tarski(B_52)) != k1_tarski(B_52) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_7395,plain,(
    ! [B_52] : k1_tarski(B_52) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_7377,c_40])).

tff(c_4,plain,(
    ! [A_3] : k3_xboole_0(A_3,A_3) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_161,plain,(
    ! [A_81,B_82] : k4_xboole_0(A_81,k4_xboole_0(A_81,B_82)) = k3_xboole_0(A_81,B_82) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_2810,plain,(
    ! [A_210,B_211] : r1_xboole_0(k3_xboole_0(A_210,B_211),k4_xboole_0(A_210,B_211)) ),
    inference(superposition,[status(thm),theory(equality)],[c_161,c_22])).

tff(c_2831,plain,(
    ! [A_3] : r1_xboole_0(A_3,k4_xboole_0(A_3,A_3)) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_2810])).

tff(c_2840,plain,(
    ! [A_213,B_214,C_215] :
      ( ~ r1_xboole_0(A_213,B_214)
      | ~ r2_hidden(C_215,k3_xboole_0(A_213,B_214)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_2870,plain,(
    ! [A_219,B_220] :
      ( ~ r1_xboole_0(A_219,B_220)
      | k3_xboole_0(A_219,B_220) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_10,c_2840])).

tff(c_3746,plain,(
    ! [A_248] : k3_xboole_0(A_248,k4_xboole_0(A_248,A_248)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2831,c_2870])).

tff(c_170,plain,(
    ! [A_81,B_82] : r1_xboole_0(k3_xboole_0(A_81,B_82),k4_xboole_0(A_81,B_82)) ),
    inference(superposition,[status(thm),theory(equality)],[c_161,c_22])).

tff(c_3757,plain,(
    ! [A_248] : r1_xboole_0(k1_xboole_0,k4_xboole_0(A_248,k4_xboole_0(A_248,A_248))) ),
    inference(superposition,[status(thm),theory(equality)],[c_3746,c_170])).

tff(c_3802,plain,(
    ! [A_249] : r1_xboole_0(k1_xboole_0,A_249) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_18,c_3757])).

tff(c_2854,plain,(
    ! [A_213,B_214] :
      ( ~ r1_xboole_0(A_213,B_214)
      | k3_xboole_0(A_213,B_214) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_10,c_2840])).

tff(c_3815,plain,(
    ! [A_250] : k3_xboole_0(k1_xboole_0,A_250) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_3802,c_2854])).

tff(c_3855,plain,(
    ! [A_1] : k3_xboole_0(A_1,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_3815])).

tff(c_3933,plain,(
    ! [A_259] : k3_xboole_0(A_259,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_3815])).

tff(c_3953,plain,(
    ! [A_259] : k5_xboole_0(A_259,k1_xboole_0) = k4_xboole_0(A_259,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_3933,c_16])).

tff(c_4040,plain,(
    ! [A_261] : k4_xboole_0(A_261,k1_xboole_0) = A_261 ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_3953])).

tff(c_4064,plain,(
    ! [A_261] : k4_xboole_0(A_261,A_261) = k3_xboole_0(A_261,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_4040,c_18])).

tff(c_4081,plain,(
    ! [A_261] : k4_xboole_0(A_261,A_261) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_3855,c_4064])).

tff(c_4092,plain,(
    ! [B_52] : k1_tarski(B_52) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4081,c_40])).

tff(c_52,plain,
    ( ~ r2_hidden('#skF_3','#skF_4')
    | r2_hidden('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_85,plain,(
    ~ r2_hidden('#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_38,plain,(
    ! [A_49,B_50] :
      ( r1_xboole_0(k1_tarski(A_49),B_50)
      | r2_hidden(A_49,B_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_212,plain,(
    ! [A_88,B_89,C_90] :
      ( ~ r1_xboole_0(A_88,B_89)
      | ~ r2_hidden(C_90,k3_xboole_0(A_88,B_89)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_232,plain,(
    ! [A_93,B_94] :
      ( ~ r1_xboole_0(A_93,B_94)
      | k3_xboole_0(A_93,B_94) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_10,c_212])).

tff(c_1476,plain,(
    ! [A_175,B_176] :
      ( k3_xboole_0(k1_tarski(A_175),B_176) = k1_xboole_0
      | r2_hidden(A_175,B_176) ) ),
    inference(resolution,[status(thm)],[c_38,c_232])).

tff(c_1508,plain,(
    ! [A_175,B_176] :
      ( k5_xboole_0(k1_tarski(A_175),k1_xboole_0) = k4_xboole_0(k1_tarski(A_175),B_176)
      | r2_hidden(A_175,B_176) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1476,c_16])).

tff(c_2613,plain,(
    ! [A_205,B_206] :
      ( k4_xboole_0(k1_tarski(A_205),B_206) = k1_tarski(A_205)
      | r2_hidden(A_205,B_206) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_1508])).

tff(c_50,plain,
    ( k4_xboole_0(k1_tarski('#skF_3'),'#skF_4') != k1_tarski('#skF_3')
    | r2_hidden('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_179,plain,(
    k4_xboole_0(k1_tarski('#skF_3'),'#skF_4') != k1_tarski('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_2684,plain,(
    r2_hidden('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_2613,c_179])).

tff(c_2736,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_85,c_2684])).

tff(c_2737,plain,(
    r2_hidden('#skF_5','#skF_6') ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_24,plain,(
    ! [A_21] : k2_tarski(A_21,A_21) = k1_tarski(A_21) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_3361,plain,(
    ! [A_232,B_233,C_234] :
      ( r1_tarski(k2_tarski(A_232,B_233),C_234)
      | ~ r2_hidden(B_233,C_234)
      | ~ r2_hidden(A_232,C_234) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_6435,plain,(
    ! [A_326,C_327] :
      ( r1_tarski(k1_tarski(A_326),C_327)
      | ~ r2_hidden(A_326,C_327)
      | ~ r2_hidden(A_326,C_327) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_3361])).

tff(c_14,plain,(
    ! [A_12,B_13] :
      ( k4_xboole_0(A_12,B_13) = k1_xboole_0
      | ~ r1_tarski(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_6444,plain,(
    ! [A_328,C_329] :
      ( k4_xboole_0(k1_tarski(A_328),C_329) = k1_xboole_0
      | ~ r2_hidden(A_328,C_329) ) ),
    inference(resolution,[status(thm)],[c_6435,c_14])).

tff(c_2738,plain,(
    k4_xboole_0(k1_tarski('#skF_3'),'#skF_4') = k1_tarski('#skF_3') ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_54,plain,
    ( k4_xboole_0(k1_tarski('#skF_3'),'#skF_4') != k1_tarski('#skF_3')
    | k4_xboole_0(k1_tarski('#skF_5'),'#skF_6') = k1_tarski('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_2797,plain,(
    k4_xboole_0(k1_tarski('#skF_5'),'#skF_6') = k1_tarski('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2738,c_54])).

tff(c_6516,plain,
    ( k1_tarski('#skF_5') = k1_xboole_0
    | ~ r2_hidden('#skF_5','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_6444,c_2797])).

tff(c_6589,plain,(
    k1_tarski('#skF_5') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2737,c_6516])).

tff(c_6591,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4092,c_6589])).

tff(c_6592,plain,(
    r2_hidden('#skF_5','#skF_6') ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_7456,plain,(
    ! [A_386,B_387,C_388] :
      ( r1_tarski(k2_tarski(A_386,B_387),C_388)
      | ~ r2_hidden(B_387,C_388)
      | ~ r2_hidden(A_386,C_388) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_9910,plain,(
    ! [A_473,C_474] :
      ( r1_tarski(k1_tarski(A_473),C_474)
      | ~ r2_hidden(A_473,C_474)
      | ~ r2_hidden(A_473,C_474) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_7456])).

tff(c_9919,plain,(
    ! [A_475,C_476] :
      ( k4_xboole_0(k1_tarski(A_475),C_476) = k1_xboole_0
      | ~ r2_hidden(A_475,C_476) ) ),
    inference(resolution,[status(thm)],[c_9910,c_14])).

tff(c_6593,plain,(
    r2_hidden('#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_56,plain,
    ( ~ r2_hidden('#skF_3','#skF_4')
    | k4_xboole_0(k1_tarski('#skF_5'),'#skF_6') = k1_tarski('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_6682,plain,(
    k4_xboole_0(k1_tarski('#skF_5'),'#skF_6') = k1_tarski('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6593,c_56])).

tff(c_10001,plain,
    ( k1_tarski('#skF_5') = k1_xboole_0
    | ~ r2_hidden('#skF_5','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_9919,c_6682])).

tff(c_10063,plain,(
    k1_tarski('#skF_5') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6592,c_10001])).

tff(c_10065,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_7395,c_10063])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:25:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.00/2.36  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.31/2.37  
% 6.31/2.37  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.31/2.37  %$ r2_hidden > r1_xboole_0 > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_1
% 6.31/2.37  
% 6.31/2.37  %Foreground sorts:
% 6.31/2.37  
% 6.31/2.37  
% 6.31/2.37  %Background operators:
% 6.31/2.37  
% 6.31/2.37  
% 6.31/2.37  %Foreground operators:
% 6.31/2.37  tff('#skF_2', type, '#skF_2': $i > $i).
% 6.31/2.37  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.31/2.37  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.31/2.37  tff(k1_tarski, type, k1_tarski: $i > $i).
% 6.31/2.37  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 6.31/2.37  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.31/2.37  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 6.31/2.37  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 6.31/2.37  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.31/2.37  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 6.31/2.37  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 6.31/2.37  tff('#skF_5', type, '#skF_5': $i).
% 6.31/2.37  tff('#skF_6', type, '#skF_6': $i).
% 6.31/2.37  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 6.31/2.37  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 6.31/2.37  tff('#skF_3', type, '#skF_3': $i).
% 6.31/2.37  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 6.31/2.37  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 6.31/2.37  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.31/2.37  tff('#skF_4', type, '#skF_4': $i).
% 6.31/2.37  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.31/2.37  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 6.31/2.37  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 6.31/2.37  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 6.31/2.37  
% 6.31/2.39  tff(f_63, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_xboole_1)).
% 6.31/2.39  tff(f_51, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 6.31/2.39  tff(f_43, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 6.31/2.39  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 6.31/2.39  tff(f_61, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 6.31/2.39  tff(f_57, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 6.31/2.39  tff(f_59, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 6.31/2.39  tff(f_87, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 6.31/2.39  tff(f_29, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 6.31/2.39  tff(f_99, negated_conjecture, ~(![A, B]: ((k4_xboole_0(k1_tarski(A), B) = k1_tarski(A)) <=> ~r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t67_zfmisc_1)).
% 6.31/2.39  tff(f_82, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 6.31/2.39  tff(f_65, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 6.31/2.39  tff(f_93, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 6.31/2.39  tff(f_55, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 6.31/2.39  tff(c_22, plain, (![A_19, B_20]: (r1_xboole_0(k4_xboole_0(A_19, B_20), B_20))), inference(cnfTransformation, [status(thm)], [f_63])).
% 6.31/2.39  tff(c_10, plain, (![A_10]: (r2_hidden('#skF_2'(A_10), A_10) | k1_xboole_0=A_10)), inference(cnfTransformation, [status(thm)], [f_51])).
% 6.31/2.39  tff(c_6707, plain, (![A_348, B_349, C_350]: (~r1_xboole_0(A_348, B_349) | ~r2_hidden(C_350, k3_xboole_0(A_348, B_349)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 6.31/2.39  tff(c_6744, plain, (![A_356, B_357]: (~r1_xboole_0(A_356, B_357) | k3_xboole_0(A_356, B_357)=k1_xboole_0)), inference(resolution, [status(thm)], [c_10, c_6707])).
% 6.31/2.39  tff(c_7063, plain, (![A_368, B_369]: (k3_xboole_0(k4_xboole_0(A_368, B_369), B_369)=k1_xboole_0)), inference(resolution, [status(thm)], [c_22, c_6744])).
% 6.31/2.39  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 6.31/2.39  tff(c_7074, plain, (![B_369, A_368]: (k3_xboole_0(B_369, k4_xboole_0(A_368, B_369))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_7063, c_2])).
% 6.31/2.39  tff(c_20, plain, (![A_18]: (k5_xboole_0(A_18, k1_xboole_0)=A_18)), inference(cnfTransformation, [status(thm)], [f_61])).
% 6.31/2.39  tff(c_7135, plain, (![B_370, A_371]: (k3_xboole_0(B_370, k4_xboole_0(A_371, B_370))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_7063, c_2])).
% 6.31/2.39  tff(c_16, plain, (![A_14, B_15]: (k5_xboole_0(A_14, k3_xboole_0(A_14, B_15))=k4_xboole_0(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_57])).
% 6.31/2.39  tff(c_7143, plain, (![B_370, A_371]: (k4_xboole_0(B_370, k4_xboole_0(A_371, B_370))=k5_xboole_0(B_370, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_7135, c_16])).
% 6.31/2.39  tff(c_7304, plain, (![B_380, A_381]: (k4_xboole_0(B_380, k4_xboole_0(A_381, B_380))=B_380)), inference(demodulation, [status(thm), theory('equality')], [c_20, c_7143])).
% 6.31/2.39  tff(c_18, plain, (![A_16, B_17]: (k4_xboole_0(A_16, k4_xboole_0(A_16, B_17))=k3_xboole_0(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_59])).
% 6.31/2.39  tff(c_7322, plain, (![B_380, A_381]: (k3_xboole_0(B_380, k4_xboole_0(A_381, B_380))=k4_xboole_0(B_380, B_380))), inference(superposition, [status(thm), theory('equality')], [c_7304, c_18])).
% 6.31/2.39  tff(c_7377, plain, (![B_380]: (k4_xboole_0(B_380, B_380)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_7074, c_7322])).
% 6.31/2.39  tff(c_40, plain, (![B_52]: (k4_xboole_0(k1_tarski(B_52), k1_tarski(B_52))!=k1_tarski(B_52))), inference(cnfTransformation, [status(thm)], [f_87])).
% 6.31/2.39  tff(c_7395, plain, (![B_52]: (k1_tarski(B_52)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_7377, c_40])).
% 6.31/2.39  tff(c_4, plain, (![A_3]: (k3_xboole_0(A_3, A_3)=A_3)), inference(cnfTransformation, [status(thm)], [f_29])).
% 6.31/2.39  tff(c_161, plain, (![A_81, B_82]: (k4_xboole_0(A_81, k4_xboole_0(A_81, B_82))=k3_xboole_0(A_81, B_82))), inference(cnfTransformation, [status(thm)], [f_59])).
% 6.31/2.39  tff(c_2810, plain, (![A_210, B_211]: (r1_xboole_0(k3_xboole_0(A_210, B_211), k4_xboole_0(A_210, B_211)))), inference(superposition, [status(thm), theory('equality')], [c_161, c_22])).
% 6.31/2.39  tff(c_2831, plain, (![A_3]: (r1_xboole_0(A_3, k4_xboole_0(A_3, A_3)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_2810])).
% 6.31/2.39  tff(c_2840, plain, (![A_213, B_214, C_215]: (~r1_xboole_0(A_213, B_214) | ~r2_hidden(C_215, k3_xboole_0(A_213, B_214)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 6.31/2.39  tff(c_2870, plain, (![A_219, B_220]: (~r1_xboole_0(A_219, B_220) | k3_xboole_0(A_219, B_220)=k1_xboole_0)), inference(resolution, [status(thm)], [c_10, c_2840])).
% 6.31/2.39  tff(c_3746, plain, (![A_248]: (k3_xboole_0(A_248, k4_xboole_0(A_248, A_248))=k1_xboole_0)), inference(resolution, [status(thm)], [c_2831, c_2870])).
% 6.31/2.39  tff(c_170, plain, (![A_81, B_82]: (r1_xboole_0(k3_xboole_0(A_81, B_82), k4_xboole_0(A_81, B_82)))), inference(superposition, [status(thm), theory('equality')], [c_161, c_22])).
% 6.31/2.39  tff(c_3757, plain, (![A_248]: (r1_xboole_0(k1_xboole_0, k4_xboole_0(A_248, k4_xboole_0(A_248, A_248))))), inference(superposition, [status(thm), theory('equality')], [c_3746, c_170])).
% 6.31/2.39  tff(c_3802, plain, (![A_249]: (r1_xboole_0(k1_xboole_0, A_249))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_18, c_3757])).
% 6.31/2.39  tff(c_2854, plain, (![A_213, B_214]: (~r1_xboole_0(A_213, B_214) | k3_xboole_0(A_213, B_214)=k1_xboole_0)), inference(resolution, [status(thm)], [c_10, c_2840])).
% 6.31/2.39  tff(c_3815, plain, (![A_250]: (k3_xboole_0(k1_xboole_0, A_250)=k1_xboole_0)), inference(resolution, [status(thm)], [c_3802, c_2854])).
% 6.31/2.39  tff(c_3855, plain, (![A_1]: (k3_xboole_0(A_1, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2, c_3815])).
% 6.31/2.39  tff(c_3933, plain, (![A_259]: (k3_xboole_0(A_259, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2, c_3815])).
% 6.31/2.39  tff(c_3953, plain, (![A_259]: (k5_xboole_0(A_259, k1_xboole_0)=k4_xboole_0(A_259, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_3933, c_16])).
% 6.31/2.39  tff(c_4040, plain, (![A_261]: (k4_xboole_0(A_261, k1_xboole_0)=A_261)), inference(demodulation, [status(thm), theory('equality')], [c_20, c_3953])).
% 6.31/2.39  tff(c_4064, plain, (![A_261]: (k4_xboole_0(A_261, A_261)=k3_xboole_0(A_261, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_4040, c_18])).
% 6.31/2.39  tff(c_4081, plain, (![A_261]: (k4_xboole_0(A_261, A_261)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_3855, c_4064])).
% 6.31/2.39  tff(c_4092, plain, (![B_52]: (k1_tarski(B_52)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_4081, c_40])).
% 6.31/2.39  tff(c_52, plain, (~r2_hidden('#skF_3', '#skF_4') | r2_hidden('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_99])).
% 6.31/2.39  tff(c_85, plain, (~r2_hidden('#skF_3', '#skF_4')), inference(splitLeft, [status(thm)], [c_52])).
% 6.31/2.39  tff(c_38, plain, (![A_49, B_50]: (r1_xboole_0(k1_tarski(A_49), B_50) | r2_hidden(A_49, B_50))), inference(cnfTransformation, [status(thm)], [f_82])).
% 6.31/2.39  tff(c_212, plain, (![A_88, B_89, C_90]: (~r1_xboole_0(A_88, B_89) | ~r2_hidden(C_90, k3_xboole_0(A_88, B_89)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 6.31/2.39  tff(c_232, plain, (![A_93, B_94]: (~r1_xboole_0(A_93, B_94) | k3_xboole_0(A_93, B_94)=k1_xboole_0)), inference(resolution, [status(thm)], [c_10, c_212])).
% 6.31/2.39  tff(c_1476, plain, (![A_175, B_176]: (k3_xboole_0(k1_tarski(A_175), B_176)=k1_xboole_0 | r2_hidden(A_175, B_176))), inference(resolution, [status(thm)], [c_38, c_232])).
% 6.31/2.39  tff(c_1508, plain, (![A_175, B_176]: (k5_xboole_0(k1_tarski(A_175), k1_xboole_0)=k4_xboole_0(k1_tarski(A_175), B_176) | r2_hidden(A_175, B_176))), inference(superposition, [status(thm), theory('equality')], [c_1476, c_16])).
% 6.31/2.39  tff(c_2613, plain, (![A_205, B_206]: (k4_xboole_0(k1_tarski(A_205), B_206)=k1_tarski(A_205) | r2_hidden(A_205, B_206))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_1508])).
% 6.31/2.39  tff(c_50, plain, (k4_xboole_0(k1_tarski('#skF_3'), '#skF_4')!=k1_tarski('#skF_3') | r2_hidden('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_99])).
% 6.31/2.39  tff(c_179, plain, (k4_xboole_0(k1_tarski('#skF_3'), '#skF_4')!=k1_tarski('#skF_3')), inference(splitLeft, [status(thm)], [c_50])).
% 6.31/2.39  tff(c_2684, plain, (r2_hidden('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_2613, c_179])).
% 6.31/2.39  tff(c_2736, plain, $false, inference(negUnitSimplification, [status(thm)], [c_85, c_2684])).
% 6.31/2.39  tff(c_2737, plain, (r2_hidden('#skF_5', '#skF_6')), inference(splitRight, [status(thm)], [c_50])).
% 6.31/2.39  tff(c_24, plain, (![A_21]: (k2_tarski(A_21, A_21)=k1_tarski(A_21))), inference(cnfTransformation, [status(thm)], [f_65])).
% 6.31/2.39  tff(c_3361, plain, (![A_232, B_233, C_234]: (r1_tarski(k2_tarski(A_232, B_233), C_234) | ~r2_hidden(B_233, C_234) | ~r2_hidden(A_232, C_234))), inference(cnfTransformation, [status(thm)], [f_93])).
% 6.31/2.39  tff(c_6435, plain, (![A_326, C_327]: (r1_tarski(k1_tarski(A_326), C_327) | ~r2_hidden(A_326, C_327) | ~r2_hidden(A_326, C_327))), inference(superposition, [status(thm), theory('equality')], [c_24, c_3361])).
% 6.31/2.39  tff(c_14, plain, (![A_12, B_13]: (k4_xboole_0(A_12, B_13)=k1_xboole_0 | ~r1_tarski(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_55])).
% 6.31/2.39  tff(c_6444, plain, (![A_328, C_329]: (k4_xboole_0(k1_tarski(A_328), C_329)=k1_xboole_0 | ~r2_hidden(A_328, C_329))), inference(resolution, [status(thm)], [c_6435, c_14])).
% 6.31/2.39  tff(c_2738, plain, (k4_xboole_0(k1_tarski('#skF_3'), '#skF_4')=k1_tarski('#skF_3')), inference(splitRight, [status(thm)], [c_50])).
% 6.31/2.39  tff(c_54, plain, (k4_xboole_0(k1_tarski('#skF_3'), '#skF_4')!=k1_tarski('#skF_3') | k4_xboole_0(k1_tarski('#skF_5'), '#skF_6')=k1_tarski('#skF_5')), inference(cnfTransformation, [status(thm)], [f_99])).
% 6.31/2.39  tff(c_2797, plain, (k4_xboole_0(k1_tarski('#skF_5'), '#skF_6')=k1_tarski('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_2738, c_54])).
% 6.31/2.39  tff(c_6516, plain, (k1_tarski('#skF_5')=k1_xboole_0 | ~r2_hidden('#skF_5', '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_6444, c_2797])).
% 6.31/2.39  tff(c_6589, plain, (k1_tarski('#skF_5')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_2737, c_6516])).
% 6.31/2.39  tff(c_6591, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4092, c_6589])).
% 6.31/2.39  tff(c_6592, plain, (r2_hidden('#skF_5', '#skF_6')), inference(splitRight, [status(thm)], [c_52])).
% 6.31/2.39  tff(c_7456, plain, (![A_386, B_387, C_388]: (r1_tarski(k2_tarski(A_386, B_387), C_388) | ~r2_hidden(B_387, C_388) | ~r2_hidden(A_386, C_388))), inference(cnfTransformation, [status(thm)], [f_93])).
% 6.31/2.39  tff(c_9910, plain, (![A_473, C_474]: (r1_tarski(k1_tarski(A_473), C_474) | ~r2_hidden(A_473, C_474) | ~r2_hidden(A_473, C_474))), inference(superposition, [status(thm), theory('equality')], [c_24, c_7456])).
% 6.31/2.39  tff(c_9919, plain, (![A_475, C_476]: (k4_xboole_0(k1_tarski(A_475), C_476)=k1_xboole_0 | ~r2_hidden(A_475, C_476))), inference(resolution, [status(thm)], [c_9910, c_14])).
% 6.31/2.39  tff(c_6593, plain, (r2_hidden('#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_52])).
% 6.31/2.39  tff(c_56, plain, (~r2_hidden('#skF_3', '#skF_4') | k4_xboole_0(k1_tarski('#skF_5'), '#skF_6')=k1_tarski('#skF_5')), inference(cnfTransformation, [status(thm)], [f_99])).
% 6.31/2.39  tff(c_6682, plain, (k4_xboole_0(k1_tarski('#skF_5'), '#skF_6')=k1_tarski('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_6593, c_56])).
% 6.31/2.39  tff(c_10001, plain, (k1_tarski('#skF_5')=k1_xboole_0 | ~r2_hidden('#skF_5', '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_9919, c_6682])).
% 6.31/2.39  tff(c_10063, plain, (k1_tarski('#skF_5')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_6592, c_10001])).
% 6.31/2.39  tff(c_10065, plain, $false, inference(negUnitSimplification, [status(thm)], [c_7395, c_10063])).
% 6.31/2.39  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.31/2.39  
% 6.31/2.39  Inference rules
% 6.31/2.39  ----------------------
% 6.31/2.39  #Ref     : 0
% 6.31/2.39  #Sup     : 2441
% 6.31/2.39  #Fact    : 0
% 6.31/2.39  #Define  : 0
% 6.31/2.39  #Split   : 2
% 6.31/2.39  #Chain   : 0
% 6.31/2.39  #Close   : 0
% 6.31/2.39  
% 6.31/2.39  Ordering : KBO
% 6.31/2.39  
% 6.31/2.39  Simplification rules
% 6.31/2.39  ----------------------
% 6.31/2.39  #Subsume      : 272
% 6.31/2.39  #Demod        : 2041
% 6.31/2.39  #Tautology    : 1755
% 6.31/2.39  #SimpNegUnit  : 150
% 6.31/2.39  #BackRed      : 9
% 6.31/2.39  
% 6.31/2.39  #Partial instantiations: 0
% 6.31/2.39  #Strategies tried      : 1
% 6.31/2.39  
% 6.31/2.39  Timing (in seconds)
% 6.31/2.39  ----------------------
% 6.31/2.39  Preprocessing        : 0.35
% 6.31/2.39  Parsing              : 0.18
% 6.31/2.39  CNF conversion       : 0.03
% 6.31/2.39  Main loop            : 1.21
% 6.31/2.39  Inferencing          : 0.38
% 6.31/2.39  Reduction            : 0.52
% 6.31/2.39  Demodulation         : 0.40
% 6.31/2.39  BG Simplification    : 0.04
% 6.31/2.39  Subsumption          : 0.18
% 6.31/2.39  Abstraction          : 0.05
% 6.31/2.39  MUC search           : 0.00
% 6.31/2.39  Cooper               : 0.00
% 6.31/2.39  Total                : 1.59
% 6.31/2.39  Index Insertion      : 0.00
% 6.31/2.39  Index Deletion       : 0.00
% 6.31/2.39  Index Matching       : 0.00
% 6.31/2.39  BG Taut test         : 0.00
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0078+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:07:13 EST 2020

% Result     : Theorem 6.41s
% Output     : CNFRefutation 6.69s
% Verified   : 
% Statistics : Number of formulae       :  100 ( 247 expanded)
%              Number of leaves         :   51 ( 110 expanded)
%              Depth                    :   13
%              Number of atoms          :   88 ( 295 expanded)
%              Number of equality atoms :   61 ( 194 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_xboole_0 > r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > o_0_0_xboole_0 > k1_xboole_0 > #skF_13 > #skF_11 > #skF_18 > #skF_6 > #skF_1 > #skF_17 > #skF_4 > #skF_10 > #skF_12 > #skF_5 > #skF_19 > #skF_21 > #skF_9 > #skF_7 > #skF_20 > #skF_14 > #skF_22 > #skF_3 > #skF_2 > #skF_23 > #skF_8 > #skF_16 > #skF_15

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_13',type,(
    '#skF_13': ( $i * ( $i * $i ) ) > $i )).

tff('#skF_11',type,(
    '#skF_11': ( $i * $i ) > $i )).

tff(o_0_0_xboole_0,type,(
    o_0_0_xboole_0: $i )).

tff('#skF_18',type,(
    '#skF_18': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': ( $i * ( $i * $i ) ) > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff('#skF_17',type,(
    '#skF_17': ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * ( $i * $i ) ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff('#skF_12',type,(
    '#skF_12': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * ( $i * $i ) ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_19',type,(
    '#skF_19': ( $i * ( $i * $i ) ) > $i )).

tff('#skF_21',type,(
    '#skF_21': $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * ( $i * $i ) ) > $i )).

tff(r2_xboole_0,type,(
    r2_xboole_0: ( $i * $i ) > $o )).

tff('#skF_20',type,(
    '#skF_20': ( $i * ( $i * $i ) ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_14',type,(
    '#skF_14': ( $i * ( $i * $i ) ) > $i )).

tff('#skF_22',type,(
    '#skF_22': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * ( $i * $i ) ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_23',type,(
    '#skF_23': $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': ( $i * ( $i * $i ) ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_16',type,(
    '#skF_16': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_15',type,(
    '#skF_15': ( $i * $i ) > $i )).

tff(f_136,axiom,(
    ? [A] : v1_xboole_0(A) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT001+2.ax',rc1_xboole_0)).

tff(f_546,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_boole)).

tff(f_396,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_xboole_1)).

tff(f_573,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( k2_xboole_0(A,B) = k2_xboole_0(C,B)
          & r1_xboole_0(A,B)
          & r1_xboole_0(C,B) )
       => A = C ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_xboole_1)).

tff(f_61,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT001+2.ax',commutativity_k2_xboole_0)).

tff(f_317,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_392,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_402,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_426,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => B = k2_xboole_0(A,k4_xboole_0(B,A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_xboole_1)).

tff(f_301,axiom,(
    ! [A,B] :
      ( k2_xboole_0(A,B) = k1_xboole_0
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t15_xboole_1)).

tff(f_410,axiom,(
    ! [A,B] : k4_xboole_0(k2_xboole_0(A,B),B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).

tff(f_113,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT001+2.ax',d7_xboole_0)).

tff(f_432,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_242,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(c_112,plain,(
    v1_xboole_0('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_450,plain,(
    ! [A_294] :
      ( k1_xboole_0 = A_294
      | ~ v1_xboole_0(A_294) ) ),
    inference(cnfTransformation,[status(thm)],[f_546])).

tff(c_459,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(resolution,[status(thm)],[c_112,c_450])).

tff(c_280,plain,(
    ! [A_179,B_180] :
      ( r1_tarski(A_179,B_180)
      | k4_xboole_0(A_179,B_180) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_396])).

tff(c_2226,plain,(
    ! [A_179,B_180] :
      ( r1_tarski(A_179,B_180)
      | k4_xboole_0(A_179,B_180) != '#skF_9' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_459,c_280])).

tff(c_370,plain,(
    '#skF_21' != '#skF_23' ),
    inference(cnfTransformation,[status(thm)],[f_573])).

tff(c_6,plain,(
    ! [B_6,A_5] : k2_xboole_0(B_6,A_5) = k2_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_234,plain,(
    ! [A_124] : k2_xboole_0(A_124,k1_xboole_0) = A_124 ),
    inference(cnfTransformation,[status(thm)],[f_317])).

tff(c_461,plain,(
    ! [A_124] : k2_xboole_0(A_124,'#skF_9') = A_124 ),
    inference(demodulation,[status(thm),theory(equality)],[c_459,c_234])).

tff(c_278,plain,(
    ! [A_177,B_178] : r1_tarski(k4_xboole_0(A_177,B_178),A_177) ),
    inference(cnfTransformation,[status(thm)],[f_392])).

tff(c_286,plain,(
    ! [A_183,B_184] : k2_xboole_0(A_183,k4_xboole_0(B_184,A_183)) = k2_xboole_0(A_183,B_184) ),
    inference(cnfTransformation,[status(thm)],[f_402])).

tff(c_302,plain,(
    ! [A_201,B_202] :
      ( k2_xboole_0(A_201,k4_xboole_0(B_202,A_201)) = B_202
      | ~ r1_tarski(A_201,B_202) ) ),
    inference(cnfTransformation,[status(thm)],[f_426])).

tff(c_1567,plain,(
    ! [A_365,B_366] :
      ( k2_xboole_0(A_365,B_366) = B_366
      | ~ r1_tarski(A_365,B_366) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_286,c_302])).

tff(c_1703,plain,(
    ! [A_369,B_370] : k2_xboole_0(k4_xboole_0(A_369,B_370),A_369) = A_369 ),
    inference(resolution,[status(thm)],[c_278,c_1567])).

tff(c_224,plain,(
    ! [A_111,B_112] :
      ( k1_xboole_0 = A_111
      | k2_xboole_0(A_111,B_112) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_301])).

tff(c_1212,plain,(
    ! [A_111,B_112] :
      ( A_111 = '#skF_9'
      | k2_xboole_0(A_111,B_112) != '#skF_9' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_459,c_459,c_224])).

tff(c_1715,plain,(
    ! [A_369,B_370] :
      ( k4_xboole_0(A_369,B_370) = '#skF_9'
      | A_369 != '#skF_9' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1703,c_1212])).

tff(c_3530,plain,(
    ! [A_426,B_427] : k2_xboole_0(A_426,k4_xboole_0(B_427,A_426)) = k2_xboole_0(A_426,B_427) ),
    inference(cnfTransformation,[status(thm)],[f_402])).

tff(c_3583,plain,(
    ! [B_370,A_369] :
      ( k2_xboole_0(B_370,A_369) = k2_xboole_0(B_370,'#skF_9')
      | A_369 != '#skF_9' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1715,c_3530])).

tff(c_3637,plain,(
    ! [B_428,A_429] :
      ( k2_xboole_0(B_428,A_429) = B_428
      | A_429 != '#skF_9' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_461,c_3583])).

tff(c_3836,plain,(
    ! [A_5] : k2_xboole_0('#skF_9',A_5) = A_5 ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_3637])).

tff(c_292,plain,(
    ! [A_187,B_188] : k4_xboole_0(k2_xboole_0(A_187,B_188),B_188) = k4_xboole_0(A_187,B_188) ),
    inference(cnfTransformation,[status(thm)],[f_410])).

tff(c_376,plain,(
    k2_xboole_0('#skF_21','#skF_22') = k2_xboole_0('#skF_23','#skF_22') ),
    inference(cnfTransformation,[status(thm)],[f_573])).

tff(c_4406,plain,(
    ! [A_444,B_445] : k4_xboole_0(k2_xboole_0(A_444,B_445),B_445) = k4_xboole_0(A_444,B_445) ),
    inference(cnfTransformation,[status(thm)],[f_410])).

tff(c_4494,plain,(
    k4_xboole_0(k2_xboole_0('#skF_23','#skF_22'),'#skF_22') = k4_xboole_0('#skF_21','#skF_22') ),
    inference(superposition,[status(thm),theory(equality)],[c_376,c_4406])).

tff(c_4511,plain,(
    k4_xboole_0('#skF_21','#skF_22') = k4_xboole_0('#skF_23','#skF_22') ),
    inference(demodulation,[status(thm),theory(equality)],[c_292,c_4494])).

tff(c_1601,plain,(
    ! [A_177,B_178] : k2_xboole_0(k4_xboole_0(A_177,B_178),A_177) = A_177 ),
    inference(resolution,[status(thm)],[c_278,c_1567])).

tff(c_4537,plain,(
    k2_xboole_0(k4_xboole_0('#skF_23','#skF_22'),'#skF_21') = '#skF_21' ),
    inference(superposition,[status(thm),theory(equality)],[c_4511,c_1601])).

tff(c_4661,plain,(
    k2_xboole_0('#skF_21',k4_xboole_0('#skF_23','#skF_22')) = '#skF_21' ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_4537])).

tff(c_374,plain,(
    r1_xboole_0('#skF_21','#skF_22') ),
    inference(cnfTransformation,[status(thm)],[f_573])).

tff(c_80,plain,(
    ! [A_40,B_41] :
      ( k3_xboole_0(A_40,B_41) = k1_xboole_0
      | ~ r1_xboole_0(A_40,B_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_1917,plain,(
    ! [A_375,B_376] :
      ( k3_xboole_0(A_375,B_376) = '#skF_9'
      | ~ r1_xboole_0(A_375,B_376) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_459,c_80])).

tff(c_1942,plain,(
    k3_xboole_0('#skF_21','#skF_22') = '#skF_9' ),
    inference(resolution,[status(thm)],[c_374,c_1917])).

tff(c_4815,plain,(
    ! [A_446,B_447] : k4_xboole_0(A_446,k4_xboole_0(A_446,B_447)) = k3_xboole_0(A_446,B_447) ),
    inference(cnfTransformation,[status(thm)],[f_432])).

tff(c_4860,plain,(
    k4_xboole_0('#skF_21',k4_xboole_0('#skF_23','#skF_22')) = k3_xboole_0('#skF_21','#skF_22') ),
    inference(superposition,[status(thm),theory(equality)],[c_4511,c_4815])).

tff(c_4910,plain,(
    k4_xboole_0('#skF_21',k4_xboole_0('#skF_23','#skF_22')) = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1942,c_4860])).

tff(c_4931,plain,(
    k2_xboole_0(k4_xboole_0('#skF_23','#skF_22'),'#skF_21') = k2_xboole_0(k4_xboole_0('#skF_23','#skF_22'),'#skF_9') ),
    inference(superposition,[status(thm),theory(equality)],[c_4910,c_286])).

tff(c_4969,plain,(
    k4_xboole_0('#skF_23','#skF_22') = '#skF_21' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3836,c_4661,c_6,c_6,c_4931])).

tff(c_5021,plain,(
    r1_tarski('#skF_21','#skF_23') ),
    inference(superposition,[status(thm),theory(equality)],[c_4969,c_278])).

tff(c_192,plain,(
    ! [B_82,A_81] :
      ( B_82 = A_81
      | ~ r1_tarski(B_82,A_81)
      | ~ r1_tarski(A_81,B_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_242])).

tff(c_5052,plain,
    ( '#skF_21' = '#skF_23'
    | ~ r1_tarski('#skF_23','#skF_21') ),
    inference(resolution,[status(thm)],[c_5021,c_192])).

tff(c_5064,plain,(
    ~ r1_tarski('#skF_23','#skF_21') ),
    inference(negUnitSimplification,[status(thm)],[c_370,c_5052])).

tff(c_5075,plain,(
    k4_xboole_0('#skF_23','#skF_21') != '#skF_9' ),
    inference(resolution,[status(thm)],[c_2226,c_5064])).

tff(c_372,plain,(
    r1_xboole_0('#skF_23','#skF_22') ),
    inference(cnfTransformation,[status(thm)],[f_573])).

tff(c_1943,plain,(
    k3_xboole_0('#skF_23','#skF_22') = '#skF_9' ),
    inference(resolution,[status(thm)],[c_372,c_1917])).

tff(c_308,plain,(
    ! [A_207,B_208] : k4_xboole_0(A_207,k4_xboole_0(A_207,B_208)) = k3_xboole_0(A_207,B_208) ),
    inference(cnfTransformation,[status(thm)],[f_432])).

tff(c_4994,plain,(
    k4_xboole_0('#skF_23','#skF_21') = k3_xboole_0('#skF_23','#skF_22') ),
    inference(superposition,[status(thm),theory(equality)],[c_4969,c_308])).

tff(c_5030,plain,(
    k4_xboole_0('#skF_23','#skF_21') = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1943,c_4994])).

tff(c_5397,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_5075,c_5030])).
%------------------------------------------------------------------------------

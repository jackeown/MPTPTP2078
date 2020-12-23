%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0090+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:07:13 EST 2020

% Result     : Theorem 7.45s
% Output     : CNFRefutation 7.84s
% Verified   : 
% Statistics : Number of formulae       :  103 ( 149 expanded)
%              Number of leaves         :   50 (  74 expanded)
%              Depth                    :    9
%              Number of atoms          :   87 ( 157 expanded)
%              Number of equality atoms :   55 (  87 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_xboole_0 > r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > o_0_0_xboole_0 > k1_xboole_0 > #skF_13 > #skF_11 > #skF_18 > #skF_6 > #skF_1 > #skF_17 > #skF_4 > #skF_10 > #skF_12 > #skF_5 > #skF_19 > #skF_21 > #skF_9 > #skF_7 > #skF_20 > #skF_14 > #skF_22 > #skF_3 > #skF_2 > #skF_24 > #skF_23 > #skF_8 > #skF_16 > #skF_15

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

tff('#skF_24',type,(
    '#skF_24': $i )).

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

tff(f_638,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_xboole_0(A,B)
      <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_136,axiom,(
    ? [A] : v1_xboole_0(A) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT001+2.ax',rc1_xboole_0)).

tff(f_546,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_boole)).

tff(f_113,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT001+2.ax',d7_xboole_0)).

tff(f_442,axiom,(
    ! [A,B] : k2_xboole_0(k3_xboole_0(A,B),k4_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).

tff(f_61,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT001+2.ax',commutativity_k2_xboole_0)).

tff(f_317,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_616,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

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

tff(c_402,plain,
    ( ~ r1_xboole_0('#skF_21','#skF_22')
    | r1_xboole_0('#skF_23','#skF_24') ),
    inference(cnfTransformation,[status(thm)],[f_638])).

tff(c_430,plain,(
    ~ r1_xboole_0('#skF_21','#skF_22') ),
    inference(splitLeft,[status(thm)],[c_402])).

tff(c_400,plain,
    ( k4_xboole_0('#skF_21','#skF_22') = '#skF_21'
    | k4_xboole_0('#skF_23','#skF_24') != '#skF_23' ),
    inference(cnfTransformation,[status(thm)],[f_638])).

tff(c_683,plain,(
    k4_xboole_0('#skF_23','#skF_24') != '#skF_23' ),
    inference(splitLeft,[status(thm)],[c_400])).

tff(c_404,plain,
    ( k4_xboole_0('#skF_21','#skF_22') = '#skF_21'
    | r1_xboole_0('#skF_23','#skF_24') ),
    inference(cnfTransformation,[status(thm)],[f_638])).

tff(c_520,plain,(
    r1_xboole_0('#skF_23','#skF_24') ),
    inference(splitLeft,[status(thm)],[c_404])).

tff(c_112,plain,(
    v1_xboole_0('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_492,plain,(
    ! [A_329] :
      ( k1_xboole_0 = A_329
      | ~ v1_xboole_0(A_329) ) ),
    inference(cnfTransformation,[status(thm)],[f_546])).

tff(c_501,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(resolution,[status(thm)],[c_112,c_492])).

tff(c_80,plain,(
    ! [A_40,B_41] :
      ( k3_xboole_0(A_40,B_41) = k1_xboole_0
      | ~ r1_xboole_0(A_40,B_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_1642,plain,(
    ! [A_413,B_414] :
      ( k3_xboole_0(A_413,B_414) = '#skF_9'
      | ~ r1_xboole_0(A_413,B_414) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_501,c_80])).

tff(c_1672,plain,(
    k3_xboole_0('#skF_23','#skF_24') = '#skF_9' ),
    inference(resolution,[status(thm)],[c_520,c_1642])).

tff(c_3373,plain,(
    ! [A_469,B_470] : k2_xboole_0(k3_xboole_0(A_469,B_470),k4_xboole_0(A_469,B_470)) = A_469 ),
    inference(cnfTransformation,[status(thm)],[f_442])).

tff(c_3436,plain,(
    k2_xboole_0('#skF_9',k4_xboole_0('#skF_23','#skF_24')) = '#skF_23' ),
    inference(superposition,[status(thm),theory(equality)],[c_1672,c_3373])).

tff(c_880,plain,(
    ! [B_372,A_373] : k2_xboole_0(B_372,A_373) = k2_xboole_0(A_373,B_372) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_234,plain,(
    ! [A_124] : k2_xboole_0(A_124,k1_xboole_0) = A_124 ),
    inference(cnfTransformation,[status(thm)],[f_317])).

tff(c_504,plain,(
    ! [A_124] : k2_xboole_0(A_124,'#skF_9') = A_124 ),
    inference(demodulation,[status(thm),theory(equality)],[c_501,c_234])).

tff(c_914,plain,(
    ! [A_373] : k2_xboole_0('#skF_9',A_373) = A_373 ),
    inference(superposition,[status(thm),theory(equality)],[c_880,c_504])).

tff(c_3854,plain,(
    k4_xboole_0('#skF_23','#skF_24') = '#skF_23' ),
    inference(superposition,[status(thm),theory(equality)],[c_3436,c_914])).

tff(c_3881,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_683,c_3854])).

tff(c_3882,plain,(
    k4_xboole_0('#skF_21','#skF_22') = '#skF_21' ),
    inference(splitRight,[status(thm)],[c_400])).

tff(c_386,plain,(
    ! [A_297,B_298] : r1_xboole_0(k4_xboole_0(A_297,B_298),B_298) ),
    inference(cnfTransformation,[status(thm)],[f_616])).

tff(c_3890,plain,(
    r1_xboole_0('#skF_21','#skF_22') ),
    inference(superposition,[status(thm),theory(equality)],[c_3882,c_386])).

tff(c_3895,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_430,c_3890])).

tff(c_3896,plain,(
    k4_xboole_0('#skF_21','#skF_22') = '#skF_21' ),
    inference(splitRight,[status(thm)],[c_404])).

tff(c_3975,plain,(
    ! [A_488,B_489] : r1_xboole_0(k4_xboole_0(A_488,B_489),B_489) ),
    inference(cnfTransformation,[status(thm)],[f_616])).

tff(c_3981,plain,(
    r1_xboole_0('#skF_21','#skF_22') ),
    inference(superposition,[status(thm),theory(equality)],[c_3896,c_3975])).

tff(c_3986,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_430,c_3981])).

tff(c_3988,plain,(
    r1_xboole_0('#skF_21','#skF_22') ),
    inference(splitRight,[status(thm)],[c_402])).

tff(c_398,plain,
    ( ~ r1_xboole_0('#skF_21','#skF_22')
    | k4_xboole_0('#skF_23','#skF_24') != '#skF_23' ),
    inference(cnfTransformation,[status(thm)],[f_638])).

tff(c_4103,plain,(
    k4_xboole_0('#skF_23','#skF_24') != '#skF_23' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3988,c_398])).

tff(c_3987,plain,(
    r1_xboole_0('#skF_23','#skF_24') ),
    inference(splitRight,[status(thm)],[c_402])).

tff(c_3989,plain,(
    ! [A_490] :
      ( k1_xboole_0 = A_490
      | ~ v1_xboole_0(A_490) ) ),
    inference(cnfTransformation,[status(thm)],[f_546])).

tff(c_3998,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(resolution,[status(thm)],[c_112,c_3989])).

tff(c_5698,plain,(
    ! [A_597,B_598] :
      ( k3_xboole_0(A_597,B_598) = '#skF_9'
      | ~ r1_xboole_0(A_597,B_598) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3998,c_80])).

tff(c_5736,plain,(
    k3_xboole_0('#skF_23','#skF_24') = '#skF_9' ),
    inference(resolution,[status(thm)],[c_3987,c_5698])).

tff(c_8969,plain,(
    ! [A_707,B_708] : k2_xboole_0(k3_xboole_0(A_707,B_708),k4_xboole_0(A_707,B_708)) = A_707 ),
    inference(cnfTransformation,[status(thm)],[f_442])).

tff(c_9060,plain,(
    k2_xboole_0('#skF_9',k4_xboole_0('#skF_23','#skF_24')) = '#skF_23' ),
    inference(superposition,[status(thm),theory(equality)],[c_5736,c_8969])).

tff(c_6,plain,(
    ! [B_6,A_5] : k2_xboole_0(B_6,A_5) = k2_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_4082,plain,(
    ! [A_124] : k2_xboole_0(A_124,'#skF_9') = A_124 ),
    inference(demodulation,[status(thm),theory(equality)],[c_3998,c_234])).

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

tff(c_6462,plain,(
    ! [A_609,B_610] :
      ( k2_xboole_0(A_609,B_610) = B_610
      | ~ r1_tarski(A_609,B_610) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_286,c_302])).

tff(c_6501,plain,(
    ! [A_611,B_612] : k2_xboole_0(k4_xboole_0(A_611,B_612),A_611) = A_611 ),
    inference(resolution,[status(thm)],[c_278,c_6462])).

tff(c_224,plain,(
    ! [A_111,B_112] :
      ( k1_xboole_0 = A_111
      | k2_xboole_0(A_111,B_112) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_301])).

tff(c_4443,plain,(
    ! [A_111,B_112] :
      ( A_111 = '#skF_9'
      | k2_xboole_0(A_111,B_112) != '#skF_9' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3998,c_3998,c_224])).

tff(c_6977,plain,(
    ! [A_622,B_623] :
      ( k4_xboole_0(A_622,B_623) = '#skF_9'
      | A_622 != '#skF_9' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6501,c_4443])).

tff(c_6992,plain,(
    ! [B_623,A_622] :
      ( k2_xboole_0(B_623,A_622) = k2_xboole_0(B_623,'#skF_9')
      | A_622 != '#skF_9' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6977,c_286])).

tff(c_7269,plain,(
    ! [B_636,A_637] :
      ( k2_xboole_0(B_636,A_637) = B_636
      | A_637 != '#skF_9' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4082,c_6992])).

tff(c_7380,plain,(
    ! [A_5,B_6] :
      ( k2_xboole_0(A_5,B_6) = B_6
      | A_5 != '#skF_9' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_7269])).

tff(c_9147,plain,(
    k4_xboole_0('#skF_23','#skF_24') = '#skF_23' ),
    inference(superposition,[status(thm),theory(equality)],[c_9060,c_7380])).

tff(c_9208,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4103,c_9147])).
%------------------------------------------------------------------------------

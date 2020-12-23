%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0071+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:07:12 EST 2020

% Result     : Theorem 9.96s
% Output     : CNFRefutation 9.96s
% Verified   : 
% Statistics : Number of formulae       :   79 (  97 expanded)
%              Number of leaves         :   48 (  58 expanded)
%              Depth                    :    8
%              Number of atoms          :   62 (  95 expanded)
%              Number of equality atoms :   25 (  36 expanded)
%              Maximal formula depth    :    9 (   3 average)
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

tff(f_63,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT001+2.ax',commutativity_k3_xboole_0)).

tff(f_136,axiom,(
    ? [A] : v1_xboole_0(A) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT001+2.ax',rc1_xboole_0)).

tff(f_507,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_boole)).

tff(f_113,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT001+2.ax',d7_xboole_0)).

tff(f_503,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( r1_tarski(A,B)
          & r1_tarski(C,D)
          & r1_xboole_0(B,D) )
       => r1_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_xboole_1)).

tff(f_402,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_426,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => B = k2_xboole_0(A,k4_xboole_0(B,A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_xboole_1)).

tff(f_362,axiom,(
    ! [A,B,C] : r1_tarski(k3_xboole_0(A,B),k2_xboole_0(A,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_xboole_1)).

tff(f_494,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_xboole_0(B,C) )
     => r1_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_xboole_1)).

tff(f_360,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(c_8,plain,(
    ! [B_8,A_7] : k3_xboole_0(B_8,A_7) = k3_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_112,plain,(
    v1_xboole_0('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_400,plain,(
    ! [A_274] :
      ( k1_xboole_0 = A_274
      | ~ v1_xboole_0(A_274) ) ),
    inference(cnfTransformation,[status(thm)],[f_507])).

tff(c_409,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(resolution,[status(thm)],[c_112,c_400])).

tff(c_82,plain,(
    ! [A_40,B_41] :
      ( r1_xboole_0(A_40,B_41)
      | k3_xboole_0(A_40,B_41) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_2151,plain,(
    ! [A_358,B_359] :
      ( r1_xboole_0(A_358,B_359)
      | k3_xboole_0(A_358,B_359) != '#skF_9' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_409,c_82])).

tff(c_346,plain,(
    ~ r1_xboole_0('#skF_21','#skF_23') ),
    inference(cnfTransformation,[status(thm)],[f_503])).

tff(c_2156,plain,(
    k3_xboole_0('#skF_21','#skF_23') != '#skF_9' ),
    inference(resolution,[status(thm)],[c_2151,c_346])).

tff(c_2159,plain,(
    k3_xboole_0('#skF_23','#skF_21') != '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_2156])).

tff(c_352,plain,(
    r1_tarski('#skF_21','#skF_22') ),
    inference(cnfTransformation,[status(thm)],[f_503])).

tff(c_286,plain,(
    ! [A_183,B_184] : k2_xboole_0(A_183,k4_xboole_0(B_184,A_183)) = k2_xboole_0(A_183,B_184) ),
    inference(cnfTransformation,[status(thm)],[f_402])).

tff(c_302,plain,(
    ! [A_201,B_202] :
      ( k2_xboole_0(A_201,k4_xboole_0(B_202,A_201)) = B_202
      | ~ r1_tarski(A_201,B_202) ) ),
    inference(cnfTransformation,[status(thm)],[f_426])).

tff(c_1330,plain,(
    ! [A_339,B_340] :
      ( k2_xboole_0(A_339,B_340) = B_340
      | ~ r1_tarski(A_339,B_340) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_286,c_302])).

tff(c_1367,plain,(
    k2_xboole_0('#skF_21','#skF_22') = '#skF_22' ),
    inference(resolution,[status(thm)],[c_352,c_1330])).

tff(c_1920,plain,(
    ! [A_351,B_352,C_353] : r1_tarski(k3_xboole_0(A_351,B_352),k2_xboole_0(A_351,C_353)) ),
    inference(cnfTransformation,[status(thm)],[f_362])).

tff(c_2051,plain,(
    ! [B_355] : r1_tarski(k3_xboole_0('#skF_21',B_355),'#skF_22') ),
    inference(superposition,[status(thm),theory(equality)],[c_1367,c_1920])).

tff(c_2067,plain,(
    ! [B_8] : r1_tarski(k3_xboole_0(B_8,'#skF_21'),'#skF_22') ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_2051])).

tff(c_348,plain,(
    r1_xboole_0('#skF_22','#skF_24') ),
    inference(cnfTransformation,[status(thm)],[f_503])).

tff(c_13234,plain,(
    ! [A_595,C_596,B_597] :
      ( r1_xboole_0(A_595,C_596)
      | ~ r1_xboole_0(B_597,C_596)
      | ~ r1_tarski(A_595,B_597) ) ),
    inference(cnfTransformation,[status(thm)],[f_494])).

tff(c_13256,plain,(
    ! [A_598] :
      ( r1_xboole_0(A_598,'#skF_24')
      | ~ r1_tarski(A_598,'#skF_22') ) ),
    inference(resolution,[status(thm)],[c_348,c_13234])).

tff(c_80,plain,(
    ! [A_40,B_41] :
      ( k3_xboole_0(A_40,B_41) = k1_xboole_0
      | ~ r1_xboole_0(A_40,B_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_2417,plain,(
    ! [A_40,B_41] :
      ( k3_xboole_0(A_40,B_41) = '#skF_9'
      | ~ r1_xboole_0(A_40,B_41) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_409,c_80])).

tff(c_13504,plain,(
    ! [A_607] :
      ( k3_xboole_0(A_607,'#skF_24') = '#skF_9'
      | ~ r1_tarski(A_607,'#skF_22') ) ),
    inference(resolution,[status(thm)],[c_13256,c_2417])).

tff(c_15404,plain,(
    ! [B_620] : k3_xboole_0(k3_xboole_0(B_620,'#skF_21'),'#skF_24') = '#skF_9' ),
    inference(resolution,[status(thm)],[c_2067,c_13504])).

tff(c_350,plain,(
    r1_tarski('#skF_23','#skF_24') ),
    inference(cnfTransformation,[status(thm)],[f_503])).

tff(c_1368,plain,(
    k2_xboole_0('#skF_23','#skF_24') = '#skF_24' ),
    inference(resolution,[status(thm)],[c_350,c_1330])).

tff(c_1950,plain,(
    ! [B_352] : r1_tarski(k3_xboole_0('#skF_23',B_352),'#skF_24') ),
    inference(superposition,[status(thm),theory(equality)],[c_1368,c_1920])).

tff(c_2832,plain,(
    ! [A_378,B_379] :
      ( k3_xboole_0(A_378,B_379) = A_378
      | ~ r1_tarski(A_378,B_379) ) ),
    inference(cnfTransformation,[status(thm)],[f_360])).

tff(c_2889,plain,(
    ! [B_352] : k3_xboole_0(k3_xboole_0('#skF_23',B_352),'#skF_24') = k3_xboole_0('#skF_23',B_352) ),
    inference(resolution,[status(thm)],[c_1950,c_2832])).

tff(c_15443,plain,(
    k3_xboole_0('#skF_23','#skF_21') = '#skF_9' ),
    inference(superposition,[status(thm),theory(equality)],[c_15404,c_2889])).

tff(c_15567,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2159,c_15443])).
%------------------------------------------------------------------------------

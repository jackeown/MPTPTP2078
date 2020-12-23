%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0073+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:07:12 EST 2020

% Result     : Theorem 5.42s
% Output     : CNFRefutation 5.42s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 150 expanded)
%              Number of leaves         :   42 (  72 expanded)
%              Depth                    :    9
%              Number of atoms          :   54 ( 190 expanded)
%              Number of equality atoms :   28 ( 100 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_xboole_0 > r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > o_0_0_xboole_0 > k1_xboole_0 > #skF_13 > #skF_11 > #skF_18 > #skF_6 > #skF_1 > #skF_17 > #skF_4 > #skF_10 > #skF_12 > #skF_5 > #skF_19 > #skF_21 > #skF_9 > #skF_7 > #skF_20 > #skF_14 > #skF_22 > #skF_3 > #skF_2 > #skF_8 > #skF_16 > #skF_15

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
    file('/export/starexec/sandbox/benchmark/Axioms/MPT001+2.ax',rc1_xboole_0)).

tff(f_521,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_boole)).

tff(f_517,negated_conjecture,(
    ~ ! [A] :
        ( ~ ( ~ r1_xboole_0(A,A)
            & A = k1_xboole_0 )
        & ~ ( A != k1_xboole_0
            & r1_xboole_0(A,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_xboole_1)).

tff(f_504,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_113,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT001+2.ax',d7_xboole_0)).

tff(f_127,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT001+2.ax',idempotence_k3_xboole_0)).

tff(c_112,plain,(
    v1_xboole_0('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_432,plain,(
    ! [A_282] :
      ( k1_xboole_0 = A_282
      | ~ v1_xboole_0(A_282) ) ),
    inference(cnfTransformation,[status(thm)],[f_521])).

tff(c_441,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(resolution,[status(thm)],[c_112,c_432])).

tff(c_352,plain,
    ( k1_xboole_0 != '#skF_21'
    | k1_xboole_0 = '#skF_22' ),
    inference(cnfTransformation,[status(thm)],[f_517])).

tff(c_389,plain,(
    k1_xboole_0 != '#skF_21' ),
    inference(splitLeft,[status(thm)],[c_352])).

tff(c_446,plain,(
    '#skF_21' != '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_441,c_389])).

tff(c_350,plain,
    ( r1_xboole_0('#skF_21','#skF_21')
    | k1_xboole_0 = '#skF_22' ),
    inference(cnfTransformation,[status(thm)],[f_517])).

tff(c_540,plain,
    ( r1_xboole_0('#skF_21','#skF_21')
    | '#skF_9' = '#skF_22' ),
    inference(demodulation,[status(thm),theory(equality)],[c_441,c_350])).

tff(c_541,plain,(
    '#skF_9' = '#skF_22' ),
    inference(splitLeft,[status(thm)],[c_540])).

tff(c_550,plain,(
    '#skF_21' != '#skF_22' ),
    inference(demodulation,[status(thm),theory(equality)],[c_541,c_446])).

tff(c_348,plain,(
    ! [A_257] : r1_xboole_0(A_257,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_504])).

tff(c_447,plain,(
    ! [A_257] : r1_xboole_0(A_257,'#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_441,c_348])).

tff(c_549,plain,(
    ! [A_257] : r1_xboole_0(A_257,'#skF_22') ),
    inference(demodulation,[status(thm),theory(equality)],[c_541,c_447])).

tff(c_354,plain,
    ( r1_xboole_0('#skF_21','#skF_21')
    | ~ r1_xboole_0('#skF_22','#skF_22') ),
    inference(cnfTransformation,[status(thm)],[f_517])).

tff(c_584,plain,(
    r1_xboole_0('#skF_21','#skF_21') ),
    inference(demodulation,[status(thm),theory(equality)],[c_549,c_354])).

tff(c_552,plain,(
    k1_xboole_0 = '#skF_22' ),
    inference(demodulation,[status(thm),theory(equality)],[c_541,c_441])).

tff(c_80,plain,(
    ! [A_40,B_41] :
      ( k3_xboole_0(A_40,B_41) = k1_xboole_0
      | ~ r1_xboole_0(A_40,B_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_2379,plain,(
    ! [A_395,B_396] :
      ( k3_xboole_0(A_395,B_396) = '#skF_22'
      | ~ r1_xboole_0(A_395,B_396) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_552,c_80])).

tff(c_2395,plain,(
    k3_xboole_0('#skF_21','#skF_21') = '#skF_22' ),
    inference(resolution,[status(thm)],[c_584,c_2379])).

tff(c_106,plain,(
    ! [A_46] : k3_xboole_0(A_46,A_46) = A_46 ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_2434,plain,(
    '#skF_21' = '#skF_22' ),
    inference(superposition,[status(thm),theory(equality)],[c_2395,c_106])).

tff(c_2452,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_550,c_2434])).

tff(c_2453,plain,(
    r1_xboole_0('#skF_21','#skF_21') ),
    inference(splitRight,[status(thm)],[c_540])).

tff(c_3350,plain,(
    ! [A_460,B_461] :
      ( k3_xboole_0(A_460,B_461) = '#skF_9'
      | ~ r1_xboole_0(A_460,B_461) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_441,c_80])).

tff(c_3362,plain,(
    k3_xboole_0('#skF_21','#skF_21') = '#skF_9' ),
    inference(resolution,[status(thm)],[c_2453,c_3350])).

tff(c_3386,plain,(
    '#skF_21' = '#skF_9' ),
    inference(superposition,[status(thm),theory(equality)],[c_3362,c_106])).

tff(c_3399,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_446,c_3386])).

tff(c_3400,plain,(
    k1_xboole_0 = '#skF_22' ),
    inference(splitRight,[status(thm)],[c_352])).

tff(c_3402,plain,(
    ! [A_257] : r1_xboole_0(A_257,'#skF_22') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3400,c_348])).

tff(c_3401,plain,(
    k1_xboole_0 = '#skF_21' ),
    inference(splitRight,[status(thm)],[c_352])).

tff(c_3411,plain,(
    '#skF_21' = '#skF_22' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3400,c_3401])).

tff(c_356,plain,
    ( k1_xboole_0 != '#skF_21'
    | ~ r1_xboole_0('#skF_22','#skF_22') ),
    inference(cnfTransformation,[status(thm)],[f_517])).

tff(c_3417,plain,(
    ~ r1_xboole_0('#skF_22','#skF_22') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3411,c_3400,c_356])).

tff(c_3426,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3402,c_3417])).
%------------------------------------------------------------------------------

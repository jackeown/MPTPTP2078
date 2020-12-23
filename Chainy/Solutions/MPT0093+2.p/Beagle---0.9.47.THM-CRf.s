%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0093+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:07:14 EST 2020

% Result     : Theorem 10.30s
% Output     : CNFRefutation 10.30s
% Verified   : 
% Statistics : Number of formulae       :   58 (  60 expanded)
%              Number of leaves         :   43 (  45 expanded)
%              Depth                    :    6
%              Number of atoms          :   27 (  33 expanded)
%              Number of equality atoms :   11 (  11 expanded)
%              Maximal formula depth    :    7 (   3 average)
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

tff(f_656,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( r1_tarski(A,B)
          & r1_xboole_0(A,C) )
       => r1_tarski(A,k4_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_xboole_1)).

tff(f_637,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_360,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_434,axiom,(
    ! [A,B,C] : k3_xboole_0(A,k4_xboole_0(B,C)) = k4_xboole_0(k3_xboole_0(A,B),C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).

tff(f_63,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT001+2.ax',commutativity_k3_xboole_0)).

tff(f_305,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(c_406,plain,(
    ~ r1_tarski('#skF_21',k4_xboole_0('#skF_22','#skF_23')) ),
    inference(cnfTransformation,[status(thm)],[f_656])).

tff(c_408,plain,(
    r1_xboole_0('#skF_21','#skF_23') ),
    inference(cnfTransformation,[status(thm)],[f_656])).

tff(c_1424,plain,(
    ! [A_405,B_406] :
      ( k4_xboole_0(A_405,B_406) = A_405
      | ~ r1_xboole_0(A_405,B_406) ) ),
    inference(cnfTransformation,[status(thm)],[f_637])).

tff(c_1450,plain,(
    k4_xboole_0('#skF_21','#skF_23') = '#skF_21' ),
    inference(resolution,[status(thm)],[c_408,c_1424])).

tff(c_410,plain,(
    r1_tarski('#skF_21','#skF_22') ),
    inference(cnfTransformation,[status(thm)],[f_656])).

tff(c_1587,plain,(
    ! [A_411,B_412] :
      ( k3_xboole_0(A_411,B_412) = A_411
      | ~ r1_tarski(A_411,B_412) ) ),
    inference(cnfTransformation,[status(thm)],[f_360])).

tff(c_1623,plain,(
    k3_xboole_0('#skF_21','#skF_22') = '#skF_21' ),
    inference(resolution,[status(thm)],[c_410,c_1587])).

tff(c_18219,plain,(
    ! [A_763,B_764,C_765] : k4_xboole_0(k3_xboole_0(A_763,B_764),C_765) = k3_xboole_0(A_763,k4_xboole_0(B_764,C_765)) ),
    inference(cnfTransformation,[status(thm)],[f_434])).

tff(c_18927,plain,(
    ! [C_769] : k3_xboole_0('#skF_21',k4_xboole_0('#skF_22',C_769)) = k4_xboole_0('#skF_21',C_769) ),
    inference(superposition,[status(thm),theory(equality)],[c_1623,c_18219])).

tff(c_1027,plain,(
    ! [B_386,A_387] : k3_xboole_0(B_386,A_387) = k3_xboole_0(A_387,B_386) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_228,plain,(
    ! [A_116,B_117] : r1_tarski(k3_xboole_0(A_116,B_117),A_116) ),
    inference(cnfTransformation,[status(thm)],[f_305])).

tff(c_1050,plain,(
    ! [B_386,A_387] : r1_tarski(k3_xboole_0(B_386,A_387),A_387) ),
    inference(superposition,[status(thm),theory(equality)],[c_1027,c_228])).

tff(c_19443,plain,(
    ! [C_775] : r1_tarski(k4_xboole_0('#skF_21',C_775),k4_xboole_0('#skF_22',C_775)) ),
    inference(superposition,[status(thm),theory(equality)],[c_18927,c_1050])).

tff(c_19544,plain,(
    r1_tarski('#skF_21',k4_xboole_0('#skF_22','#skF_23')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1450,c_19443])).

tff(c_19581,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_406,c_19544])).
%------------------------------------------------------------------------------

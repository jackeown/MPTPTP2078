%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0068+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:07:12 EST 2020

% Result     : Theorem 6.46s
% Output     : CNFRefutation 6.46s
% Verified   : 
% Statistics : Number of formulae       :   63 (  76 expanded)
%              Number of leaves         :   43 (  49 expanded)
%              Depth                    :    8
%              Number of atoms          :   49 (  67 expanded)
%              Number of equality atoms :   17 (  26 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_xboole_0 > r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > o_0_0_xboole_0 > k1_xboole_0 > #skF_13 > #skF_11 > #skF_18 > #skF_6 > #skF_1 > #skF_17 > #skF_4 > #skF_10 > #skF_12 > #skF_5 > #skF_19 > #skF_21 > #skF_9 > #skF_7 > #skF_20 > #skF_14 > #skF_3 > #skF_2 > #skF_8 > #skF_16 > #skF_15

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
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT001+2.ax',rc1_xboole_0)).

tff(f_490,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_boole)).

tff(f_486,negated_conjecture,(
    ~ ! [A] :
        ( A != k1_xboole_0
       => r2_xboole_0(k1_xboole_0,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_xboole_1)).

tff(f_79,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT001+2.ax',d3_tarski)).

tff(f_127,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT001+2.ax',idempotence_k3_xboole_0)).

tff(f_113,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT001+2.ax',d7_xboole_0)).

tff(f_199,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT001+2.ax',t4_xboole_0)).

tff(f_120,axiom,(
    ! [A,B] :
      ( r2_xboole_0(A,B)
    <=> ( r1_tarski(A,B)
        & A != B ) ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT001+2.ax',d8_xboole_0)).

tff(c_112,plain,(
    v1_xboole_0('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_417,plain,(
    ! [A_270] :
      ( k1_xboole_0 = A_270
      | ~ v1_xboole_0(A_270) ) ),
    inference(cnfTransformation,[status(thm)],[f_490])).

tff(c_426,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(resolution,[status(thm)],[c_112,c_417])).

tff(c_342,plain,(
    k1_xboole_0 != '#skF_21' ),
    inference(cnfTransformation,[status(thm)],[f_486])).

tff(c_435,plain,(
    '#skF_21' != '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_426,c_342])).

tff(c_22,plain,(
    ! [A_15,B_16] :
      ( r2_hidden('#skF_2'(A_15,B_16),A_15)
      | r1_tarski(A_15,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_106,plain,(
    ! [A_46] : k3_xboole_0(A_46,A_46) = A_46 ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_82,plain,(
    ! [A_40,B_41] :
      ( r1_xboole_0(A_40,B_41)
      | k3_xboole_0(A_40,B_41) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_1673,plain,(
    ! [A_40,B_41] :
      ( r1_xboole_0(A_40,B_41)
      | k3_xboole_0(A_40,B_41) != '#skF_9' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_426,c_82])).

tff(c_3368,plain,(
    ! [A_434,B_435,C_436] :
      ( ~ r1_xboole_0(A_434,B_435)
      | ~ r2_hidden(C_436,k3_xboole_0(A_434,B_435)) ) ),
    inference(cnfTransformation,[status(thm)],[f_199])).

tff(c_3410,plain,(
    ! [A_437,C_438] :
      ( ~ r1_xboole_0(A_437,A_437)
      | ~ r2_hidden(C_438,A_437) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_106,c_3368])).

tff(c_3419,plain,(
    ! [C_438,B_41] :
      ( ~ r2_hidden(C_438,B_41)
      | k3_xboole_0(B_41,B_41) != '#skF_9' ) ),
    inference(resolution,[status(thm)],[c_1673,c_3410])).

tff(c_3425,plain,(
    ! [C_439,B_440] :
      ( ~ r2_hidden(C_439,B_440)
      | B_440 != '#skF_9' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_3419])).

tff(c_3479,plain,(
    ! [B_16] : r1_tarski('#skF_9',B_16) ),
    inference(resolution,[status(thm)],[c_22,c_3425])).

tff(c_6057,plain,(
    ! [A_522,B_523] :
      ( r2_xboole_0(A_522,B_523)
      | B_523 = A_522
      | ~ r1_tarski(A_522,B_523) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_340,plain,(
    ~ r2_xboole_0(k1_xboole_0,'#skF_21') ),
    inference(cnfTransformation,[status(thm)],[f_486])).

tff(c_432,plain,(
    ~ r2_xboole_0('#skF_9','#skF_21') ),
    inference(demodulation,[status(thm),theory(equality)],[c_426,c_340])).

tff(c_6068,plain,
    ( '#skF_21' = '#skF_9'
    | ~ r1_tarski('#skF_9','#skF_21') ),
    inference(resolution,[status(thm)],[c_6057,c_432])).

tff(c_6078,plain,(
    '#skF_21' = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3479,c_6068])).

tff(c_6080,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_435,c_6078])).
%------------------------------------------------------------------------------

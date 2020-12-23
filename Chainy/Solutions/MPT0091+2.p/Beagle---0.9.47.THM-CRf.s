%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0091+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:07:14 EST 2020

% Result     : Theorem 10.57s
% Output     : CNFRefutation 10.57s
% Verified   : 
% Statistics : Number of formulae       :   64 (  72 expanded)
%              Number of leaves         :   44 (  49 expanded)
%              Depth                    :    6
%              Number of atoms          :   40 (  55 expanded)
%              Number of equality atoms :   16 (  20 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    2 (   1 average)

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

tff(f_63,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT001+2.ax',commutativity_k3_xboole_0)).

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

tff(f_646,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( ~ r1_xboole_0(A,B)
          & r1_xboole_0(A,C)
          & r1_xboole_0(A,k4_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t84_xboole_1)).

tff(f_637,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_631,axiom,(
    ! [A,B,C] :
      ( r1_xboole_0(A,k4_xboole_0(B,C))
     => r1_xboole_0(B,k4_xboole_0(A,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_xboole_1)).

tff(c_8,plain,(
    ! [B_8,A_7] : k3_xboole_0(B_8,A_7) = k3_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_112,plain,(
    v1_xboole_0('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_493,plain,(
    ! [A_331] :
      ( k1_xboole_0 = A_331
      | ~ v1_xboole_0(A_331) ) ),
    inference(cnfTransformation,[status(thm)],[f_546])).

tff(c_502,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(resolution,[status(thm)],[c_112,c_493])).

tff(c_82,plain,(
    ! [A_40,B_41] :
      ( r1_xboole_0(A_40,B_41)
      | k3_xboole_0(A_40,B_41) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_2331,plain,(
    ! [A_435,B_436] :
      ( r1_xboole_0(A_435,B_436)
      | k3_xboole_0(A_435,B_436) != '#skF_9' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_502,c_82])).

tff(c_406,plain,(
    ~ r1_xboole_0('#skF_21','#skF_22') ),
    inference(cnfTransformation,[status(thm)],[f_646])).

tff(c_2343,plain,(
    k3_xboole_0('#skF_21','#skF_22') != '#skF_9' ),
    inference(resolution,[status(thm)],[c_2331,c_406])).

tff(c_2349,plain,(
    k3_xboole_0('#skF_22','#skF_21') != '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_2343])).

tff(c_404,plain,(
    r1_xboole_0('#skF_21','#skF_23') ),
    inference(cnfTransformation,[status(thm)],[f_646])).

tff(c_1686,plain,(
    ! [A_415,B_416] :
      ( k4_xboole_0(A_415,B_416) = A_415
      | ~ r1_xboole_0(A_415,B_416) ) ),
    inference(cnfTransformation,[status(thm)],[f_637])).

tff(c_1720,plain,(
    k4_xboole_0('#skF_21','#skF_23') = '#skF_21' ),
    inference(resolution,[status(thm)],[c_404,c_1686])).

tff(c_402,plain,(
    r1_xboole_0('#skF_21',k4_xboole_0('#skF_22','#skF_23')) ),
    inference(cnfTransformation,[status(thm)],[f_646])).

tff(c_20679,plain,(
    ! [B_821,A_822,C_823] :
      ( r1_xboole_0(B_821,k4_xboole_0(A_822,C_823))
      | ~ r1_xboole_0(A_822,k4_xboole_0(B_821,C_823)) ) ),
    inference(cnfTransformation,[status(thm)],[f_631])).

tff(c_20788,plain,(
    r1_xboole_0('#skF_22',k4_xboole_0('#skF_21','#skF_23')) ),
    inference(resolution,[status(thm)],[c_402,c_20679])).

tff(c_20836,plain,(
    r1_xboole_0('#skF_22','#skF_21') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1720,c_20788])).

tff(c_80,plain,(
    ! [A_40,B_41] :
      ( k3_xboole_0(A_40,B_41) = k1_xboole_0
      | ~ r1_xboole_0(A_40,B_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_2573,plain,(
    ! [A_40,B_41] :
      ( k3_xboole_0(A_40,B_41) = '#skF_9'
      | ~ r1_xboole_0(A_40,B_41) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_502,c_80])).

tff(c_20846,plain,(
    k3_xboole_0('#skF_22','#skF_21') = '#skF_9' ),
    inference(resolution,[status(thm)],[c_20836,c_2573])).

tff(c_20860,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2349,c_20846])).
%------------------------------------------------------------------------------

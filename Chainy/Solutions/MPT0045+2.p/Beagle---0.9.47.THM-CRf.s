%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0045+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:07:11 EST 2020

% Result     : Theorem 5.50s
% Output     : CNFRefutation 5.50s
% Verified   : 
% Statistics : Number of formulae       :   59 (  65 expanded)
%              Number of leaves         :   43 (  46 expanded)
%              Depth                    :    6
%              Number of atoms          :   40 (  49 expanded)
%              Number of equality atoms :   15 (  19 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

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
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT001+2.ax',rc1_xboole_0)).

tff(f_409,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_boole)).

tff(f_393,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_tarski(A,k4_xboole_0(B,A))
       => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_xboole_1)).

tff(f_234,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT001+2.ax',t7_xboole_0)).

tff(f_352,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_97,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT001+2.ax',d4_xboole_0)).

tff(f_107,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT001+2.ax',d5_xboole_0)).

tff(c_112,plain,(
    v1_xboole_0('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_381,plain,(
    ! [A_207] :
      ( k1_xboole_0 = A_207
      | ~ v1_xboole_0(A_207) ) ),
    inference(cnfTransformation,[status(thm)],[f_409])).

tff(c_390,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(resolution,[status(thm)],[c_112,c_381])).

tff(c_280,plain,(
    k1_xboole_0 != '#skF_21' ),
    inference(cnfTransformation,[status(thm)],[f_393])).

tff(c_418,plain,(
    '#skF_21' != '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_390,c_280])).

tff(c_190,plain,(
    ! [A_79] :
      ( r2_hidden('#skF_18'(A_79),A_79)
      | k1_xboole_0 = A_79 ) ),
    inference(cnfTransformation,[status(thm)],[f_234])).

tff(c_579,plain,(
    ! [A_79] :
      ( r2_hidden('#skF_18'(A_79),A_79)
      | A_79 = '#skF_9' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_390,c_190])).

tff(c_282,plain,(
    r1_tarski('#skF_21',k4_xboole_0('#skF_22','#skF_21')) ),
    inference(cnfTransformation,[status(thm)],[f_393])).

tff(c_1180,plain,(
    ! [A_265,B_266] :
      ( k3_xboole_0(A_265,B_266) = A_265
      | ~ r1_tarski(A_265,B_266) ) ),
    inference(cnfTransformation,[status(thm)],[f_352])).

tff(c_1218,plain,(
    k3_xboole_0('#skF_21',k4_xboole_0('#skF_22','#skF_21')) = '#skF_21' ),
    inference(resolution,[status(thm)],[c_282,c_1180])).

tff(c_4144,plain,(
    ! [D_356,B_357,A_358] :
      ( r2_hidden(D_356,B_357)
      | ~ r2_hidden(D_356,k3_xboole_0(A_358,B_357)) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_4193,plain,(
    ! [D_359] :
      ( r2_hidden(D_359,k4_xboole_0('#skF_22','#skF_21'))
      | ~ r2_hidden(D_359,'#skF_21') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1218,c_4144])).

tff(c_62,plain,(
    ! [D_37,B_33,A_32] :
      ( ~ r2_hidden(D_37,B_33)
      | ~ r2_hidden(D_37,k4_xboole_0(A_32,B_33)) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_4213,plain,(
    ! [D_360] : ~ r2_hidden(D_360,'#skF_21') ),
    inference(resolution,[status(thm)],[c_4193,c_62])).

tff(c_4225,plain,(
    '#skF_21' = '#skF_9' ),
    inference(resolution,[status(thm)],[c_579,c_4213])).

tff(c_4231,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_418,c_4225])).
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0074+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:07:12 EST 2020

% Result     : Theorem 8.98s
% Output     : CNFRefutation 8.98s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 146 expanded)
%              Number of leaves         :   49 (  73 expanded)
%              Depth                    :    9
%              Number of atoms          :   83 ( 192 expanded)
%              Number of equality atoms :   29 (  64 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   1 average)

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
    file('/export/starexec/sandbox/benchmark/Axioms/MPT001+2.ax',rc1_xboole_0)).

tff(f_529,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_boole)).

tff(f_525,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( r1_tarski(A,B)
          & r1_tarski(A,C)
          & r1_xboole_0(B,C) )
       => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_xboole_1)).

tff(f_71,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT001+2.ax',d1_xboole_0)).

tff(f_402,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_426,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => B = k2_xboole_0(A,k4_xboole_0(B,A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_xboole_1)).

tff(f_88,axiom,(
    ! [A,B,C] :
      ( C = k2_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            | r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT001+2.ax',d3_xboole_0)).

tff(f_404,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_143,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT001+2.ax',symmetry_r1_xboole_0)).

tff(f_113,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT001+2.ax',d7_xboole_0)).

tff(f_430,axiom,(
    ! [A,B] : k4_xboole_0(A,k3_xboole_0(A,B)) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

tff(f_107,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT001+2.ax',d5_xboole_0)).

tff(c_112,plain,(
    v1_xboole_0('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_448,plain,(
    ! [A_283] :
      ( k1_xboole_0 = A_283
      | ~ v1_xboole_0(A_283) ) ),
    inference(cnfTransformation,[status(thm)],[f_529])).

tff(c_457,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(resolution,[status(thm)],[c_112,c_448])).

tff(c_354,plain,(
    k1_xboole_0 != '#skF_21' ),
    inference(cnfTransformation,[status(thm)],[f_525])).

tff(c_466,plain,(
    '#skF_21' != '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_457,c_354])).

tff(c_14,plain,(
    ! [A_11] :
      ( v1_xboole_0(A_11)
      | r2_hidden('#skF_1'(A_11),A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_360,plain,(
    r1_tarski('#skF_21','#skF_22') ),
    inference(cnfTransformation,[status(thm)],[f_525])).

tff(c_286,plain,(
    ! [A_183,B_184] : k2_xboole_0(A_183,k4_xboole_0(B_184,A_183)) = k2_xboole_0(A_183,B_184) ),
    inference(cnfTransformation,[status(thm)],[f_402])).

tff(c_302,plain,(
    ! [A_201,B_202] :
      ( k2_xboole_0(A_201,k4_xboole_0(B_202,A_201)) = B_202
      | ~ r1_tarski(A_201,B_202) ) ),
    inference(cnfTransformation,[status(thm)],[f_426])).

tff(c_1714,plain,(
    ! [A_363,B_364] :
      ( k2_xboole_0(A_363,B_364) = B_364
      | ~ r1_tarski(A_363,B_364) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_286,c_302])).

tff(c_1760,plain,(
    k2_xboole_0('#skF_21','#skF_22') = '#skF_22' ),
    inference(resolution,[status(thm)],[c_360,c_1714])).

tff(c_2273,plain,(
    ! [D_372,A_373,B_374] :
      ( ~ r2_hidden(D_372,A_373)
      | r2_hidden(D_372,k2_xboole_0(A_373,B_374)) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_2399,plain,(
    ! [D_377] :
      ( ~ r2_hidden(D_377,'#skF_21')
      | r2_hidden(D_377,'#skF_22') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1760,c_2273])).

tff(c_2411,plain,
    ( r2_hidden('#skF_1'('#skF_21'),'#skF_22')
    | v1_xboole_0('#skF_21') ),
    inference(resolution,[status(thm)],[c_14,c_2399])).

tff(c_2955,plain,(
    v1_xboole_0('#skF_21') ),
    inference(splitLeft,[status(thm)],[c_2411])).

tff(c_362,plain,(
    ! [A_259] :
      ( k1_xboole_0 = A_259
      | ~ v1_xboole_0(A_259) ) ),
    inference(cnfTransformation,[status(thm)],[f_529])).

tff(c_458,plain,(
    ! [A_259] :
      ( A_259 = '#skF_9'
      | ~ v1_xboole_0(A_259) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_457,c_362])).

tff(c_2960,plain,(
    '#skF_21' = '#skF_9' ),
    inference(resolution,[status(thm)],[c_2955,c_458])).

tff(c_2965,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_466,c_2960])).

tff(c_2967,plain,(
    ~ v1_xboole_0('#skF_21') ),
    inference(splitRight,[status(thm)],[c_2411])).

tff(c_358,plain,(
    r1_tarski('#skF_21','#skF_23') ),
    inference(cnfTransformation,[status(thm)],[f_525])).

tff(c_1759,plain,(
    k2_xboole_0('#skF_21','#skF_23') = '#skF_23' ),
    inference(resolution,[status(thm)],[c_358,c_1714])).

tff(c_2608,plain,(
    ! [D_384] :
      ( ~ r2_hidden(D_384,'#skF_21')
      | r2_hidden(D_384,'#skF_23') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1759,c_2273])).

tff(c_2620,plain,
    ( r2_hidden('#skF_1'('#skF_21'),'#skF_23')
    | v1_xboole_0('#skF_21') ),
    inference(resolution,[status(thm)],[c_14,c_2608])).

tff(c_4274,plain,(
    r2_hidden('#skF_1'('#skF_21'),'#skF_23') ),
    inference(negUnitSimplification,[status(thm)],[c_2967,c_2620])).

tff(c_2966,plain,(
    r2_hidden('#skF_1'('#skF_21'),'#skF_22') ),
    inference(splitRight,[status(thm)],[c_2411])).

tff(c_288,plain,(
    ! [A_185] : k4_xboole_0(A_185,k1_xboole_0) = A_185 ),
    inference(cnfTransformation,[status(thm)],[f_404])).

tff(c_479,plain,(
    ! [A_185] : k4_xboole_0(A_185,'#skF_9') = A_185 ),
    inference(demodulation,[status(thm),theory(equality)],[c_457,c_288])).

tff(c_356,plain,(
    r1_xboole_0('#skF_22','#skF_23') ),
    inference(cnfTransformation,[status(thm)],[f_525])).

tff(c_808,plain,(
    ! [B_320,A_321] :
      ( r1_xboole_0(B_320,A_321)
      | ~ r1_xboole_0(A_321,B_320) ) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_814,plain,(
    r1_xboole_0('#skF_23','#skF_22') ),
    inference(resolution,[status(thm)],[c_356,c_808])).

tff(c_80,plain,(
    ! [A_40,B_41] :
      ( k3_xboole_0(A_40,B_41) = k1_xboole_0
      | ~ r1_xboole_0(A_40,B_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_1175,plain,(
    ! [A_341,B_342] :
      ( k3_xboole_0(A_341,B_342) = '#skF_9'
      | ~ r1_xboole_0(A_341,B_342) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_457,c_80])).

tff(c_1190,plain,(
    k3_xboole_0('#skF_23','#skF_22') = '#skF_9' ),
    inference(resolution,[status(thm)],[c_814,c_1175])).

tff(c_6347,plain,(
    ! [A_478,B_479] : k4_xboole_0(A_478,k3_xboole_0(A_478,B_479)) = k4_xboole_0(A_478,B_479) ),
    inference(cnfTransformation,[status(thm)],[f_430])).

tff(c_6411,plain,(
    k4_xboole_0('#skF_23','#skF_9') = k4_xboole_0('#skF_23','#skF_22') ),
    inference(superposition,[status(thm),theory(equality)],[c_1190,c_6347])).

tff(c_6440,plain,(
    k4_xboole_0('#skF_23','#skF_22') = '#skF_23' ),
    inference(demodulation,[status(thm),theory(equality)],[c_479,c_6411])).

tff(c_11986,plain,(
    ! [D_565,B_566,A_567] :
      ( ~ r2_hidden(D_565,B_566)
      | ~ r2_hidden(D_565,k4_xboole_0(A_567,B_566)) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_12095,plain,(
    ! [D_568] :
      ( ~ r2_hidden(D_568,'#skF_22')
      | ~ r2_hidden(D_568,'#skF_23') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6440,c_11986])).

tff(c_12113,plain,(
    ~ r2_hidden('#skF_1'('#skF_21'),'#skF_23') ),
    inference(resolution,[status(thm)],[c_2966,c_12095])).

tff(c_12136,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4274,c_12113])).
%------------------------------------------------------------------------------

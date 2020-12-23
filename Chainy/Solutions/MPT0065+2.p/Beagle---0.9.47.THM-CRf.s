%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0065+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:07:12 EST 2020

% Result     : Theorem 8.81s
% Output     : CNFRefutation 8.81s
% Verified   : 
% Statistics : Number of formulae       :   98 ( 200 expanded)
%              Number of leaves         :   51 (  91 expanded)
%              Depth                    :   10
%              Number of atoms          :   85 ( 259 expanded)
%              Number of equality atoms :   41 ( 101 expanded)
%              Maximal formula depth    :    7 (   3 average)
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

tff(f_130,axiom,(
    ! [A,B] : ~ r2_xboole_0(A,A) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT001+2.ax',irreflexivity_r2_xboole_0)).

tff(f_468,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( r2_xboole_0(A,B)
          & r1_tarski(B,C) )
       => r2_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t58_xboole_1)).

tff(f_402,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_426,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => B = k2_xboole_0(A,k4_xboole_0(B,A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_xboole_1)).

tff(f_136,axiom,(
    ? [A] : v1_xboole_0(A) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT001+2.ax',rc1_xboole_0)).

tff(f_474,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_boole)).

tff(f_428,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).

tff(f_317,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_120,axiom,(
    ! [A,B] :
      ( r2_xboole_0(A,B)
    <=> ( r1_tarski(A,B)
        & A != B ) ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT001+2.ax',d8_xboole_0)).

tff(f_360,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_63,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT001+2.ax',commutativity_k3_xboole_0)).

tff(f_362,axiom,(
    ! [A,B,C] : r1_tarski(k3_xboole_0(A,B),k2_xboole_0(A,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_xboole_1)).

tff(f_396,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_xboole_1)).

tff(f_242,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(c_108,plain,(
    ! [A_48] : ~ r2_xboole_0(A_48,A_48) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_334,plain,(
    r1_tarski('#skF_22','#skF_23') ),
    inference(cnfTransformation,[status(thm)],[f_468])).

tff(c_286,plain,(
    ! [A_183,B_184] : k2_xboole_0(A_183,k4_xboole_0(B_184,A_183)) = k2_xboole_0(A_183,B_184) ),
    inference(cnfTransformation,[status(thm)],[f_402])).

tff(c_302,plain,(
    ! [A_201,B_202] :
      ( k2_xboole_0(A_201,k4_xboole_0(B_202,A_201)) = B_202
      | ~ r1_tarski(A_201,B_202) ) ),
    inference(cnfTransformation,[status(thm)],[f_426])).

tff(c_1575,plain,(
    ! [A_329,B_330] :
      ( k2_xboole_0(A_329,B_330) = B_330
      | ~ r1_tarski(A_329,B_330) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_286,c_302])).

tff(c_1617,plain,(
    k2_xboole_0('#skF_22','#skF_23') = '#skF_23' ),
    inference(resolution,[status(thm)],[c_334,c_1575])).

tff(c_112,plain,(
    v1_xboole_0('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_449,plain,(
    ! [A_264] :
      ( k1_xboole_0 = A_264
      | ~ v1_xboole_0(A_264) ) ),
    inference(cnfTransformation,[status(thm)],[f_474])).

tff(c_458,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(resolution,[status(thm)],[c_112,c_449])).

tff(c_304,plain,(
    ! [A_203,B_204] : k4_xboole_0(A_203,k2_xboole_0(A_203,B_204)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_428])).

tff(c_678,plain,(
    ! [A_203,B_204] : k4_xboole_0(A_203,k2_xboole_0(A_203,B_204)) = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_458,c_304])).

tff(c_1639,plain,(
    k4_xboole_0('#skF_22','#skF_23') = '#skF_9' ),
    inference(superposition,[status(thm),theory(equality)],[c_1617,c_678])).

tff(c_234,plain,(
    ! [A_124] : k2_xboole_0(A_124,k1_xboole_0) = A_124 ),
    inference(cnfTransformation,[status(thm)],[f_317])).

tff(c_461,plain,(
    ! [A_124] : k2_xboole_0(A_124,'#skF_9') = A_124 ),
    inference(demodulation,[status(thm),theory(equality)],[c_458,c_234])).

tff(c_679,plain,(
    ! [A_297,B_298] : k4_xboole_0(A_297,k2_xboole_0(A_297,B_298)) = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_458,c_304])).

tff(c_695,plain,(
    ! [A_124] : k4_xboole_0(A_124,A_124) = '#skF_9' ),
    inference(superposition,[status(thm),theory(equality)],[c_461,c_679])).

tff(c_336,plain,(
    r2_xboole_0('#skF_21','#skF_22') ),
    inference(cnfTransformation,[status(thm)],[f_468])).

tff(c_672,plain,(
    ! [A_293,B_294] :
      ( r1_tarski(A_293,B_294)
      | ~ r2_xboole_0(A_293,B_294) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_676,plain,(
    r1_tarski('#skF_21','#skF_22') ),
    inference(resolution,[status(thm)],[c_336,c_672])).

tff(c_1387,plain,(
    ! [A_327,B_328] :
      ( k3_xboole_0(A_327,B_328) = A_327
      | ~ r1_tarski(A_327,B_328) ) ),
    inference(cnfTransformation,[status(thm)],[f_360])).

tff(c_1422,plain,(
    k3_xboole_0('#skF_21','#skF_22') = '#skF_21' ),
    inference(resolution,[status(thm)],[c_676,c_1387])).

tff(c_8,plain,(
    ! [B_8,A_7] : k3_xboole_0(B_8,A_7) = k3_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_1488,plain,(
    k3_xboole_0('#skF_22','#skF_21') = '#skF_21' ),
    inference(superposition,[status(thm),theory(equality)],[c_1422,c_8])).

tff(c_260,plain,(
    ! [A_154,B_155,C_156] : r1_tarski(k3_xboole_0(A_154,B_155),k2_xboole_0(A_154,C_156)) ),
    inference(cnfTransformation,[status(thm)],[f_362])).

tff(c_1797,plain,(
    ! [B_333] : r1_tarski(k3_xboole_0('#skF_22',B_333),'#skF_23') ),
    inference(superposition,[status(thm),theory(equality)],[c_1617,c_260])).

tff(c_1805,plain,(
    r1_tarski('#skF_21','#skF_23') ),
    inference(superposition,[status(thm),theory(equality)],[c_1488,c_1797])).

tff(c_12905,plain,(
    ! [A_568,B_569] :
      ( r2_xboole_0(A_568,B_569)
      | B_569 = A_568
      | ~ r1_tarski(A_568,B_569) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_332,plain,(
    ~ r2_xboole_0('#skF_21','#skF_23') ),
    inference(cnfTransformation,[status(thm)],[f_468])).

tff(c_12919,plain,
    ( '#skF_21' = '#skF_23'
    | ~ r1_tarski('#skF_21','#skF_23') ),
    inference(resolution,[status(thm)],[c_12905,c_332])).

tff(c_12930,plain,(
    '#skF_21' = '#skF_23' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1805,c_12919])).

tff(c_280,plain,(
    ! [A_179,B_180] :
      ( r1_tarski(A_179,B_180)
      | k4_xboole_0(A_179,B_180) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_396])).

tff(c_1992,plain,(
    ! [A_179,B_180] :
      ( r1_tarski(A_179,B_180)
      | k4_xboole_0(A_179,B_180) != '#skF_9' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_458,c_280])).

tff(c_2674,plain,(
    ! [B_353,A_354] :
      ( B_353 = A_354
      | ~ r1_tarski(B_353,A_354)
      | ~ r1_tarski(A_354,B_353) ) ),
    inference(cnfTransformation,[status(thm)],[f_242])).

tff(c_2732,plain,
    ( '#skF_21' = '#skF_23'
    | ~ r1_tarski('#skF_23','#skF_21') ),
    inference(resolution,[status(thm)],[c_1805,c_2674])).

tff(c_2757,plain,(
    ~ r1_tarski('#skF_23','#skF_21') ),
    inference(splitLeft,[status(thm)],[c_2732])).

tff(c_2761,plain,(
    k4_xboole_0('#skF_23','#skF_21') != '#skF_9' ),
    inference(resolution,[status(thm)],[c_1992,c_2757])).

tff(c_12955,plain,(
    k4_xboole_0('#skF_23','#skF_23') != '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12930,c_2761])).

tff(c_12985,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_695,c_12955])).

tff(c_12986,plain,(
    '#skF_21' = '#skF_23' ),
    inference(splitRight,[status(thm)],[c_2732])).

tff(c_2737,plain,
    ( '#skF_21' = '#skF_22'
    | ~ r1_tarski('#skF_22','#skF_21') ),
    inference(resolution,[status(thm)],[c_676,c_2674])).

tff(c_2752,plain,(
    ~ r1_tarski('#skF_22','#skF_21') ),
    inference(splitLeft,[status(thm)],[c_2737])).

tff(c_2756,plain,(
    k4_xboole_0('#skF_22','#skF_21') != '#skF_9' ),
    inference(resolution,[status(thm)],[c_1992,c_2752])).

tff(c_12988,plain,(
    k4_xboole_0('#skF_22','#skF_23') != '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12986,c_2756])).

tff(c_13014,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1639,c_12988])).

tff(c_13015,plain,(
    '#skF_21' = '#skF_22' ),
    inference(splitRight,[status(thm)],[c_2737])).

tff(c_13038,plain,(
    r2_xboole_0('#skF_22','#skF_22') ),
    inference(demodulation,[status(thm),theory(equality)],[c_13015,c_336])).

tff(c_13059,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_108,c_13038])).
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0066+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:07:12 EST 2020

% Result     : Theorem 5.77s
% Output     : CNFRefutation 5.77s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 209 expanded)
%              Number of leaves         :   50 (  94 expanded)
%              Depth                    :   11
%              Number of atoms          :   81 ( 268 expanded)
%              Number of equality atoms :   41 ( 114 expanded)
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

tff(f_474,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( r1_tarski(A,B)
          & r2_xboole_0(B,C) )
       => r2_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_xboole_1)).

tff(f_120,axiom,(
    ! [A,B] :
      ( r2_xboole_0(A,B)
    <=> ( r1_tarski(A,B)
        & A != B ) ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT001+2.ax',d8_xboole_0)).

tff(f_402,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_426,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => B = k2_xboole_0(A,k4_xboole_0(B,A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_xboole_1)).

tff(f_136,axiom,(
    ? [A] : v1_xboole_0(A) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT001+2.ax',rc1_xboole_0)).

tff(f_480,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_boole)).

tff(f_428,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

tff(f_340,axiom,(
    ! [A,B] : k2_xboole_0(A,k3_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_xboole_1)).

tff(f_63,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT001+2.ax',commutativity_k3_xboole_0)).

tff(f_338,axiom,(
    ! [A,B] : k3_xboole_0(A,k2_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_xboole_1)).

tff(f_362,axiom,(
    ! [A,B,C] : r1_tarski(k3_xboole_0(A,B),k2_xboole_0(A,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_xboole_1)).

tff(f_396,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_xboole_1)).

tff(f_242,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(c_336,plain,(
    r2_xboole_0('#skF_22','#skF_23') ),
    inference(cnfTransformation,[status(thm)],[f_474])).

tff(c_1149,plain,(
    ! [A_316,B_317] :
      ( r1_tarski(A_316,B_317)
      | ~ r2_xboole_0(A_316,B_317) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_1153,plain,(
    r1_tarski('#skF_22','#skF_23') ),
    inference(resolution,[status(thm)],[c_336,c_1149])).

tff(c_286,plain,(
    ! [A_183,B_184] : k2_xboole_0(A_183,k4_xboole_0(B_184,A_183)) = k2_xboole_0(A_183,B_184) ),
    inference(cnfTransformation,[status(thm)],[f_402])).

tff(c_302,plain,(
    ! [A_201,B_202] :
      ( k2_xboole_0(A_201,k4_xboole_0(B_202,A_201)) = B_202
      | ~ r1_tarski(A_201,B_202) ) ),
    inference(cnfTransformation,[status(thm)],[f_426])).

tff(c_1336,plain,(
    ! [A_327,B_328] :
      ( k2_xboole_0(A_327,B_328) = B_328
      | ~ r1_tarski(A_327,B_328) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_286,c_302])).

tff(c_1364,plain,(
    k2_xboole_0('#skF_22','#skF_23') = '#skF_23' ),
    inference(resolution,[status(thm)],[c_1153,c_1336])).

tff(c_112,plain,(
    v1_xboole_0('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_451,plain,(
    ! [A_267] :
      ( k1_xboole_0 = A_267
      | ~ v1_xboole_0(A_267) ) ),
    inference(cnfTransformation,[status(thm)],[f_480])).

tff(c_460,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(resolution,[status(thm)],[c_112,c_451])).

tff(c_304,plain,(
    ! [A_203,B_204] : k4_xboole_0(A_203,k2_xboole_0(A_203,B_204)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_428])).

tff(c_734,plain,(
    ! [A_203,B_204] : k4_xboole_0(A_203,k2_xboole_0(A_203,B_204)) = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_460,c_304])).

tff(c_1433,plain,(
    k4_xboole_0('#skF_22','#skF_23') = '#skF_9' ),
    inference(superposition,[status(thm),theory(equality)],[c_1364,c_734])).

tff(c_246,plain,(
    ! [A_134,B_135] : k2_xboole_0(A_134,k3_xboole_0(A_134,B_135)) = A_134 ),
    inference(cnfTransformation,[status(thm)],[f_340])).

tff(c_735,plain,(
    ! [A_297,B_298] : k4_xboole_0(A_297,k2_xboole_0(A_297,B_298)) = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_460,c_304])).

tff(c_748,plain,(
    ! [A_134] : k4_xboole_0(A_134,A_134) = '#skF_9' ),
    inference(superposition,[status(thm),theory(equality)],[c_246,c_735])).

tff(c_8,plain,(
    ! [B_8,A_7] : k3_xboole_0(B_8,A_7) = k3_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_338,plain,(
    r1_tarski('#skF_21','#skF_22') ),
    inference(cnfTransformation,[status(thm)],[f_474])).

tff(c_1372,plain,(
    k2_xboole_0('#skF_21','#skF_22') = '#skF_22' ),
    inference(resolution,[status(thm)],[c_338,c_1336])).

tff(c_244,plain,(
    ! [A_132,B_133] : k3_xboole_0(A_132,k2_xboole_0(A_132,B_133)) = A_132 ),
    inference(cnfTransformation,[status(thm)],[f_338])).

tff(c_1396,plain,(
    k3_xboole_0('#skF_21','#skF_22') = '#skF_21' ),
    inference(superposition,[status(thm),theory(equality)],[c_1372,c_244])).

tff(c_1546,plain,(
    k3_xboole_0('#skF_22','#skF_21') = '#skF_21' ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_1396])).

tff(c_2531,plain,(
    ! [A_360,B_361,C_362] : r1_tarski(k3_xboole_0(A_360,B_361),k2_xboole_0(A_360,C_362)) ),
    inference(cnfTransformation,[status(thm)],[f_362])).

tff(c_2677,plain,(
    ! [B_364] : r1_tarski(k3_xboole_0('#skF_22',B_364),'#skF_23') ),
    inference(superposition,[status(thm),theory(equality)],[c_1364,c_2531])).

tff(c_2690,plain,(
    r1_tarski('#skF_21','#skF_23') ),
    inference(superposition,[status(thm),theory(equality)],[c_1546,c_2677])).

tff(c_3841,plain,(
    ! [A_384,B_385] :
      ( r2_xboole_0(A_384,B_385)
      | B_385 = A_384
      | ~ r1_tarski(A_384,B_385) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_334,plain,(
    ~ r2_xboole_0('#skF_21','#skF_23') ),
    inference(cnfTransformation,[status(thm)],[f_474])).

tff(c_3852,plain,
    ( '#skF_21' = '#skF_23'
    | ~ r1_tarski('#skF_21','#skF_23') ),
    inference(resolution,[status(thm)],[c_3841,c_334])).

tff(c_3862,plain,(
    '#skF_21' = '#skF_23' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2690,c_3852])).

tff(c_280,plain,(
    ! [A_179,B_180] :
      ( r1_tarski(A_179,B_180)
      | k4_xboole_0(A_179,B_180) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_396])).

tff(c_1498,plain,(
    ! [A_179,B_180] :
      ( r1_tarski(A_179,B_180)
      | k4_xboole_0(A_179,B_180) != '#skF_9' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_460,c_280])).

tff(c_3366,plain,(
    ! [B_373,A_374] :
      ( B_373 = A_374
      | ~ r1_tarski(B_373,A_374)
      | ~ r1_tarski(A_374,B_373) ) ),
    inference(cnfTransformation,[status(thm)],[f_242])).

tff(c_3407,plain,
    ( '#skF_21' = '#skF_23'
    | ~ r1_tarski('#skF_23','#skF_21') ),
    inference(resolution,[status(thm)],[c_2690,c_3366])).

tff(c_3442,plain,(
    ~ r1_tarski('#skF_23','#skF_21') ),
    inference(splitLeft,[status(thm)],[c_3407])).

tff(c_3446,plain,(
    k4_xboole_0('#skF_23','#skF_21') != '#skF_9' ),
    inference(resolution,[status(thm)],[c_1498,c_3442])).

tff(c_3872,plain,(
    k4_xboole_0('#skF_23','#skF_23') != '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3862,c_3446])).

tff(c_3897,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_748,c_3872])).

tff(c_3898,plain,(
    '#skF_21' = '#skF_23' ),
    inference(splitRight,[status(thm)],[c_3407])).

tff(c_3419,plain,
    ( '#skF_21' = '#skF_22'
    | ~ r1_tarski('#skF_22','#skF_21') ),
    inference(resolution,[status(thm)],[c_338,c_3366])).

tff(c_3424,plain,(
    ~ r1_tarski('#skF_22','#skF_21') ),
    inference(splitLeft,[status(thm)],[c_3419])).

tff(c_3428,plain,(
    k4_xboole_0('#skF_22','#skF_21') != '#skF_9' ),
    inference(resolution,[status(thm)],[c_1498,c_3424])).

tff(c_3900,plain,(
    k4_xboole_0('#skF_22','#skF_23') != '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3898,c_3428])).

tff(c_3920,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1433,c_3900])).

tff(c_3921,plain,(
    '#skF_21' = '#skF_22' ),
    inference(splitRight,[status(thm)],[c_3419])).

tff(c_3937,plain,(
    ~ r2_xboole_0('#skF_22','#skF_23') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3921,c_334])).

tff(c_3955,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_336,c_3937])).
%------------------------------------------------------------------------------

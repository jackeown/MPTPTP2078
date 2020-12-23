%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0063+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:07:12 EST 2020

% Result     : Theorem 7.90s
% Output     : CNFRefutation 8.29s
% Verified   : 
% Statistics : Number of formulae       :  103 ( 231 expanded)
%              Number of leaves         :   51 ( 101 expanded)
%              Depth                    :   10
%              Number of atoms          :   95 ( 320 expanded)
%              Number of equality atoms :   48 ( 120 expanded)
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

tff(f_457,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( r2_xboole_0(A,B)
          & r2_xboole_0(B,C) )
       => r2_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_xboole_1)).

tff(f_340,axiom,(
    ! [A,B] : k2_xboole_0(A,k3_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_xboole_1)).

tff(f_136,axiom,(
    ? [A] : v1_xboole_0(A) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT001+2.ax',rc1_xboole_0)).

tff(f_463,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_boole)).

tff(f_428,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).

tff(f_120,axiom,(
    ! [A,B] :
      ( r2_xboole_0(A,B)
    <=> ( r1_tarski(A,B)
        & A != B ) ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT001+2.ax',d8_xboole_0)).

tff(f_63,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT001+2.ax',commutativity_k3_xboole_0)).

tff(f_360,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

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

tff(f_376,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k4_xboole_0(B,A)
     => A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_xboole_1)).

tff(c_330,plain,(
    r2_xboole_0('#skF_22','#skF_23') ),
    inference(cnfTransformation,[status(thm)],[f_457])).

tff(c_246,plain,(
    ! [A_134,B_135] : k2_xboole_0(A_134,k3_xboole_0(A_134,B_135)) = A_134 ),
    inference(cnfTransformation,[status(thm)],[f_340])).

tff(c_112,plain,(
    v1_xboole_0('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_407,plain,(
    ! [A_257] :
      ( k1_xboole_0 = A_257
      | ~ v1_xboole_0(A_257) ) ),
    inference(cnfTransformation,[status(thm)],[f_463])).

tff(c_416,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(resolution,[status(thm)],[c_112,c_407])).

tff(c_304,plain,(
    ! [A_203,B_204] : k4_xboole_0(A_203,k2_xboole_0(A_203,B_204)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_428])).

tff(c_1008,plain,(
    ! [A_304,B_305] : k4_xboole_0(A_304,k2_xboole_0(A_304,B_305)) = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_416,c_304])).

tff(c_1021,plain,(
    ! [A_134] : k4_xboole_0(A_134,A_134) = '#skF_9' ),
    inference(superposition,[status(thm),theory(equality)],[c_246,c_1008])).

tff(c_675,plain,(
    ! [A_287,B_288] :
      ( r1_tarski(A_287,B_288)
      | ~ r2_xboole_0(A_287,B_288) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_683,plain,(
    r1_tarski('#skF_22','#skF_23') ),
    inference(resolution,[status(thm)],[c_330,c_675])).

tff(c_8,plain,(
    ! [B_8,A_7] : k3_xboole_0(B_8,A_7) = k3_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_332,plain,(
    r2_xboole_0('#skF_21','#skF_22') ),
    inference(cnfTransformation,[status(thm)],[f_457])).

tff(c_682,plain,(
    r1_tarski('#skF_21','#skF_22') ),
    inference(resolution,[status(thm)],[c_332,c_675])).

tff(c_1686,plain,(
    ! [A_331,B_332] :
      ( k3_xboole_0(A_331,B_332) = A_331
      | ~ r1_tarski(A_331,B_332) ) ),
    inference(cnfTransformation,[status(thm)],[f_360])).

tff(c_1719,plain,(
    k3_xboole_0('#skF_21','#skF_22') = '#skF_21' ),
    inference(resolution,[status(thm)],[c_682,c_1686])).

tff(c_1756,plain,(
    k3_xboole_0('#skF_22','#skF_21') = '#skF_21' ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_1719])).

tff(c_286,plain,(
    ! [A_183,B_184] : k2_xboole_0(A_183,k4_xboole_0(B_184,A_183)) = k2_xboole_0(A_183,B_184) ),
    inference(cnfTransformation,[status(thm)],[f_402])).

tff(c_302,plain,(
    ! [A_201,B_202] :
      ( k2_xboole_0(A_201,k4_xboole_0(B_202,A_201)) = B_202
      | ~ r1_tarski(A_201,B_202) ) ),
    inference(cnfTransformation,[status(thm)],[f_426])).

tff(c_1459,plain,(
    ! [A_329,B_330] :
      ( k2_xboole_0(A_329,B_330) = B_330
      | ~ r1_tarski(A_329,B_330) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_286,c_302])).

tff(c_1489,plain,(
    k2_xboole_0('#skF_22','#skF_23') = '#skF_23' ),
    inference(resolution,[status(thm)],[c_683,c_1459])).

tff(c_1940,plain,(
    ! [A_337,B_338,C_339] : r1_tarski(k3_xboole_0(A_337,B_338),k2_xboole_0(A_337,C_339)) ),
    inference(cnfTransformation,[status(thm)],[f_362])).

tff(c_2079,plain,(
    ! [B_341] : r1_tarski(k3_xboole_0('#skF_22',B_341),'#skF_23') ),
    inference(superposition,[status(thm),theory(equality)],[c_1489,c_1940])).

tff(c_2090,plain,(
    r1_tarski('#skF_21','#skF_23') ),
    inference(superposition,[status(thm),theory(equality)],[c_1756,c_2079])).

tff(c_9116,plain,(
    ! [A_507,B_508] :
      ( r2_xboole_0(A_507,B_508)
      | B_508 = A_507
      | ~ r1_tarski(A_507,B_508) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_328,plain,(
    ~ r2_xboole_0('#skF_21','#skF_23') ),
    inference(cnfTransformation,[status(thm)],[f_457])).

tff(c_9140,plain,
    ( '#skF_21' = '#skF_23'
    | ~ r1_tarski('#skF_21','#skF_23') ),
    inference(resolution,[status(thm)],[c_9116,c_328])).

tff(c_9154,plain,(
    '#skF_21' = '#skF_23' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2090,c_9140])).

tff(c_280,plain,(
    ! [A_179,B_180] :
      ( r1_tarski(A_179,B_180)
      | k4_xboole_0(A_179,B_180) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_396])).

tff(c_2192,plain,(
    ! [A_179,B_180] :
      ( r1_tarski(A_179,B_180)
      | k4_xboole_0(A_179,B_180) != '#skF_9' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_416,c_280])).

tff(c_8491,plain,(
    ! [B_492,A_493] :
      ( B_492 = A_493
      | ~ r1_tarski(B_492,A_493)
      | ~ r1_tarski(A_493,B_492) ) ),
    inference(cnfTransformation,[status(thm)],[f_242])).

tff(c_8567,plain,
    ( '#skF_21' = '#skF_23'
    | ~ r1_tarski('#skF_23','#skF_21') ),
    inference(resolution,[status(thm)],[c_2090,c_8491])).

tff(c_8608,plain,(
    ~ r1_tarski('#skF_23','#skF_21') ),
    inference(splitLeft,[status(thm)],[c_8567])).

tff(c_8620,plain,(
    k4_xboole_0('#skF_23','#skF_21') != '#skF_9' ),
    inference(resolution,[status(thm)],[c_2192,c_8608])).

tff(c_9161,plain,(
    k4_xboole_0('#skF_23','#skF_23') != '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9154,c_8620])).

tff(c_9210,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1021,c_9161])).

tff(c_9211,plain,(
    '#skF_21' = '#skF_23' ),
    inference(splitRight,[status(thm)],[c_8567])).

tff(c_8574,plain,
    ( '#skF_21' = '#skF_22'
    | ~ r1_tarski('#skF_22','#skF_21') ),
    inference(resolution,[status(thm)],[c_682,c_8491])).

tff(c_8595,plain,(
    ~ r1_tarski('#skF_22','#skF_21') ),
    inference(splitLeft,[status(thm)],[c_8574])).

tff(c_9213,plain,(
    ~ r1_tarski('#skF_22','#skF_23') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9211,c_8595])).

tff(c_9260,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_683,c_9213])).

tff(c_9261,plain,(
    '#skF_21' = '#skF_22' ),
    inference(splitRight,[status(thm)],[c_8574])).

tff(c_282,plain,(
    ! [A_179,B_180] :
      ( k4_xboole_0(A_179,B_180) = k1_xboole_0
      | ~ r1_tarski(A_179,B_180) ) ),
    inference(cnfTransformation,[status(thm)],[f_396])).

tff(c_1839,plain,(
    ! [A_333,B_334] :
      ( k4_xboole_0(A_333,B_334) = '#skF_9'
      | ~ r1_tarski(A_333,B_334) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_416,c_282])).

tff(c_1872,plain,(
    k4_xboole_0('#skF_21','#skF_22') = '#skF_9' ),
    inference(resolution,[status(thm)],[c_682,c_1839])).

tff(c_5080,plain,(
    ! [B_416,A_417] :
      ( B_416 = A_417
      | k4_xboole_0(B_416,A_417) != k4_xboole_0(A_417,B_416) ) ),
    inference(cnfTransformation,[status(thm)],[f_376])).

tff(c_5125,plain,
    ( '#skF_21' = '#skF_22'
    | k4_xboole_0('#skF_22','#skF_21') != '#skF_9' ),
    inference(superposition,[status(thm),theory(equality)],[c_1872,c_5080])).

tff(c_5158,plain,(
    k4_xboole_0('#skF_22','#skF_21') != '#skF_9' ),
    inference(splitLeft,[status(thm)],[c_5125])).

tff(c_9269,plain,(
    k4_xboole_0('#skF_22','#skF_22') != '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9261,c_5158])).

tff(c_9314,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1021,c_9269])).

tff(c_9315,plain,(
    '#skF_21' = '#skF_22' ),
    inference(splitRight,[status(thm)],[c_5125])).

tff(c_9353,plain,(
    ~ r2_xboole_0('#skF_22','#skF_23') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9315,c_328])).

tff(c_9380,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_330,c_9353])).
%------------------------------------------------------------------------------

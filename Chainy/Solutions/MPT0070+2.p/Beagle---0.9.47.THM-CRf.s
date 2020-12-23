%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0070+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:07:12 EST 2020

% Result     : Theorem 10.67s
% Output     : CNFRefutation 10.67s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 113 expanded)
%              Number of leaves         :   51 (  63 expanded)
%              Depth                    :    9
%              Number of atoms          :   72 ( 110 expanded)
%              Number of equality atoms :   44 (  59 expanded)
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

tff(f_63,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT001+2.ax',commutativity_k3_xboole_0)).

tff(f_136,axiom,(
    ? [A] : v1_xboole_0(A) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT001+2.ax',rc1_xboole_0)).

tff(f_499,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_boole)).

tff(f_113,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT001+2.ax',d7_xboole_0)).

tff(f_495,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( r1_tarski(A,B)
          & r1_xboole_0(B,C) )
       => r1_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_xboole_1)).

tff(f_360,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_404,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_392,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_402,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_426,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => B = k2_xboole_0(A,k4_xboole_0(B,A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_xboole_1)).

tff(f_301,axiom,(
    ! [A,B] :
      ( k2_xboole_0(A,B) = k1_xboole_0
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_xboole_1)).

tff(f_432,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_143,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT001+2.ax',symmetry_r1_xboole_0)).

tff(f_303,axiom,(
    ! [A,B,C] : k3_xboole_0(k3_xboole_0(A,B),C) = k3_xboole_0(A,k3_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_xboole_1)).

tff(c_8,plain,(
    ! [B_8,A_7] : k3_xboole_0(B_8,A_7) = k3_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_112,plain,(
    v1_xboole_0('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_417,plain,(
    ! [A_272] :
      ( k1_xboole_0 = A_272
      | ~ v1_xboole_0(A_272) ) ),
    inference(cnfTransformation,[status(thm)],[f_499])).

tff(c_426,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(resolution,[status(thm)],[c_112,c_417])).

tff(c_82,plain,(
    ! [A_40,B_41] :
      ( r1_xboole_0(A_40,B_41)
      | k3_xboole_0(A_40,B_41) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_1294,plain,(
    ! [A_334,B_335] :
      ( r1_xboole_0(A_334,B_335)
      | k3_xboole_0(A_334,B_335) != '#skF_9' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_426,c_82])).

tff(c_344,plain,(
    ~ r1_xboole_0('#skF_21','#skF_23') ),
    inference(cnfTransformation,[status(thm)],[f_495])).

tff(c_1299,plain,(
    k3_xboole_0('#skF_21','#skF_23') != '#skF_9' ),
    inference(resolution,[status(thm)],[c_1294,c_344])).

tff(c_1302,plain,(
    k3_xboole_0('#skF_23','#skF_21') != '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_1299])).

tff(c_348,plain,(
    r1_tarski('#skF_21','#skF_22') ),
    inference(cnfTransformation,[status(thm)],[f_495])).

tff(c_1158,plain,(
    ! [A_330,B_331] :
      ( k3_xboole_0(A_330,B_331) = A_330
      | ~ r1_tarski(A_330,B_331) ) ),
    inference(cnfTransformation,[status(thm)],[f_360])).

tff(c_1191,plain,(
    k3_xboole_0('#skF_21','#skF_22') = '#skF_21' ),
    inference(resolution,[status(thm)],[c_348,c_1158])).

tff(c_1200,plain,(
    k3_xboole_0('#skF_22','#skF_21') = '#skF_21' ),
    inference(superposition,[status(thm),theory(equality)],[c_1191,c_8])).

tff(c_288,plain,(
    ! [A_185] : k4_xboole_0(A_185,k1_xboole_0) = A_185 ),
    inference(cnfTransformation,[status(thm)],[f_404])).

tff(c_436,plain,(
    ! [A_185] : k4_xboole_0(A_185,'#skF_9') = A_185 ),
    inference(demodulation,[status(thm),theory(equality)],[c_426,c_288])).

tff(c_278,plain,(
    ! [A_177,B_178] : r1_tarski(k4_xboole_0(A_177,B_178),A_177) ),
    inference(cnfTransformation,[status(thm)],[f_392])).

tff(c_286,plain,(
    ! [A_183,B_184] : k2_xboole_0(A_183,k4_xboole_0(B_184,A_183)) = k2_xboole_0(A_183,B_184) ),
    inference(cnfTransformation,[status(thm)],[f_402])).

tff(c_302,plain,(
    ! [A_201,B_202] :
      ( k2_xboole_0(A_201,k4_xboole_0(B_202,A_201)) = B_202
      | ~ r1_tarski(A_201,B_202) ) ),
    inference(cnfTransformation,[status(thm)],[f_426])).

tff(c_2326,plain,(
    ! [A_370,B_371] :
      ( k2_xboole_0(A_370,B_371) = B_371
      | ~ r1_tarski(A_370,B_371) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_286,c_302])).

tff(c_2522,plain,(
    ! [A_374,B_375] : k2_xboole_0(k4_xboole_0(A_374,B_375),A_374) = A_374 ),
    inference(resolution,[status(thm)],[c_278,c_2326])).

tff(c_224,plain,(
    ! [A_111,B_112] :
      ( k1_xboole_0 = A_111
      | k2_xboole_0(A_111,B_112) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_301])).

tff(c_624,plain,(
    ! [A_111,B_112] :
      ( A_111 = '#skF_9'
      | k2_xboole_0(A_111,B_112) != '#skF_9' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_426,c_426,c_224])).

tff(c_2569,plain,(
    ! [A_374,B_375] :
      ( k4_xboole_0(A_374,B_375) = '#skF_9'
      | A_374 != '#skF_9' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2522,c_624])).

tff(c_5178,plain,(
    ! [A_430,B_431] : k4_xboole_0(A_430,k4_xboole_0(A_430,B_431)) = k3_xboole_0(A_430,B_431) ),
    inference(cnfTransformation,[status(thm)],[f_432])).

tff(c_5243,plain,(
    ! [A_374,B_375] :
      ( k4_xboole_0(A_374,'#skF_9') = k3_xboole_0(A_374,B_375)
      | A_374 != '#skF_9' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2569,c_5178])).

tff(c_5304,plain,(
    ! [B_375] : k3_xboole_0('#skF_9',B_375) = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_436,c_5243])).

tff(c_346,plain,(
    r1_xboole_0('#skF_22','#skF_23') ),
    inference(cnfTransformation,[status(thm)],[f_495])).

tff(c_1124,plain,(
    ! [B_326,A_327] :
      ( r1_xboole_0(B_326,A_327)
      | ~ r1_xboole_0(A_327,B_326) ) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_1127,plain,(
    r1_xboole_0('#skF_23','#skF_22') ),
    inference(resolution,[status(thm)],[c_346,c_1124])).

tff(c_80,plain,(
    ! [A_40,B_41] :
      ( k3_xboole_0(A_40,B_41) = k1_xboole_0
      | ~ r1_xboole_0(A_40,B_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_1969,plain,(
    ! [A_360,B_361] :
      ( k3_xboole_0(A_360,B_361) = '#skF_9'
      | ~ r1_xboole_0(A_360,B_361) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_426,c_80])).

tff(c_1980,plain,(
    k3_xboole_0('#skF_23','#skF_22') = '#skF_9' ),
    inference(resolution,[status(thm)],[c_1127,c_1969])).

tff(c_18055,plain,(
    ! [A_732,B_733,C_734] : k3_xboole_0(k3_xboole_0(A_732,B_733),C_734) = k3_xboole_0(A_732,k3_xboole_0(B_733,C_734)) ),
    inference(cnfTransformation,[status(thm)],[f_303])).

tff(c_18287,plain,(
    ! [C_734] : k3_xboole_0('#skF_23',k3_xboole_0('#skF_22',C_734)) = k3_xboole_0('#skF_9',C_734) ),
    inference(superposition,[status(thm),theory(equality)],[c_1980,c_18055])).

tff(c_18567,plain,(
    ! [C_736] : k3_xboole_0('#skF_23',k3_xboole_0('#skF_22',C_736)) = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5304,c_18287])).

tff(c_18737,plain,(
    k3_xboole_0('#skF_23','#skF_21') = '#skF_9' ),
    inference(superposition,[status(thm),theory(equality)],[c_1200,c_18567])).

tff(c_18797,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1302,c_18737])).
%------------------------------------------------------------------------------

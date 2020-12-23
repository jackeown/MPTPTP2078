%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0087+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:07:13 EST 2020

% Result     : Theorem 8.49s
% Output     : CNFRefutation 8.49s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 110 expanded)
%              Number of leaves         :   52 (  62 expanded)
%              Depth                    :   10
%              Number of atoms          :   72 ( 105 expanded)
%              Number of equality atoms :   39 (  55 expanded)
%              Maximal formula depth    :    9 (   4 average)
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

tff(f_628,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_xboole_0(A,B)
       => r1_xboole_0(A,k4_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_xboole_1)).

tff(f_136,axiom,(
    ? [A] : v1_xboole_0(A) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT001+2.ax',rc1_xboole_0)).

tff(f_546,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_boole)).

tff(f_113,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT001+2.ax',d7_xboole_0)).

tff(f_442,axiom,(
    ! [A,B] : k2_xboole_0(k3_xboole_0(A,B),k4_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_xboole_1)).

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

tff(f_63,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT001+2.ax',commutativity_k3_xboole_0)).

tff(f_305,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_616,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_564,axiom,(
    ! [A,B,C] :
      ( ~ ( ~ r1_xboole_0(A,k2_xboole_0(B,C))
          & r1_xboole_0(A,B)
          & r1_xboole_0(A,C) )
      & ~ ( ~ ( r1_xboole_0(A,B)
              & r1_xboole_0(A,C) )
          & r1_xboole_0(A,k2_xboole_0(B,C)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_xboole_1)).

tff(c_394,plain,(
    r1_xboole_0('#skF_21','#skF_22') ),
    inference(cnfTransformation,[status(thm)],[f_628])).

tff(c_112,plain,(
    v1_xboole_0('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_429,plain,(
    ! [A_317] :
      ( k1_xboole_0 = A_317
      | ~ v1_xboole_0(A_317) ) ),
    inference(cnfTransformation,[status(thm)],[f_546])).

tff(c_436,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(resolution,[status(thm)],[c_112,c_429])).

tff(c_80,plain,(
    ! [A_40,B_41] :
      ( k3_xboole_0(A_40,B_41) = k1_xboole_0
      | ~ r1_xboole_0(A_40,B_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_1267,plain,(
    ! [A_385,B_386] :
      ( k3_xboole_0(A_385,B_386) = '#skF_9'
      | ~ r1_xboole_0(A_385,B_386) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_436,c_80])).

tff(c_1293,plain,(
    k3_xboole_0('#skF_21','#skF_22') = '#skF_9' ),
    inference(resolution,[status(thm)],[c_394,c_1267])).

tff(c_6961,plain,(
    ! [A_580,B_581] : k2_xboole_0(k3_xboole_0(A_580,B_581),k4_xboole_0(A_580,B_581)) = A_580 ),
    inference(cnfTransformation,[status(thm)],[f_442])).

tff(c_7110,plain,(
    k2_xboole_0('#skF_9',k4_xboole_0('#skF_21','#skF_22')) = '#skF_21' ),
    inference(superposition,[status(thm),theory(equality)],[c_1293,c_6961])).

tff(c_288,plain,(
    ! [A_185] : k4_xboole_0(A_185,k1_xboole_0) = A_185 ),
    inference(cnfTransformation,[status(thm)],[f_404])).

tff(c_454,plain,(
    ! [A_185] : k4_xboole_0(A_185,'#skF_9') = A_185 ),
    inference(demodulation,[status(thm),theory(equality)],[c_436,c_288])).

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

tff(c_2466,plain,(
    ! [A_427,B_428] :
      ( k2_xboole_0(A_427,B_428) = B_428
      | ~ r1_tarski(A_427,B_428) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_286,c_302])).

tff(c_2622,plain,(
    ! [A_431,B_432] : k2_xboole_0(k4_xboole_0(A_431,B_432),A_431) = A_431 ),
    inference(resolution,[status(thm)],[c_278,c_2466])).

tff(c_224,plain,(
    ! [A_111,B_112] :
      ( k1_xboole_0 = A_111
      | k2_xboole_0(A_111,B_112) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_301])).

tff(c_1058,plain,(
    ! [A_111,B_112] :
      ( A_111 = '#skF_9'
      | k2_xboole_0(A_111,B_112) != '#skF_9' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_436,c_436,c_224])).

tff(c_3126,plain,(
    ! [A_443,B_444] :
      ( k4_xboole_0(A_443,B_444) = '#skF_9'
      | A_443 != '#skF_9' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2622,c_1058])).

tff(c_308,plain,(
    ! [A_207,B_208] : k4_xboole_0(A_207,k4_xboole_0(A_207,B_208)) = k3_xboole_0(A_207,B_208) ),
    inference(cnfTransformation,[status(thm)],[f_432])).

tff(c_3132,plain,(
    ! [A_443,B_444] :
      ( k4_xboole_0(A_443,'#skF_9') = k3_xboole_0(A_443,B_444)
      | A_443 != '#skF_9' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3126,c_308])).

tff(c_3259,plain,(
    ! [A_445,B_446] :
      ( k3_xboole_0(A_445,B_446) = A_445
      | A_445 != '#skF_9' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_454,c_3132])).

tff(c_1086,plain,(
    ! [B_374,A_375] : k3_xboole_0(B_374,A_375) = k3_xboole_0(A_375,B_374) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_228,plain,(
    ! [A_116,B_117] : r1_tarski(k3_xboole_0(A_116,B_117),A_116) ),
    inference(cnfTransformation,[status(thm)],[f_305])).

tff(c_1115,plain,(
    ! [B_374,A_375] : r1_tarski(k3_xboole_0(B_374,A_375),A_375) ),
    inference(superposition,[status(thm),theory(equality)],[c_1086,c_228])).

tff(c_2496,plain,(
    ! [B_374,A_375] : k2_xboole_0(k3_xboole_0(B_374,A_375),A_375) = A_375 ),
    inference(resolution,[status(thm)],[c_1115,c_2466])).

tff(c_3265,plain,(
    ! [A_445,B_446] :
      ( k2_xboole_0(A_445,B_446) = B_446
      | A_445 != '#skF_9' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3259,c_2496])).

tff(c_7275,plain,(
    k4_xboole_0('#skF_21','#skF_22') = '#skF_21' ),
    inference(superposition,[status(thm),theory(equality)],[c_7110,c_3265])).

tff(c_386,plain,(
    ! [A_297,B_298] : r1_xboole_0(k4_xboole_0(A_297,B_298),B_298) ),
    inference(cnfTransformation,[status(thm)],[f_616])).

tff(c_5350,plain,(
    ! [A_530,C_531,B_532] :
      ( r1_xboole_0(A_530,C_531)
      | ~ r1_xboole_0(A_530,k2_xboole_0(B_532,C_531)) ) ),
    inference(cnfTransformation,[status(thm)],[f_564])).

tff(c_5416,plain,(
    ! [A_297,B_532,C_531] : r1_xboole_0(k4_xboole_0(A_297,k2_xboole_0(B_532,C_531)),C_531) ),
    inference(resolution,[status(thm)],[c_386,c_5350])).

tff(c_9852,plain,(
    ! [A_642,A_643,B_644] : r1_xboole_0(k4_xboole_0(A_642,A_643),k4_xboole_0(A_643,B_644)) ),
    inference(superposition,[status(thm),theory(equality)],[c_6961,c_5416])).

tff(c_9898,plain,(
    ! [B_644] : r1_xboole_0('#skF_21',k4_xboole_0('#skF_22',B_644)) ),
    inference(superposition,[status(thm),theory(equality)],[c_7275,c_9852])).

tff(c_392,plain,(
    ~ r1_xboole_0('#skF_21',k4_xboole_0('#skF_22','#skF_23')) ),
    inference(cnfTransformation,[status(thm)],[f_628])).

tff(c_10052,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_9898,c_392])).
%------------------------------------------------------------------------------

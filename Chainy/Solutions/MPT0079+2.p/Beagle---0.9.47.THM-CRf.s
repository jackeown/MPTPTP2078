%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0079+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:07:13 EST 2020

% Result     : Theorem 46.40s
% Output     : CNFRefutation 46.54s
% Verified   : 
% Statistics : Number of formulae       :  118 ( 164 expanded)
%              Number of leaves         :   60 (  81 expanded)
%              Depth                    :   11
%              Number of atoms          :  103 ( 174 expanded)
%              Number of equality atoms :   68 ( 108 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_xboole_0 > r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > o_0_0_xboole_0 > k1_xboole_0 > #skF_13 > #skF_11 > #skF_18 > #skF_6 > #skF_1 > #skF_17 > #skF_4 > #skF_10 > #skF_12 > #skF_5 > #skF_19 > #skF_21 > #skF_9 > #skF_7 > #skF_20 > #skF_14 > #skF_22 > #skF_3 > #skF_2 > #skF_24 > #skF_23 > #skF_8 > #skF_16 > #skF_15

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

tff('#skF_24',type,(
    '#skF_24': $i )).

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

tff(f_581,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( k2_xboole_0(A,B) = k2_xboole_0(C,D)
          & r1_xboole_0(C,A)
          & r1_xboole_0(D,B) )
       => C = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_xboole_1)).

tff(f_136,axiom,(
    ? [A] : v1_xboole_0(A) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT001+2.ax',rc1_xboole_0)).

tff(f_546,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_boole)).

tff(f_404,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_396,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_xboole_1)).

tff(f_317,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_270,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(A,k2_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_xboole_1)).

tff(f_360,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_63,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT001+2.ax',commutativity_k3_xboole_0)).

tff(f_340,axiom,(
    ! [A,B] : k2_xboole_0(A,k3_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_xboole_1)).

tff(f_113,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT001+2.ax',d7_xboole_0)).

tff(f_370,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,k3_xboole_0(C,B)) = k3_xboole_0(k2_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_xboole_1)).

tff(f_61,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT001+2.ax',commutativity_k2_xboole_0)).

tff(f_125,axiom,(
    ! [A,B] : k2_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT001+2.ax',idempotence_k2_xboole_0)).

tff(f_344,axiom,(
    ! [A,B,C] : k2_xboole_0(A,k3_xboole_0(B,C)) = k3_xboole_0(k2_xboole_0(A,B),k2_xboole_0(A,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_xboole_1)).

tff(f_430,axiom,(
    ! [A,B] : k4_xboole_0(A,k3_xboole_0(A,B)) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

tff(f_444,axiom,(
    ! [A,B,C] : k4_xboole_0(A,k4_xboole_0(B,C)) = k2_xboole_0(k4_xboole_0(A,B),k3_xboole_0(A,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_xboole_1)).

tff(f_338,axiom,(
    ! [A,B] : k3_xboole_0(A,k2_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_xboole_1)).

tff(f_410,axiom,(
    ! [A,B] : k4_xboole_0(k2_xboole_0(A,B),B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).

tff(f_432,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_414,axiom,(
    ! [A,B,C] : k4_xboole_0(k2_xboole_0(A,B),C) = k2_xboole_0(k4_xboole_0(A,C),k4_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_xboole_1)).

tff(f_588,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(c_372,plain,(
    '#skF_22' != '#skF_23' ),
    inference(cnfTransformation,[status(thm)],[f_581])).

tff(c_112,plain,(
    v1_xboole_0('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_469,plain,(
    ! [A_298] :
      ( k1_xboole_0 = A_298
      | ~ v1_xboole_0(A_298) ) ),
    inference(cnfTransformation,[status(thm)],[f_546])).

tff(c_478,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(resolution,[status(thm)],[c_112,c_469])).

tff(c_288,plain,(
    ! [A_185] : k4_xboole_0(A_185,k1_xboole_0) = A_185 ),
    inference(cnfTransformation,[status(thm)],[f_404])).

tff(c_504,plain,(
    ! [A_185] : k4_xboole_0(A_185,'#skF_9') = A_185 ),
    inference(demodulation,[status(thm),theory(equality)],[c_478,c_288])).

tff(c_280,plain,(
    ! [A_179,B_180] :
      ( r1_tarski(A_179,B_180)
      | k4_xboole_0(A_179,B_180) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_396])).

tff(c_1959,plain,(
    ! [A_179,B_180] :
      ( r1_tarski(A_179,B_180)
      | k4_xboole_0(A_179,B_180) != '#skF_9' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_478,c_280])).

tff(c_234,plain,(
    ! [A_124] : k2_xboole_0(A_124,k1_xboole_0) = A_124 ),
    inference(cnfTransformation,[status(thm)],[f_317])).

tff(c_481,plain,(
    ! [A_124] : k2_xboole_0(A_124,'#skF_9') = A_124 ),
    inference(demodulation,[status(thm),theory(equality)],[c_478,c_234])).

tff(c_6396,plain,(
    ! [A_487,C_488,B_489] :
      ( r1_tarski(A_487,k2_xboole_0(C_488,B_489))
      | ~ r1_tarski(A_487,B_489) ) ),
    inference(cnfTransformation,[status(thm)],[f_270])).

tff(c_6475,plain,(
    ! [A_490,A_491] :
      ( r1_tarski(A_490,A_491)
      | ~ r1_tarski(A_490,'#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_481,c_6396])).

tff(c_6481,plain,(
    ! [A_179,A_491] :
      ( r1_tarski(A_179,A_491)
      | k4_xboole_0(A_179,'#skF_9') != '#skF_9' ) ),
    inference(resolution,[status(thm)],[c_1959,c_6475])).

tff(c_6512,plain,(
    ! [A_492,A_493] :
      ( r1_tarski(A_492,A_493)
      | A_492 != '#skF_9' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_504,c_6481])).

tff(c_258,plain,(
    ! [A_152,B_153] :
      ( k3_xboole_0(A_152,B_153) = A_152
      | ~ r1_tarski(A_152,B_153) ) ),
    inference(cnfTransformation,[status(thm)],[f_360])).

tff(c_6816,plain,(
    ! [A_497,A_498] :
      ( k3_xboole_0(A_497,A_498) = A_497
      | A_497 != '#skF_9' ) ),
    inference(resolution,[status(thm)],[c_6512,c_258])).

tff(c_746,plain,(
    ! [B_331,A_332] : k3_xboole_0(B_331,A_332) = k3_xboole_0(A_332,B_331) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_246,plain,(
    ! [A_134,B_135] : k2_xboole_0(A_134,k3_xboole_0(A_134,B_135)) = A_134 ),
    inference(cnfTransformation,[status(thm)],[f_340])).

tff(c_764,plain,(
    ! [B_331,A_332] : k2_xboole_0(B_331,k3_xboole_0(A_332,B_331)) = B_331 ),
    inference(superposition,[status(thm),theory(equality)],[c_746,c_246])).

tff(c_7265,plain,(
    ! [A_498] : k2_xboole_0(A_498,'#skF_9') = A_498 ),
    inference(superposition,[status(thm),theory(equality)],[c_6816,c_764])).

tff(c_374,plain,(
    r1_xboole_0('#skF_24','#skF_22') ),
    inference(cnfTransformation,[status(thm)],[f_581])).

tff(c_80,plain,(
    ! [A_40,B_41] :
      ( k3_xboole_0(A_40,B_41) = k1_xboole_0
      | ~ r1_xboole_0(A_40,B_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_2417,plain,(
    ! [A_401,B_402] :
      ( k3_xboole_0(A_401,B_402) = '#skF_9'
      | ~ r1_xboole_0(A_401,B_402) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_478,c_80])).

tff(c_2447,plain,(
    k3_xboole_0('#skF_24','#skF_22') = '#skF_9' ),
    inference(resolution,[status(thm)],[c_374,c_2417])).

tff(c_42709,plain,(
    ! [A_982,C_983,B_984] :
      ( k3_xboole_0(k2_xboole_0(A_982,C_983),B_984) = k2_xboole_0(A_982,k3_xboole_0(C_983,B_984))
      | ~ r1_tarski(A_982,B_984) ) ),
    inference(cnfTransformation,[status(thm)],[f_370])).

tff(c_1080,plain,(
    ! [B_353,A_354] : k2_xboole_0(B_353,A_354) = k2_xboole_0(A_354,B_353) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_378,plain,(
    k2_xboole_0('#skF_21','#skF_22') = k2_xboole_0('#skF_23','#skF_24') ),
    inference(cnfTransformation,[status(thm)],[f_581])).

tff(c_1139,plain,(
    k2_xboole_0('#skF_22','#skF_21') = k2_xboole_0('#skF_23','#skF_24') ),
    inference(superposition,[status(thm),theory(equality)],[c_1080,c_378])).

tff(c_104,plain,(
    ! [A_44] : k2_xboole_0(A_44,A_44) = A_44 ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_33609,plain,(
    ! [A_909,B_910,C_911] : k3_xboole_0(k2_xboole_0(A_909,B_910),k2_xboole_0(A_909,C_911)) = k2_xboole_0(A_909,k3_xboole_0(B_910,C_911)) ),
    inference(cnfTransformation,[status(thm)],[f_344])).

tff(c_33909,plain,(
    ! [A_44,B_910] : k3_xboole_0(k2_xboole_0(A_44,B_910),A_44) = k2_xboole_0(A_44,k3_xboole_0(B_910,A_44)) ),
    inference(superposition,[status(thm),theory(equality)],[c_104,c_33609])).

tff(c_33949,plain,(
    ! [A_912,B_913] : k3_xboole_0(k2_xboole_0(A_912,B_913),A_912) = A_912 ),
    inference(demodulation,[status(thm),theory(equality)],[c_764,c_33909])).

tff(c_34267,plain,(
    k3_xboole_0(k2_xboole_0('#skF_23','#skF_24'),'#skF_22') = '#skF_22' ),
    inference(superposition,[status(thm),theory(equality)],[c_1139,c_33949])).

tff(c_42751,plain,
    ( k2_xboole_0('#skF_23',k3_xboole_0('#skF_24','#skF_22')) = '#skF_22'
    | ~ r1_tarski('#skF_23','#skF_22') ),
    inference(superposition,[status(thm),theory(equality)],[c_42709,c_34267])).

tff(c_43170,plain,
    ( '#skF_22' = '#skF_23'
    | ~ r1_tarski('#skF_23','#skF_22') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7265,c_2447,c_42751])).

tff(c_43171,plain,(
    ~ r1_tarski('#skF_23','#skF_22') ),
    inference(negUnitSimplification,[status(thm)],[c_372,c_43170])).

tff(c_376,plain,(
    r1_xboole_0('#skF_23','#skF_21') ),
    inference(cnfTransformation,[status(thm)],[f_581])).

tff(c_2446,plain,(
    k3_xboole_0('#skF_23','#skF_21') = '#skF_9' ),
    inference(resolution,[status(thm)],[c_376,c_2417])).

tff(c_8973,plain,(
    ! [A_558,B_559] : k4_xboole_0(A_558,k3_xboole_0(A_558,B_559)) = k4_xboole_0(A_558,B_559) ),
    inference(cnfTransformation,[status(thm)],[f_430])).

tff(c_9035,plain,(
    k4_xboole_0('#skF_23','#skF_21') = k4_xboole_0('#skF_23','#skF_9') ),
    inference(superposition,[status(thm),theory(equality)],[c_2446,c_8973])).

tff(c_9079,plain,(
    k4_xboole_0('#skF_23','#skF_21') = '#skF_23' ),
    inference(demodulation,[status(thm),theory(equality)],[c_504,c_9035])).

tff(c_35774,plain,(
    ! [A_922,B_923,C_924] : k2_xboole_0(k4_xboole_0(A_922,B_923),k3_xboole_0(A_922,C_924)) = k4_xboole_0(A_922,k4_xboole_0(B_923,C_924)) ),
    inference(cnfTransformation,[status(thm)],[f_444])).

tff(c_36062,plain,(
    ! [C_924] : k4_xboole_0('#skF_23',k4_xboole_0('#skF_21',C_924)) = k2_xboole_0('#skF_23',k3_xboole_0('#skF_23',C_924)) ),
    inference(superposition,[status(thm),theory(equality)],[c_9079,c_35774])).

tff(c_36222,plain,(
    ! [C_924] : k4_xboole_0('#skF_23',k4_xboole_0('#skF_21',C_924)) = '#skF_23' ),
    inference(demodulation,[status(thm),theory(equality)],[c_246,c_36062])).

tff(c_244,plain,(
    ! [A_132,B_133] : k3_xboole_0(A_132,k2_xboole_0(A_132,B_133)) = A_132 ),
    inference(cnfTransformation,[status(thm)],[f_338])).

tff(c_1113,plain,(
    ! [A_354,B_353] : k3_xboole_0(A_354,k2_xboole_0(B_353,A_354)) = A_354 ),
    inference(superposition,[status(thm),theory(equality)],[c_1080,c_244])).

tff(c_8,plain,(
    ! [B_8,A_7] : k3_xboole_0(B_8,A_7) = k3_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_292,plain,(
    ! [A_187,B_188] : k4_xboole_0(k2_xboole_0(A_187,B_188),B_188) = k4_xboole_0(A_187,B_188) ),
    inference(cnfTransformation,[status(thm)],[f_410])).

tff(c_7768,plain,(
    ! [A_519,B_520] : k4_xboole_0(A_519,k4_xboole_0(A_519,B_520)) = k3_xboole_0(A_519,B_520) ),
    inference(cnfTransformation,[status(thm)],[f_432])).

tff(c_7823,plain,(
    ! [A_187,B_188] : k4_xboole_0(k2_xboole_0(A_187,B_188),k4_xboole_0(A_187,B_188)) = k3_xboole_0(k2_xboole_0(A_187,B_188),B_188) ),
    inference(superposition,[status(thm),theory(equality)],[c_292,c_7768])).

tff(c_104726,plain,(
    ! [A_1544,B_1545] : k4_xboole_0(k2_xboole_0(A_1544,B_1545),k4_xboole_0(A_1544,B_1545)) = B_1545 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1113,c_8,c_7823])).

tff(c_105216,plain,(
    k4_xboole_0(k2_xboole_0('#skF_23','#skF_24'),k4_xboole_0('#skF_21','#skF_22')) = '#skF_22' ),
    inference(superposition,[status(thm),theory(equality)],[c_378,c_104726])).

tff(c_38663,plain,(
    ! [A_935,C_936,B_937] : k2_xboole_0(k4_xboole_0(A_935,C_936),k4_xboole_0(B_937,C_936)) = k4_xboole_0(k2_xboole_0(A_935,B_937),C_936) ),
    inference(cnfTransformation,[status(thm)],[f_414])).

tff(c_382,plain,(
    ! [A_278,B_279] : r1_tarski(A_278,k2_xboole_0(A_278,B_279)) ),
    inference(cnfTransformation,[status(thm)],[f_588])).

tff(c_156135,plain,(
    ! [A_1887,C_1888,B_1889] : r1_tarski(k4_xboole_0(A_1887,C_1888),k4_xboole_0(k2_xboole_0(A_1887,B_1889),C_1888)) ),
    inference(superposition,[status(thm),theory(equality)],[c_38663,c_382])).

tff(c_156219,plain,(
    r1_tarski(k4_xboole_0('#skF_23',k4_xboole_0('#skF_21','#skF_22')),'#skF_22') ),
    inference(superposition,[status(thm),theory(equality)],[c_105216,c_156135])).

tff(c_156564,plain,(
    r1_tarski('#skF_23','#skF_22') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36222,c_156219])).

tff(c_156566,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_43171,c_156564])).
%------------------------------------------------------------------------------

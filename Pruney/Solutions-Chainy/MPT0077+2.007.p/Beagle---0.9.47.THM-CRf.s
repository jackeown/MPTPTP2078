%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:43:36 EST 2020

% Result     : Theorem 22.18s
% Output     : CNFRefutation 22.18s
% Verified   : 
% Statistics : Number of formulae       :  191 ( 453 expanded)
%              Number of leaves         :   35 ( 157 expanded)
%              Depth                    :   10
%              Number of atoms          :  244 ( 717 expanded)
%              Number of equality atoms :   83 ( 251 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_116,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ~ ( ~ r1_xboole_0(A,k2_xboole_0(B,C))
            & r1_xboole_0(A,B)
            & r1_xboole_0(A,C) )
        & ~ ( ~ ( r1_xboole_0(A,B)
                & r1_xboole_0(A,C) )
            & r1_xboole_0(A,k2_xboole_0(B,C)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_xboole_1)).

tff(f_63,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_69,axiom,(
    ! [A,B] : k4_xboole_0(k2_xboole_0(A,B),B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).

tff(f_53,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_77,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_61,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_55,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_99,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(k2_xboole_0(A,C),k2_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_xboole_1)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(k4_xboole_0(C,B),k4_xboole_0(C,A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_xboole_1)).

tff(f_51,axiom,(
    ! [A,B,C] : k3_xboole_0(A,k2_xboole_0(B,C)) = k2_xboole_0(k3_xboole_0(A,B),k3_xboole_0(A,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_xboole_1)).

tff(f_93,axiom,(
    ! [A,B,C,D] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,D)
        & r1_xboole_0(B,D) )
     => r1_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_xboole_1)).

tff(f_73,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).

tff(f_83,axiom,(
    ! [A,B] : k2_xboole_0(k3_xboole_0(A,B),k4_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_xboole_1)).

tff(f_75,axiom,(
    ! [A,B] : k4_xboole_0(A,k3_xboole_0(A,B)) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

tff(f_85,axiom,(
    ! [A,B,C] : k4_xboole_0(A,k4_xboole_0(B,C)) = k2_xboole_0(k4_xboole_0(A,B),k3_xboole_0(A,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_xboole_1)).

tff(c_27147,plain,(
    ! [A_623,B_624] :
      ( r1_xboole_0(A_623,B_624)
      | k3_xboole_0(A_623,B_624) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_8,plain,(
    ! [B_6,A_5] :
      ( r1_xboole_0(B_6,A_5)
      | ~ r1_xboole_0(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_27234,plain,(
    ! [B_630,A_631] :
      ( r1_xboole_0(B_630,A_631)
      | k3_xboole_0(A_631,B_630) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_27147,c_8])).

tff(c_204,plain,(
    ! [A_67,B_68] :
      ( r1_xboole_0(A_67,B_68)
      | k3_xboole_0(A_67,B_68) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_58,plain,
    ( ~ r1_xboole_0('#skF_2','#skF_4')
    | ~ r1_xboole_0('#skF_2','#skF_3')
    | r1_xboole_0('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_150,plain,(
    ~ r1_xboole_0('#skF_2','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_58])).

tff(c_210,plain,(
    k3_xboole_0('#skF_2','#skF_3') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_204,c_150])).

tff(c_24,plain,(
    ! [A_22] : k4_xboole_0(A_22,k1_xboole_0) = A_22 ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_265,plain,(
    ! [A_78,B_79] : k4_xboole_0(k2_xboole_0(A_78,B_79),B_79) = k4_xboole_0(A_78,B_79) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_272,plain,(
    ! [A_78] : k4_xboole_0(A_78,k1_xboole_0) = k2_xboole_0(A_78,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_265,c_24])).

tff(c_287,plain,(
    ! [A_78] : k2_xboole_0(A_78,k1_xboole_0) = A_78 ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_272])).

tff(c_16,plain,(
    ! [A_15] : k3_xboole_0(A_15,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_290,plain,(
    ! [A_80,B_81] : k4_xboole_0(A_80,k4_xboole_0(A_80,B_81)) = k3_xboole_0(A_80,B_81) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_325,plain,(
    ! [A_22] : k4_xboole_0(A_22,A_22) = k3_xboole_0(A_22,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_290])).

tff(c_333,plain,(
    ! [A_22] : k4_xboole_0(A_22,A_22) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_325])).

tff(c_20466,plain,(
    ! [A_465,B_466] : k2_xboole_0(A_465,k4_xboole_0(B_466,A_465)) = k2_xboole_0(A_465,B_466) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_20513,plain,(
    ! [A_22] : k2_xboole_0(A_22,k1_xboole_0) = k2_xboole_0(A_22,A_22) ),
    inference(superposition,[status(thm),theory(equality)],[c_333,c_20466])).

tff(c_20543,plain,(
    ! [A_22] : k2_xboole_0(A_22,A_22) = A_22 ),
    inference(demodulation,[status(thm),theory(equality)],[c_287,c_20513])).

tff(c_18,plain,(
    ! [A_16] : r1_tarski(k1_xboole_0,A_16) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_334,plain,(
    ! [A_82] : k2_xboole_0(A_82,k1_xboole_0) = A_82 ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_272])).

tff(c_363,plain,(
    ! [B_2] : k2_xboole_0(k1_xboole_0,B_2) = B_2 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_334])).

tff(c_21347,plain,(
    ! [A_486,C_487,B_488] :
      ( r1_tarski(k2_xboole_0(A_486,C_487),k2_xboole_0(B_488,C_487))
      | ~ r1_tarski(A_486,B_488) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_21386,plain,(
    ! [B_2,B_488] :
      ( r1_tarski(B_2,k2_xboole_0(B_488,B_2))
      | ~ r1_tarski(k1_xboole_0,B_488) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_363,c_21347])).

tff(c_21412,plain,(
    ! [B_489,B_490] : r1_tarski(B_489,k2_xboole_0(B_490,B_489)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_21386])).

tff(c_21427,plain,(
    ! [A_22] : r1_tarski(A_22,A_22) ),
    inference(superposition,[status(thm),theory(equality)],[c_20543,c_21412])).

tff(c_21409,plain,(
    ! [B_2,B_488] : r1_tarski(B_2,k2_xboole_0(B_488,B_2)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_21386])).

tff(c_15150,plain,(
    ! [C_364,B_365,A_366] :
      ( r1_tarski(k4_xboole_0(C_364,B_365),k4_xboole_0(C_364,A_366))
      | ~ r1_tarski(A_366,B_365) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_15246,plain,(
    ! [A_22,B_365] :
      ( r1_tarski(k4_xboole_0(A_22,B_365),A_22)
      | ~ r1_tarski(k1_xboole_0,B_365) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_15150])).

tff(c_15256,plain,(
    ! [A_367,B_368] : r1_tarski(k4_xboole_0(A_367,B_368),A_367) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_15246])).

tff(c_15308,plain,(
    ! [A_22] : r1_tarski(A_22,A_22) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_15256])).

tff(c_15798,plain,(
    ! [A_380,C_381,B_382] :
      ( r1_tarski(k2_xboole_0(A_380,C_381),k2_xboole_0(B_382,C_381))
      | ~ r1_tarski(A_380,B_382) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_15837,plain,(
    ! [B_2,B_382] :
      ( r1_tarski(B_2,k2_xboole_0(B_382,B_2))
      | ~ r1_tarski(k1_xboole_0,B_382) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_363,c_15798])).

tff(c_15862,plain,(
    ! [B_2,B_382] : r1_tarski(B_2,k2_xboole_0(B_382,B_2)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_15837])).

tff(c_52,plain,
    ( r1_xboole_0('#skF_2',k2_xboole_0('#skF_3','#skF_4'))
    | r1_xboole_0('#skF_5','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_64,plain,
    ( r1_xboole_0('#skF_2',k2_xboole_0('#skF_4','#skF_3'))
    | r1_xboole_0('#skF_5','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_52])).

tff(c_476,plain,(
    r1_xboole_0('#skF_5','#skF_7') ),
    inference(splitLeft,[status(thm)],[c_64])).

tff(c_4,plain,(
    ! [A_3,B_4] :
      ( k3_xboole_0(A_3,B_4) = k1_xboole_0
      | ~ r1_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_482,plain,(
    k3_xboole_0('#skF_5','#skF_7') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_476,c_4])).

tff(c_56,plain,
    ( r1_xboole_0('#skF_2',k2_xboole_0('#skF_3','#skF_4'))
    | r1_xboole_0('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_63,plain,
    ( r1_xboole_0('#skF_2',k2_xboole_0('#skF_4','#skF_3'))
    | r1_xboole_0('#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_56])).

tff(c_451,plain,(
    r1_xboole_0('#skF_5','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_63])).

tff(c_457,plain,(
    k3_xboole_0('#skF_5','#skF_6') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_451,c_4])).

tff(c_2847,plain,(
    ! [A_154,B_155,C_156] : k2_xboole_0(k3_xboole_0(A_154,B_155),k3_xboole_0(A_154,C_156)) = k3_xboole_0(A_154,k2_xboole_0(B_155,C_156)) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_2948,plain,(
    ! [C_156] : k3_xboole_0('#skF_5',k2_xboole_0('#skF_6',C_156)) = k2_xboole_0(k1_xboole_0,k3_xboole_0('#skF_5',C_156)) ),
    inference(superposition,[status(thm),theory(equality)],[c_457,c_2847])).

tff(c_2989,plain,(
    ! [C_156] : k3_xboole_0('#skF_5',k2_xboole_0('#skF_6',C_156)) = k3_xboole_0('#skF_5',C_156) ),
    inference(demodulation,[status(thm),theory(equality)],[c_363,c_2948])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( r1_xboole_0(A_3,B_4)
      | k3_xboole_0(A_3,B_4) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_60,plain,
    ( r1_xboole_0('#skF_2',k2_xboole_0('#skF_3','#skF_4'))
    | ~ r1_xboole_0('#skF_5',k2_xboole_0('#skF_6','#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_65,plain,
    ( r1_xboole_0('#skF_2',k2_xboole_0('#skF_4','#skF_3'))
    | ~ r1_xboole_0('#skF_5',k2_xboole_0('#skF_6','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_60])).

tff(c_618,plain,(
    ~ r1_xboole_0('#skF_5',k2_xboole_0('#skF_6','#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_65])).

tff(c_642,plain,(
    k3_xboole_0('#skF_5',k2_xboole_0('#skF_6','#skF_7')) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_618])).

tff(c_14382,plain,(
    k3_xboole_0('#skF_5','#skF_7') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2989,c_642])).

tff(c_14385,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_482,c_14382])).

tff(c_14386,plain,(
    r1_xboole_0('#skF_2',k2_xboole_0('#skF_4','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_65])).

tff(c_18820,plain,(
    ! [A_431,C_432,B_433,D_434] :
      ( r1_xboole_0(A_431,C_432)
      | ~ r1_xboole_0(B_433,D_434)
      | ~ r1_tarski(C_432,D_434)
      | ~ r1_tarski(A_431,B_433) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_20124,plain,(
    ! [A_451,C_452] :
      ( r1_xboole_0(A_451,C_452)
      | ~ r1_tarski(C_452,k2_xboole_0('#skF_4','#skF_3'))
      | ~ r1_tarski(A_451,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_14386,c_18820])).

tff(c_20162,plain,(
    ! [A_453] :
      ( r1_xboole_0(A_453,'#skF_3')
      | ~ r1_tarski(A_453,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_15862,c_20124])).

tff(c_20173,plain,(
    ~ r1_tarski('#skF_2','#skF_2') ),
    inference(resolution,[status(thm)],[c_20162,c_150])).

tff(c_20182,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_15308,c_20173])).

tff(c_20183,plain,(
    r1_xboole_0('#skF_2',k2_xboole_0('#skF_4','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_23797,plain,(
    ! [A_536,C_537,B_538,D_539] :
      ( r1_xboole_0(A_536,C_537)
      | ~ r1_xboole_0(B_538,D_539)
      | ~ r1_tarski(C_537,D_539)
      | ~ r1_tarski(A_536,B_538) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_24404,plain,(
    ! [A_550,C_551] :
      ( r1_xboole_0(A_550,C_551)
      | ~ r1_tarski(C_551,k2_xboole_0('#skF_4','#skF_3'))
      | ~ r1_tarski(A_550,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_20183,c_23797])).

tff(c_24683,plain,(
    ! [A_554] :
      ( r1_xboole_0(A_554,'#skF_3')
      | ~ r1_tarski(A_554,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_21409,c_24404])).

tff(c_24694,plain,(
    ~ r1_tarski('#skF_2','#skF_2') ),
    inference(resolution,[status(thm)],[c_24683,c_150])).

tff(c_24703,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_21427,c_24694])).

tff(c_24704,plain,(
    r1_xboole_0('#skF_2',k2_xboole_0('#skF_4','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_63])).

tff(c_24719,plain,(
    k3_xboole_0('#skF_2',k2_xboole_0('#skF_4','#skF_3')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_24704,c_4])).

tff(c_22,plain,(
    ! [A_20,B_21] : k2_xboole_0(A_20,k4_xboole_0(B_21,A_20)) = k2_xboole_0(A_20,B_21) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_28,plain,(
    ! [A_24,B_25] : k4_xboole_0(k2_xboole_0(A_24,B_25),B_25) = k4_xboole_0(A_24,B_25) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_24857,plain,(
    ! [A_560,B_561] : k2_xboole_0(A_560,k4_xboole_0(B_561,A_560)) = k2_xboole_0(A_560,B_561) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_24895,plain,(
    ! [B_25,A_24] : k2_xboole_0(B_25,k4_xboole_0(A_24,B_25)) = k2_xboole_0(B_25,k2_xboole_0(A_24,B_25)) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_24857])).

tff(c_24916,plain,(
    ! [B_25,A_24] : k2_xboole_0(B_25,k2_xboole_0(A_24,B_25)) = k2_xboole_0(B_25,A_24) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_24895])).

tff(c_26474,plain,(
    ! [A_610,B_611,C_612] : k2_xboole_0(k3_xboole_0(A_610,B_611),k3_xboole_0(A_610,C_612)) = k3_xboole_0(A_610,k2_xboole_0(B_611,C_612)) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_26560,plain,(
    ! [B_611] : k3_xboole_0('#skF_2',k2_xboole_0(B_611,k2_xboole_0('#skF_4','#skF_3'))) = k2_xboole_0(k3_xboole_0('#skF_2',B_611),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_24719,c_26474])).

tff(c_27019,plain,(
    ! [B_620] : k3_xboole_0('#skF_2',k2_xboole_0(B_620,k2_xboole_0('#skF_4','#skF_3'))) = k3_xboole_0('#skF_2',B_620) ),
    inference(demodulation,[status(thm),theory(equality)],[c_287,c_26560])).

tff(c_27075,plain,(
    k3_xboole_0('#skF_2',k2_xboole_0('#skF_3','#skF_4')) = k3_xboole_0('#skF_2','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_24916,c_27019])).

tff(c_27113,plain,(
    k3_xboole_0('#skF_2','#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_24719,c_2,c_27075])).

tff(c_27115,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_210,c_27113])).

tff(c_27116,plain,
    ( ~ r1_xboole_0('#skF_2','#skF_4')
    | r1_xboole_0('#skF_5','#skF_6') ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_27125,plain,(
    ~ r1_xboole_0('#skF_2','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_27116])).

tff(c_27244,plain,(
    k3_xboole_0('#skF_4','#skF_2') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_27234,c_27125])).

tff(c_32,plain,(
    ! [A_29,B_30] : k4_xboole_0(A_29,k2_xboole_0(A_29,B_30)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_94749,plain,(
    ! [C_1565,B_1566,A_1567] :
      ( r1_tarski(k4_xboole_0(C_1565,B_1566),k4_xboole_0(C_1565,A_1567))
      | ~ r1_tarski(A_1567,B_1566) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_94851,plain,(
    ! [A_22,B_1566] :
      ( r1_tarski(k4_xboole_0(A_22,B_1566),A_22)
      | ~ r1_tarski(k1_xboole_0,B_1566) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_94749])).

tff(c_94862,plain,(
    ! [A_1568,B_1569] : r1_tarski(k4_xboole_0(A_1568,B_1569),A_1568) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_94851])).

tff(c_94917,plain,(
    ! [A_22] : r1_tarski(A_22,A_22) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_94862])).

tff(c_27278,plain,(
    ! [A_634,B_635] : k2_xboole_0(k3_xboole_0(A_634,B_635),k4_xboole_0(A_634,B_635)) = A_634 ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_27308,plain,(
    ! [A_15] : k2_xboole_0(k1_xboole_0,k4_xboole_0(A_15,k1_xboole_0)) = A_15 ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_27278])).

tff(c_27318,plain,(
    ! [A_15] : k2_xboole_0(k1_xboole_0,A_15) = A_15 ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_27308])).

tff(c_95039,plain,(
    ! [A_1574,C_1575,B_1576] :
      ( r1_tarski(k2_xboole_0(A_1574,C_1575),k2_xboole_0(B_1576,C_1575))
      | ~ r1_tarski(A_1574,B_1576) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_95084,plain,(
    ! [A_15,B_1576] :
      ( r1_tarski(A_15,k2_xboole_0(B_1576,A_15))
      | ~ r1_tarski(k1_xboole_0,B_1576) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_27318,c_95039])).

tff(c_95118,plain,(
    ! [A_1577,B_1578] : r1_tarski(A_1577,k2_xboole_0(B_1578,A_1577)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_95084])).

tff(c_95151,plain,(
    ! [B_2,A_1] : r1_tarski(B_2,k2_xboole_0(B_2,A_1)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_95118])).

tff(c_85824,plain,(
    ! [C_1385,B_1386,A_1387] :
      ( r1_tarski(k4_xboole_0(C_1385,B_1386),k4_xboole_0(C_1385,A_1387))
      | ~ r1_tarski(A_1387,B_1386) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_85938,plain,(
    ! [A_22,B_1386] :
      ( r1_tarski(k4_xboole_0(A_22,B_1386),A_22)
      | ~ r1_tarski(k1_xboole_0,B_1386) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_85824])).

tff(c_85948,plain,(
    ! [A_1388,B_1389] : r1_tarski(k4_xboole_0(A_1388,B_1389),A_1388) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_85938])).

tff(c_86009,plain,(
    ! [A_22] : r1_tarski(A_22,A_22) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_85948])).

tff(c_86033,plain,(
    ! [A_1391,C_1392,B_1393] :
      ( r1_tarski(k2_xboole_0(A_1391,C_1392),k2_xboole_0(B_1393,C_1392))
      | ~ r1_tarski(A_1391,B_1393) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_86066,plain,(
    ! [A_15,B_1393] :
      ( r1_tarski(A_15,k2_xboole_0(B_1393,A_15))
      | ~ r1_tarski(k1_xboole_0,B_1393) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_27318,c_86033])).

tff(c_86170,plain,(
    ! [A_1396,B_1397] : r1_tarski(A_1396,k2_xboole_0(B_1397,A_1396)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_86066])).

tff(c_86197,plain,(
    ! [B_2,A_1] : r1_tarski(B_2,k2_xboole_0(B_2,A_1)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_86170])).

tff(c_27442,plain,(
    r1_xboole_0('#skF_5','#skF_7') ),
    inference(splitLeft,[status(thm)],[c_64])).

tff(c_27448,plain,(
    k3_xboole_0('#skF_5','#skF_7') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_27442,c_4])).

tff(c_27465,plain,(
    r1_xboole_0('#skF_5','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_63])).

tff(c_27471,plain,(
    k3_xboole_0('#skF_5','#skF_6') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_27465,c_4])).

tff(c_30939,plain,(
    ! [A_723,B_724,C_725] : k2_xboole_0(k3_xboole_0(A_723,B_724),k3_xboole_0(A_723,C_725)) = k3_xboole_0(A_723,k2_xboole_0(B_724,C_725)) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_46430,plain,(
    ! [A_936,C_937,B_938] : k2_xboole_0(k3_xboole_0(A_936,C_937),k3_xboole_0(A_936,B_938)) = k3_xboole_0(A_936,k2_xboole_0(B_938,C_937)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_30939])).

tff(c_46794,plain,(
    ! [C_937] : k3_xboole_0('#skF_5',k2_xboole_0('#skF_6',C_937)) = k2_xboole_0(k3_xboole_0('#skF_5',C_937),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_27471,c_46430])).

tff(c_46927,plain,(
    ! [C_937] : k3_xboole_0('#skF_5',k2_xboole_0('#skF_6',C_937)) = k3_xboole_0('#skF_5',C_937) ),
    inference(demodulation,[status(thm),theory(equality)],[c_27318,c_2,c_46794])).

tff(c_27522,plain,(
    ~ r1_xboole_0('#skF_5',k2_xboole_0('#skF_6','#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_65])).

tff(c_27554,plain,(
    k3_xboole_0('#skF_5',k2_xboole_0('#skF_6','#skF_7')) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_27522])).

tff(c_84275,plain,(
    k3_xboole_0('#skF_5','#skF_7') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_46927,c_27554])).

tff(c_84278,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_27448,c_84275])).

tff(c_84279,plain,(
    r1_xboole_0('#skF_2',k2_xboole_0('#skF_4','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_65])).

tff(c_86830,plain,(
    ! [A_1410,C_1411,B_1412,D_1413] :
      ( r1_xboole_0(A_1410,C_1411)
      | ~ r1_xboole_0(B_1412,D_1413)
      | ~ r1_tarski(C_1411,D_1413)
      | ~ r1_tarski(A_1410,B_1412) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_91531,plain,(
    ! [A_1498,C_1499] :
      ( r1_xboole_0(A_1498,C_1499)
      | ~ r1_tarski(C_1499,k2_xboole_0('#skF_4','#skF_3'))
      | ~ r1_tarski(A_1498,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_84279,c_86830])).

tff(c_92991,plain,(
    ! [A_1520] :
      ( r1_xboole_0(A_1520,'#skF_4')
      | ~ r1_tarski(A_1520,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_86197,c_91531])).

tff(c_93002,plain,(
    ~ r1_tarski('#skF_2','#skF_2') ),
    inference(resolution,[status(thm)],[c_92991,c_27125])).

tff(c_93011,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_86009,c_93002])).

tff(c_93012,plain,(
    r1_xboole_0('#skF_2',k2_xboole_0('#skF_4','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_63])).

tff(c_96040,plain,(
    ! [A_1597,C_1598,B_1599,D_1600] :
      ( r1_xboole_0(A_1597,C_1598)
      | ~ r1_xboole_0(B_1599,D_1600)
      | ~ r1_tarski(C_1598,D_1600)
      | ~ r1_tarski(A_1597,B_1599) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_101168,plain,(
    ! [A_1688,C_1689] :
      ( r1_xboole_0(A_1688,C_1689)
      | ~ r1_tarski(C_1689,k2_xboole_0('#skF_4','#skF_3'))
      | ~ r1_tarski(A_1688,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_93012,c_96040])).

tff(c_102316,plain,(
    ! [A_1703] :
      ( r1_xboole_0(A_1703,'#skF_4')
      | ~ r1_tarski(A_1703,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_95151,c_101168])).

tff(c_102327,plain,(
    ~ r1_tarski('#skF_2','#skF_2') ),
    inference(resolution,[status(thm)],[c_102316,c_27125])).

tff(c_102336,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_94917,c_102327])).

tff(c_102337,plain,(
    r1_xboole_0('#skF_2',k2_xboole_0('#skF_4','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_102376,plain,(
    r1_xboole_0(k2_xboole_0('#skF_4','#skF_3'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_102337,c_8])).

tff(c_102431,plain,(
    k3_xboole_0(k2_xboole_0('#skF_4','#skF_3'),'#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_102376,c_4])).

tff(c_34,plain,(
    ! [A_31,B_32] : k4_xboole_0(A_31,k3_xboole_0(A_31,B_32)) = k4_xboole_0(A_31,B_32) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_102835,plain,(
    k4_xboole_0(k2_xboole_0('#skF_4','#skF_3'),k1_xboole_0) = k4_xboole_0(k2_xboole_0('#skF_4','#skF_3'),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_102431,c_34])).

tff(c_102845,plain,(
    k4_xboole_0(k2_xboole_0('#skF_4','#skF_3'),'#skF_2') = k2_xboole_0('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_102835])).

tff(c_105295,plain,(
    ! [A_1786,B_1787,C_1788] : k2_xboole_0(k4_xboole_0(A_1786,B_1787),k3_xboole_0(A_1786,C_1788)) = k4_xboole_0(A_1786,k4_xboole_0(B_1787,C_1788)) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_105451,plain,(
    ! [A_29,B_30,C_1788] : k4_xboole_0(A_29,k4_xboole_0(k2_xboole_0(A_29,B_30),C_1788)) = k2_xboole_0(k1_xboole_0,k3_xboole_0(A_29,C_1788)) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_105295])).

tff(c_108010,plain,(
    ! [A_1839,B_1840,C_1841] : k4_xboole_0(A_1839,k4_xboole_0(k2_xboole_0(A_1839,B_1840),C_1841)) = k3_xboole_0(A_1839,C_1841) ),
    inference(demodulation,[status(thm),theory(equality)],[c_27318,c_105451])).

tff(c_108159,plain,(
    k4_xboole_0('#skF_4',k2_xboole_0('#skF_4','#skF_3')) = k3_xboole_0('#skF_4','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_102845,c_108010])).

tff(c_108245,plain,(
    k3_xboole_0('#skF_4','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_108159])).

tff(c_108247,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_27244,c_108245])).

tff(c_108248,plain,(
    r1_xboole_0('#skF_5','#skF_6') ),
    inference(splitRight,[status(thm)],[c_27116])).

tff(c_108330,plain,(
    ! [A_1848,B_1849] :
      ( k3_xboole_0(A_1848,B_1849) = k1_xboole_0
      | ~ r1_xboole_0(A_1848,B_1849) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_108370,plain,(
    k3_xboole_0('#skF_5','#skF_6') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_108248,c_108330])).

tff(c_108805,plain,(
    ! [A_1865,B_1866] : k2_xboole_0(k3_xboole_0(A_1865,B_1866),k4_xboole_0(A_1865,B_1866)) = A_1865 ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_108889,plain,(
    ! [A_15] : k2_xboole_0(k1_xboole_0,k4_xboole_0(A_15,k1_xboole_0)) = A_15 ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_108805])).

tff(c_108917,plain,(
    ! [A_15] : k2_xboole_0(k1_xboole_0,A_15) = A_15 ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_108889])).

tff(c_27117,plain,(
    r1_xboole_0('#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_108249,plain,(
    r1_xboole_0('#skF_2','#skF_4') ),
    inference(splitRight,[status(thm)],[c_27116])).

tff(c_54,plain,
    ( ~ r1_xboole_0('#skF_2','#skF_4')
    | ~ r1_xboole_0('#skF_2','#skF_3')
    | r1_xboole_0('#skF_5','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_108261,plain,(
    r1_xboole_0('#skF_5','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_27117,c_108249,c_54])).

tff(c_108367,plain,(
    k3_xboole_0('#skF_5','#skF_7') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_108261,c_108330])).

tff(c_109828,plain,(
    ! [A_1896,B_1897,C_1898] : k2_xboole_0(k3_xboole_0(A_1896,B_1897),k3_xboole_0(A_1896,C_1898)) = k3_xboole_0(A_1896,k2_xboole_0(B_1897,C_1898)) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_109930,plain,(
    ! [B_1897] : k3_xboole_0('#skF_5',k2_xboole_0(B_1897,'#skF_7')) = k2_xboole_0(k3_xboole_0('#skF_5',B_1897),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_108367,c_109828])).

tff(c_109965,plain,(
    ! [B_1897] : k3_xboole_0('#skF_5',k2_xboole_0(B_1897,'#skF_7')) = k3_xboole_0('#skF_5',B_1897) ),
    inference(demodulation,[status(thm),theory(equality)],[c_108917,c_2,c_109930])).

tff(c_62,plain,
    ( ~ r1_xboole_0('#skF_2','#skF_4')
    | ~ r1_xboole_0('#skF_2','#skF_3')
    | ~ r1_xboole_0('#skF_5',k2_xboole_0('#skF_6','#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_108385,plain,(
    ~ r1_xboole_0('#skF_5',k2_xboole_0('#skF_6','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_27117,c_108249,c_62])).

tff(c_108389,plain,(
    k3_xboole_0('#skF_5',k2_xboole_0('#skF_6','#skF_7')) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_108385])).

tff(c_124470,plain,(
    k3_xboole_0('#skF_5','#skF_6') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_109965,c_108389])).

tff(c_124473,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_108370,c_124470])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:31:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 22.18/13.71  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 22.18/13.73  
% 22.18/13.73  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 22.18/13.73  %$ r2_hidden > r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 22.18/13.73  
% 22.18/13.73  %Foreground sorts:
% 22.18/13.73  
% 22.18/13.73  
% 22.18/13.73  %Background operators:
% 22.18/13.73  
% 22.18/13.73  
% 22.18/13.73  %Foreground operators:
% 22.18/13.73  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 22.18/13.73  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 22.18/13.73  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 22.18/13.73  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 22.18/13.73  tff('#skF_7', type, '#skF_7': $i).
% 22.18/13.73  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 22.18/13.73  tff('#skF_5', type, '#skF_5': $i).
% 22.18/13.73  tff('#skF_6', type, '#skF_6': $i).
% 22.18/13.73  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 22.18/13.73  tff('#skF_2', type, '#skF_2': $i).
% 22.18/13.73  tff('#skF_3', type, '#skF_3': $i).
% 22.18/13.73  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 22.18/13.73  tff('#skF_4', type, '#skF_4': $i).
% 22.18/13.73  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 22.18/13.73  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 22.18/13.73  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 22.18/13.73  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 22.18/13.73  
% 22.18/13.76  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 22.18/13.76  tff(f_35, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 22.18/13.76  tff(f_116, negated_conjecture, ~(![A, B, C]: (~((~r1_xboole_0(A, k2_xboole_0(B, C)) & r1_xboole_0(A, B)) & r1_xboole_0(A, C)) & ~(~(r1_xboole_0(A, B) & r1_xboole_0(A, C)) & r1_xboole_0(A, k2_xboole_0(B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_xboole_1)).
% 22.18/13.76  tff(f_63, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 22.18/13.76  tff(f_69, axiom, (![A, B]: (k4_xboole_0(k2_xboole_0(A, B), B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t40_xboole_1)).
% 22.18/13.76  tff(f_53, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 22.18/13.76  tff(f_77, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 22.18/13.76  tff(f_61, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 22.18/13.76  tff(f_55, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 22.18/13.76  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 22.18/13.76  tff(f_99, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(k2_xboole_0(A, C), k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t9_xboole_1)).
% 22.18/13.76  tff(f_59, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(k4_xboole_0(C, B), k4_xboole_0(C, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t34_xboole_1)).
% 22.18/13.76  tff(f_51, axiom, (![A, B, C]: (k3_xboole_0(A, k2_xboole_0(B, C)) = k2_xboole_0(k3_xboole_0(A, B), k3_xboole_0(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t23_xboole_1)).
% 22.18/13.76  tff(f_93, axiom, (![A, B, C, D]: (((r1_tarski(A, B) & r1_tarski(C, D)) & r1_xboole_0(B, D)) => r1_xboole_0(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_xboole_1)).
% 22.18/13.76  tff(f_73, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_xboole_1)).
% 22.18/13.76  tff(f_83, axiom, (![A, B]: (k2_xboole_0(k3_xboole_0(A, B), k4_xboole_0(A, B)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t51_xboole_1)).
% 22.18/13.76  tff(f_75, axiom, (![A, B]: (k4_xboole_0(A, k3_xboole_0(A, B)) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_xboole_1)).
% 22.18/13.76  tff(f_85, axiom, (![A, B, C]: (k4_xboole_0(A, k4_xboole_0(B, C)) = k2_xboole_0(k4_xboole_0(A, B), k3_xboole_0(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_xboole_1)).
% 22.18/13.76  tff(c_27147, plain, (![A_623, B_624]: (r1_xboole_0(A_623, B_624) | k3_xboole_0(A_623, B_624)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 22.18/13.76  tff(c_8, plain, (![B_6, A_5]: (r1_xboole_0(B_6, A_5) | ~r1_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 22.18/13.76  tff(c_27234, plain, (![B_630, A_631]: (r1_xboole_0(B_630, A_631) | k3_xboole_0(A_631, B_630)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_27147, c_8])).
% 22.18/13.76  tff(c_204, plain, (![A_67, B_68]: (r1_xboole_0(A_67, B_68) | k3_xboole_0(A_67, B_68)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 22.18/13.76  tff(c_58, plain, (~r1_xboole_0('#skF_2', '#skF_4') | ~r1_xboole_0('#skF_2', '#skF_3') | r1_xboole_0('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_116])).
% 22.18/13.76  tff(c_150, plain, (~r1_xboole_0('#skF_2', '#skF_3')), inference(splitLeft, [status(thm)], [c_58])).
% 22.18/13.76  tff(c_210, plain, (k3_xboole_0('#skF_2', '#skF_3')!=k1_xboole_0), inference(resolution, [status(thm)], [c_204, c_150])).
% 22.18/13.76  tff(c_24, plain, (![A_22]: (k4_xboole_0(A_22, k1_xboole_0)=A_22)), inference(cnfTransformation, [status(thm)], [f_63])).
% 22.18/13.76  tff(c_265, plain, (![A_78, B_79]: (k4_xboole_0(k2_xboole_0(A_78, B_79), B_79)=k4_xboole_0(A_78, B_79))), inference(cnfTransformation, [status(thm)], [f_69])).
% 22.18/13.76  tff(c_272, plain, (![A_78]: (k4_xboole_0(A_78, k1_xboole_0)=k2_xboole_0(A_78, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_265, c_24])).
% 22.18/13.76  tff(c_287, plain, (![A_78]: (k2_xboole_0(A_78, k1_xboole_0)=A_78)), inference(demodulation, [status(thm), theory('equality')], [c_24, c_272])).
% 22.18/13.76  tff(c_16, plain, (![A_15]: (k3_xboole_0(A_15, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_53])).
% 22.18/13.76  tff(c_290, plain, (![A_80, B_81]: (k4_xboole_0(A_80, k4_xboole_0(A_80, B_81))=k3_xboole_0(A_80, B_81))), inference(cnfTransformation, [status(thm)], [f_77])).
% 22.18/13.76  tff(c_325, plain, (![A_22]: (k4_xboole_0(A_22, A_22)=k3_xboole_0(A_22, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_24, c_290])).
% 22.18/13.76  tff(c_333, plain, (![A_22]: (k4_xboole_0(A_22, A_22)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_325])).
% 22.18/13.76  tff(c_20466, plain, (![A_465, B_466]: (k2_xboole_0(A_465, k4_xboole_0(B_466, A_465))=k2_xboole_0(A_465, B_466))), inference(cnfTransformation, [status(thm)], [f_61])).
% 22.18/13.76  tff(c_20513, plain, (![A_22]: (k2_xboole_0(A_22, k1_xboole_0)=k2_xboole_0(A_22, A_22))), inference(superposition, [status(thm), theory('equality')], [c_333, c_20466])).
% 22.18/13.76  tff(c_20543, plain, (![A_22]: (k2_xboole_0(A_22, A_22)=A_22)), inference(demodulation, [status(thm), theory('equality')], [c_287, c_20513])).
% 22.18/13.76  tff(c_18, plain, (![A_16]: (r1_tarski(k1_xboole_0, A_16))), inference(cnfTransformation, [status(thm)], [f_55])).
% 22.18/13.76  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 22.18/13.76  tff(c_334, plain, (![A_82]: (k2_xboole_0(A_82, k1_xboole_0)=A_82)), inference(demodulation, [status(thm), theory('equality')], [c_24, c_272])).
% 22.18/13.76  tff(c_363, plain, (![B_2]: (k2_xboole_0(k1_xboole_0, B_2)=B_2)), inference(superposition, [status(thm), theory('equality')], [c_2, c_334])).
% 22.18/13.76  tff(c_21347, plain, (![A_486, C_487, B_488]: (r1_tarski(k2_xboole_0(A_486, C_487), k2_xboole_0(B_488, C_487)) | ~r1_tarski(A_486, B_488))), inference(cnfTransformation, [status(thm)], [f_99])).
% 22.18/13.76  tff(c_21386, plain, (![B_2, B_488]: (r1_tarski(B_2, k2_xboole_0(B_488, B_2)) | ~r1_tarski(k1_xboole_0, B_488))), inference(superposition, [status(thm), theory('equality')], [c_363, c_21347])).
% 22.18/13.76  tff(c_21412, plain, (![B_489, B_490]: (r1_tarski(B_489, k2_xboole_0(B_490, B_489)))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_21386])).
% 22.18/13.76  tff(c_21427, plain, (![A_22]: (r1_tarski(A_22, A_22))), inference(superposition, [status(thm), theory('equality')], [c_20543, c_21412])).
% 22.18/13.76  tff(c_21409, plain, (![B_2, B_488]: (r1_tarski(B_2, k2_xboole_0(B_488, B_2)))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_21386])).
% 22.18/13.76  tff(c_15150, plain, (![C_364, B_365, A_366]: (r1_tarski(k4_xboole_0(C_364, B_365), k4_xboole_0(C_364, A_366)) | ~r1_tarski(A_366, B_365))), inference(cnfTransformation, [status(thm)], [f_59])).
% 22.18/13.76  tff(c_15246, plain, (![A_22, B_365]: (r1_tarski(k4_xboole_0(A_22, B_365), A_22) | ~r1_tarski(k1_xboole_0, B_365))), inference(superposition, [status(thm), theory('equality')], [c_24, c_15150])).
% 22.18/13.76  tff(c_15256, plain, (![A_367, B_368]: (r1_tarski(k4_xboole_0(A_367, B_368), A_367))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_15246])).
% 22.18/13.76  tff(c_15308, plain, (![A_22]: (r1_tarski(A_22, A_22))), inference(superposition, [status(thm), theory('equality')], [c_24, c_15256])).
% 22.18/13.76  tff(c_15798, plain, (![A_380, C_381, B_382]: (r1_tarski(k2_xboole_0(A_380, C_381), k2_xboole_0(B_382, C_381)) | ~r1_tarski(A_380, B_382))), inference(cnfTransformation, [status(thm)], [f_99])).
% 22.18/13.76  tff(c_15837, plain, (![B_2, B_382]: (r1_tarski(B_2, k2_xboole_0(B_382, B_2)) | ~r1_tarski(k1_xboole_0, B_382))), inference(superposition, [status(thm), theory('equality')], [c_363, c_15798])).
% 22.18/13.76  tff(c_15862, plain, (![B_2, B_382]: (r1_tarski(B_2, k2_xboole_0(B_382, B_2)))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_15837])).
% 22.18/13.76  tff(c_52, plain, (r1_xboole_0('#skF_2', k2_xboole_0('#skF_3', '#skF_4')) | r1_xboole_0('#skF_5', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_116])).
% 22.18/13.76  tff(c_64, plain, (r1_xboole_0('#skF_2', k2_xboole_0('#skF_4', '#skF_3')) | r1_xboole_0('#skF_5', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_52])).
% 22.18/13.76  tff(c_476, plain, (r1_xboole_0('#skF_5', '#skF_7')), inference(splitLeft, [status(thm)], [c_64])).
% 22.18/13.76  tff(c_4, plain, (![A_3, B_4]: (k3_xboole_0(A_3, B_4)=k1_xboole_0 | ~r1_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 22.18/13.76  tff(c_482, plain, (k3_xboole_0('#skF_5', '#skF_7')=k1_xboole_0), inference(resolution, [status(thm)], [c_476, c_4])).
% 22.18/13.76  tff(c_56, plain, (r1_xboole_0('#skF_2', k2_xboole_0('#skF_3', '#skF_4')) | r1_xboole_0('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_116])).
% 22.18/13.76  tff(c_63, plain, (r1_xboole_0('#skF_2', k2_xboole_0('#skF_4', '#skF_3')) | r1_xboole_0('#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_56])).
% 22.18/13.76  tff(c_451, plain, (r1_xboole_0('#skF_5', '#skF_6')), inference(splitLeft, [status(thm)], [c_63])).
% 22.18/13.76  tff(c_457, plain, (k3_xboole_0('#skF_5', '#skF_6')=k1_xboole_0), inference(resolution, [status(thm)], [c_451, c_4])).
% 22.18/13.76  tff(c_2847, plain, (![A_154, B_155, C_156]: (k2_xboole_0(k3_xboole_0(A_154, B_155), k3_xboole_0(A_154, C_156))=k3_xboole_0(A_154, k2_xboole_0(B_155, C_156)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 22.18/13.76  tff(c_2948, plain, (![C_156]: (k3_xboole_0('#skF_5', k2_xboole_0('#skF_6', C_156))=k2_xboole_0(k1_xboole_0, k3_xboole_0('#skF_5', C_156)))), inference(superposition, [status(thm), theory('equality')], [c_457, c_2847])).
% 22.18/13.76  tff(c_2989, plain, (![C_156]: (k3_xboole_0('#skF_5', k2_xboole_0('#skF_6', C_156))=k3_xboole_0('#skF_5', C_156))), inference(demodulation, [status(thm), theory('equality')], [c_363, c_2948])).
% 22.18/13.76  tff(c_6, plain, (![A_3, B_4]: (r1_xboole_0(A_3, B_4) | k3_xboole_0(A_3, B_4)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 22.18/13.76  tff(c_60, plain, (r1_xboole_0('#skF_2', k2_xboole_0('#skF_3', '#skF_4')) | ~r1_xboole_0('#skF_5', k2_xboole_0('#skF_6', '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_116])).
% 22.18/13.76  tff(c_65, plain, (r1_xboole_0('#skF_2', k2_xboole_0('#skF_4', '#skF_3')) | ~r1_xboole_0('#skF_5', k2_xboole_0('#skF_6', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_60])).
% 22.18/13.76  tff(c_618, plain, (~r1_xboole_0('#skF_5', k2_xboole_0('#skF_6', '#skF_7'))), inference(splitLeft, [status(thm)], [c_65])).
% 22.18/13.76  tff(c_642, plain, (k3_xboole_0('#skF_5', k2_xboole_0('#skF_6', '#skF_7'))!=k1_xboole_0), inference(resolution, [status(thm)], [c_6, c_618])).
% 22.18/13.76  tff(c_14382, plain, (k3_xboole_0('#skF_5', '#skF_7')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_2989, c_642])).
% 22.18/13.76  tff(c_14385, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_482, c_14382])).
% 22.18/13.76  tff(c_14386, plain, (r1_xboole_0('#skF_2', k2_xboole_0('#skF_4', '#skF_3'))), inference(splitRight, [status(thm)], [c_65])).
% 22.18/13.76  tff(c_18820, plain, (![A_431, C_432, B_433, D_434]: (r1_xboole_0(A_431, C_432) | ~r1_xboole_0(B_433, D_434) | ~r1_tarski(C_432, D_434) | ~r1_tarski(A_431, B_433))), inference(cnfTransformation, [status(thm)], [f_93])).
% 22.18/13.76  tff(c_20124, plain, (![A_451, C_452]: (r1_xboole_0(A_451, C_452) | ~r1_tarski(C_452, k2_xboole_0('#skF_4', '#skF_3')) | ~r1_tarski(A_451, '#skF_2'))), inference(resolution, [status(thm)], [c_14386, c_18820])).
% 22.18/13.76  tff(c_20162, plain, (![A_453]: (r1_xboole_0(A_453, '#skF_3') | ~r1_tarski(A_453, '#skF_2'))), inference(resolution, [status(thm)], [c_15862, c_20124])).
% 22.18/13.76  tff(c_20173, plain, (~r1_tarski('#skF_2', '#skF_2')), inference(resolution, [status(thm)], [c_20162, c_150])).
% 22.18/13.76  tff(c_20182, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_15308, c_20173])).
% 22.18/13.76  tff(c_20183, plain, (r1_xboole_0('#skF_2', k2_xboole_0('#skF_4', '#skF_3'))), inference(splitRight, [status(thm)], [c_64])).
% 22.18/13.76  tff(c_23797, plain, (![A_536, C_537, B_538, D_539]: (r1_xboole_0(A_536, C_537) | ~r1_xboole_0(B_538, D_539) | ~r1_tarski(C_537, D_539) | ~r1_tarski(A_536, B_538))), inference(cnfTransformation, [status(thm)], [f_93])).
% 22.18/13.76  tff(c_24404, plain, (![A_550, C_551]: (r1_xboole_0(A_550, C_551) | ~r1_tarski(C_551, k2_xboole_0('#skF_4', '#skF_3')) | ~r1_tarski(A_550, '#skF_2'))), inference(resolution, [status(thm)], [c_20183, c_23797])).
% 22.18/13.76  tff(c_24683, plain, (![A_554]: (r1_xboole_0(A_554, '#skF_3') | ~r1_tarski(A_554, '#skF_2'))), inference(resolution, [status(thm)], [c_21409, c_24404])).
% 22.18/13.76  tff(c_24694, plain, (~r1_tarski('#skF_2', '#skF_2')), inference(resolution, [status(thm)], [c_24683, c_150])).
% 22.18/13.76  tff(c_24703, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_21427, c_24694])).
% 22.18/13.76  tff(c_24704, plain, (r1_xboole_0('#skF_2', k2_xboole_0('#skF_4', '#skF_3'))), inference(splitRight, [status(thm)], [c_63])).
% 22.18/13.76  tff(c_24719, plain, (k3_xboole_0('#skF_2', k2_xboole_0('#skF_4', '#skF_3'))=k1_xboole_0), inference(resolution, [status(thm)], [c_24704, c_4])).
% 22.18/13.76  tff(c_22, plain, (![A_20, B_21]: (k2_xboole_0(A_20, k4_xboole_0(B_21, A_20))=k2_xboole_0(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_61])).
% 22.18/13.76  tff(c_28, plain, (![A_24, B_25]: (k4_xboole_0(k2_xboole_0(A_24, B_25), B_25)=k4_xboole_0(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_69])).
% 22.18/13.76  tff(c_24857, plain, (![A_560, B_561]: (k2_xboole_0(A_560, k4_xboole_0(B_561, A_560))=k2_xboole_0(A_560, B_561))), inference(cnfTransformation, [status(thm)], [f_61])).
% 22.18/13.76  tff(c_24895, plain, (![B_25, A_24]: (k2_xboole_0(B_25, k4_xboole_0(A_24, B_25))=k2_xboole_0(B_25, k2_xboole_0(A_24, B_25)))), inference(superposition, [status(thm), theory('equality')], [c_28, c_24857])).
% 22.18/13.76  tff(c_24916, plain, (![B_25, A_24]: (k2_xboole_0(B_25, k2_xboole_0(A_24, B_25))=k2_xboole_0(B_25, A_24))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_24895])).
% 22.18/13.76  tff(c_26474, plain, (![A_610, B_611, C_612]: (k2_xboole_0(k3_xboole_0(A_610, B_611), k3_xboole_0(A_610, C_612))=k3_xboole_0(A_610, k2_xboole_0(B_611, C_612)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 22.18/13.76  tff(c_26560, plain, (![B_611]: (k3_xboole_0('#skF_2', k2_xboole_0(B_611, k2_xboole_0('#skF_4', '#skF_3')))=k2_xboole_0(k3_xboole_0('#skF_2', B_611), k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_24719, c_26474])).
% 22.18/13.76  tff(c_27019, plain, (![B_620]: (k3_xboole_0('#skF_2', k2_xboole_0(B_620, k2_xboole_0('#skF_4', '#skF_3')))=k3_xboole_0('#skF_2', B_620))), inference(demodulation, [status(thm), theory('equality')], [c_287, c_26560])).
% 22.18/13.76  tff(c_27075, plain, (k3_xboole_0('#skF_2', k2_xboole_0('#skF_3', '#skF_4'))=k3_xboole_0('#skF_2', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_24916, c_27019])).
% 22.18/13.76  tff(c_27113, plain, (k3_xboole_0('#skF_2', '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_24719, c_2, c_27075])).
% 22.18/13.76  tff(c_27115, plain, $false, inference(negUnitSimplification, [status(thm)], [c_210, c_27113])).
% 22.18/13.76  tff(c_27116, plain, (~r1_xboole_0('#skF_2', '#skF_4') | r1_xboole_0('#skF_5', '#skF_6')), inference(splitRight, [status(thm)], [c_58])).
% 22.18/13.76  tff(c_27125, plain, (~r1_xboole_0('#skF_2', '#skF_4')), inference(splitLeft, [status(thm)], [c_27116])).
% 22.18/13.76  tff(c_27244, plain, (k3_xboole_0('#skF_4', '#skF_2')!=k1_xboole_0), inference(resolution, [status(thm)], [c_27234, c_27125])).
% 22.18/13.76  tff(c_32, plain, (![A_29, B_30]: (k4_xboole_0(A_29, k2_xboole_0(A_29, B_30))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_73])).
% 22.18/13.76  tff(c_94749, plain, (![C_1565, B_1566, A_1567]: (r1_tarski(k4_xboole_0(C_1565, B_1566), k4_xboole_0(C_1565, A_1567)) | ~r1_tarski(A_1567, B_1566))), inference(cnfTransformation, [status(thm)], [f_59])).
% 22.18/13.76  tff(c_94851, plain, (![A_22, B_1566]: (r1_tarski(k4_xboole_0(A_22, B_1566), A_22) | ~r1_tarski(k1_xboole_0, B_1566))), inference(superposition, [status(thm), theory('equality')], [c_24, c_94749])).
% 22.18/13.76  tff(c_94862, plain, (![A_1568, B_1569]: (r1_tarski(k4_xboole_0(A_1568, B_1569), A_1568))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_94851])).
% 22.18/13.76  tff(c_94917, plain, (![A_22]: (r1_tarski(A_22, A_22))), inference(superposition, [status(thm), theory('equality')], [c_24, c_94862])).
% 22.18/13.76  tff(c_27278, plain, (![A_634, B_635]: (k2_xboole_0(k3_xboole_0(A_634, B_635), k4_xboole_0(A_634, B_635))=A_634)), inference(cnfTransformation, [status(thm)], [f_83])).
% 22.18/13.76  tff(c_27308, plain, (![A_15]: (k2_xboole_0(k1_xboole_0, k4_xboole_0(A_15, k1_xboole_0))=A_15)), inference(superposition, [status(thm), theory('equality')], [c_16, c_27278])).
% 22.18/13.76  tff(c_27318, plain, (![A_15]: (k2_xboole_0(k1_xboole_0, A_15)=A_15)), inference(demodulation, [status(thm), theory('equality')], [c_24, c_27308])).
% 22.18/13.76  tff(c_95039, plain, (![A_1574, C_1575, B_1576]: (r1_tarski(k2_xboole_0(A_1574, C_1575), k2_xboole_0(B_1576, C_1575)) | ~r1_tarski(A_1574, B_1576))), inference(cnfTransformation, [status(thm)], [f_99])).
% 22.18/13.76  tff(c_95084, plain, (![A_15, B_1576]: (r1_tarski(A_15, k2_xboole_0(B_1576, A_15)) | ~r1_tarski(k1_xboole_0, B_1576))), inference(superposition, [status(thm), theory('equality')], [c_27318, c_95039])).
% 22.18/13.76  tff(c_95118, plain, (![A_1577, B_1578]: (r1_tarski(A_1577, k2_xboole_0(B_1578, A_1577)))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_95084])).
% 22.18/13.76  tff(c_95151, plain, (![B_2, A_1]: (r1_tarski(B_2, k2_xboole_0(B_2, A_1)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_95118])).
% 22.18/13.76  tff(c_85824, plain, (![C_1385, B_1386, A_1387]: (r1_tarski(k4_xboole_0(C_1385, B_1386), k4_xboole_0(C_1385, A_1387)) | ~r1_tarski(A_1387, B_1386))), inference(cnfTransformation, [status(thm)], [f_59])).
% 22.18/13.76  tff(c_85938, plain, (![A_22, B_1386]: (r1_tarski(k4_xboole_0(A_22, B_1386), A_22) | ~r1_tarski(k1_xboole_0, B_1386))), inference(superposition, [status(thm), theory('equality')], [c_24, c_85824])).
% 22.18/13.76  tff(c_85948, plain, (![A_1388, B_1389]: (r1_tarski(k4_xboole_0(A_1388, B_1389), A_1388))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_85938])).
% 22.18/13.76  tff(c_86009, plain, (![A_22]: (r1_tarski(A_22, A_22))), inference(superposition, [status(thm), theory('equality')], [c_24, c_85948])).
% 22.18/13.76  tff(c_86033, plain, (![A_1391, C_1392, B_1393]: (r1_tarski(k2_xboole_0(A_1391, C_1392), k2_xboole_0(B_1393, C_1392)) | ~r1_tarski(A_1391, B_1393))), inference(cnfTransformation, [status(thm)], [f_99])).
% 22.18/13.76  tff(c_86066, plain, (![A_15, B_1393]: (r1_tarski(A_15, k2_xboole_0(B_1393, A_15)) | ~r1_tarski(k1_xboole_0, B_1393))), inference(superposition, [status(thm), theory('equality')], [c_27318, c_86033])).
% 22.18/13.76  tff(c_86170, plain, (![A_1396, B_1397]: (r1_tarski(A_1396, k2_xboole_0(B_1397, A_1396)))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_86066])).
% 22.18/13.76  tff(c_86197, plain, (![B_2, A_1]: (r1_tarski(B_2, k2_xboole_0(B_2, A_1)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_86170])).
% 22.18/13.76  tff(c_27442, plain, (r1_xboole_0('#skF_5', '#skF_7')), inference(splitLeft, [status(thm)], [c_64])).
% 22.18/13.76  tff(c_27448, plain, (k3_xboole_0('#skF_5', '#skF_7')=k1_xboole_0), inference(resolution, [status(thm)], [c_27442, c_4])).
% 22.18/13.76  tff(c_27465, plain, (r1_xboole_0('#skF_5', '#skF_6')), inference(splitLeft, [status(thm)], [c_63])).
% 22.18/13.76  tff(c_27471, plain, (k3_xboole_0('#skF_5', '#skF_6')=k1_xboole_0), inference(resolution, [status(thm)], [c_27465, c_4])).
% 22.18/13.76  tff(c_30939, plain, (![A_723, B_724, C_725]: (k2_xboole_0(k3_xboole_0(A_723, B_724), k3_xboole_0(A_723, C_725))=k3_xboole_0(A_723, k2_xboole_0(B_724, C_725)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 22.18/13.76  tff(c_46430, plain, (![A_936, C_937, B_938]: (k2_xboole_0(k3_xboole_0(A_936, C_937), k3_xboole_0(A_936, B_938))=k3_xboole_0(A_936, k2_xboole_0(B_938, C_937)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_30939])).
% 22.18/13.76  tff(c_46794, plain, (![C_937]: (k3_xboole_0('#skF_5', k2_xboole_0('#skF_6', C_937))=k2_xboole_0(k3_xboole_0('#skF_5', C_937), k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_27471, c_46430])).
% 22.18/13.76  tff(c_46927, plain, (![C_937]: (k3_xboole_0('#skF_5', k2_xboole_0('#skF_6', C_937))=k3_xboole_0('#skF_5', C_937))), inference(demodulation, [status(thm), theory('equality')], [c_27318, c_2, c_46794])).
% 22.18/13.76  tff(c_27522, plain, (~r1_xboole_0('#skF_5', k2_xboole_0('#skF_6', '#skF_7'))), inference(splitLeft, [status(thm)], [c_65])).
% 22.18/13.76  tff(c_27554, plain, (k3_xboole_0('#skF_5', k2_xboole_0('#skF_6', '#skF_7'))!=k1_xboole_0), inference(resolution, [status(thm)], [c_6, c_27522])).
% 22.18/13.76  tff(c_84275, plain, (k3_xboole_0('#skF_5', '#skF_7')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_46927, c_27554])).
% 22.18/13.76  tff(c_84278, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_27448, c_84275])).
% 22.18/13.76  tff(c_84279, plain, (r1_xboole_0('#skF_2', k2_xboole_0('#skF_4', '#skF_3'))), inference(splitRight, [status(thm)], [c_65])).
% 22.18/13.76  tff(c_86830, plain, (![A_1410, C_1411, B_1412, D_1413]: (r1_xboole_0(A_1410, C_1411) | ~r1_xboole_0(B_1412, D_1413) | ~r1_tarski(C_1411, D_1413) | ~r1_tarski(A_1410, B_1412))), inference(cnfTransformation, [status(thm)], [f_93])).
% 22.18/13.76  tff(c_91531, plain, (![A_1498, C_1499]: (r1_xboole_0(A_1498, C_1499) | ~r1_tarski(C_1499, k2_xboole_0('#skF_4', '#skF_3')) | ~r1_tarski(A_1498, '#skF_2'))), inference(resolution, [status(thm)], [c_84279, c_86830])).
% 22.18/13.76  tff(c_92991, plain, (![A_1520]: (r1_xboole_0(A_1520, '#skF_4') | ~r1_tarski(A_1520, '#skF_2'))), inference(resolution, [status(thm)], [c_86197, c_91531])).
% 22.18/13.76  tff(c_93002, plain, (~r1_tarski('#skF_2', '#skF_2')), inference(resolution, [status(thm)], [c_92991, c_27125])).
% 22.18/13.76  tff(c_93011, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_86009, c_93002])).
% 22.18/13.76  tff(c_93012, plain, (r1_xboole_0('#skF_2', k2_xboole_0('#skF_4', '#skF_3'))), inference(splitRight, [status(thm)], [c_63])).
% 22.18/13.76  tff(c_96040, plain, (![A_1597, C_1598, B_1599, D_1600]: (r1_xboole_0(A_1597, C_1598) | ~r1_xboole_0(B_1599, D_1600) | ~r1_tarski(C_1598, D_1600) | ~r1_tarski(A_1597, B_1599))), inference(cnfTransformation, [status(thm)], [f_93])).
% 22.18/13.76  tff(c_101168, plain, (![A_1688, C_1689]: (r1_xboole_0(A_1688, C_1689) | ~r1_tarski(C_1689, k2_xboole_0('#skF_4', '#skF_3')) | ~r1_tarski(A_1688, '#skF_2'))), inference(resolution, [status(thm)], [c_93012, c_96040])).
% 22.18/13.76  tff(c_102316, plain, (![A_1703]: (r1_xboole_0(A_1703, '#skF_4') | ~r1_tarski(A_1703, '#skF_2'))), inference(resolution, [status(thm)], [c_95151, c_101168])).
% 22.18/13.76  tff(c_102327, plain, (~r1_tarski('#skF_2', '#skF_2')), inference(resolution, [status(thm)], [c_102316, c_27125])).
% 22.18/13.76  tff(c_102336, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_94917, c_102327])).
% 22.18/13.76  tff(c_102337, plain, (r1_xboole_0('#skF_2', k2_xboole_0('#skF_4', '#skF_3'))), inference(splitRight, [status(thm)], [c_64])).
% 22.18/13.76  tff(c_102376, plain, (r1_xboole_0(k2_xboole_0('#skF_4', '#skF_3'), '#skF_2')), inference(resolution, [status(thm)], [c_102337, c_8])).
% 22.18/13.76  tff(c_102431, plain, (k3_xboole_0(k2_xboole_0('#skF_4', '#skF_3'), '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_102376, c_4])).
% 22.18/13.76  tff(c_34, plain, (![A_31, B_32]: (k4_xboole_0(A_31, k3_xboole_0(A_31, B_32))=k4_xboole_0(A_31, B_32))), inference(cnfTransformation, [status(thm)], [f_75])).
% 22.18/13.76  tff(c_102835, plain, (k4_xboole_0(k2_xboole_0('#skF_4', '#skF_3'), k1_xboole_0)=k4_xboole_0(k2_xboole_0('#skF_4', '#skF_3'), '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_102431, c_34])).
% 22.18/13.76  tff(c_102845, plain, (k4_xboole_0(k2_xboole_0('#skF_4', '#skF_3'), '#skF_2')=k2_xboole_0('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_102835])).
% 22.18/13.76  tff(c_105295, plain, (![A_1786, B_1787, C_1788]: (k2_xboole_0(k4_xboole_0(A_1786, B_1787), k3_xboole_0(A_1786, C_1788))=k4_xboole_0(A_1786, k4_xboole_0(B_1787, C_1788)))), inference(cnfTransformation, [status(thm)], [f_85])).
% 22.18/13.76  tff(c_105451, plain, (![A_29, B_30, C_1788]: (k4_xboole_0(A_29, k4_xboole_0(k2_xboole_0(A_29, B_30), C_1788))=k2_xboole_0(k1_xboole_0, k3_xboole_0(A_29, C_1788)))), inference(superposition, [status(thm), theory('equality')], [c_32, c_105295])).
% 22.18/13.76  tff(c_108010, plain, (![A_1839, B_1840, C_1841]: (k4_xboole_0(A_1839, k4_xboole_0(k2_xboole_0(A_1839, B_1840), C_1841))=k3_xboole_0(A_1839, C_1841))), inference(demodulation, [status(thm), theory('equality')], [c_27318, c_105451])).
% 22.18/13.76  tff(c_108159, plain, (k4_xboole_0('#skF_4', k2_xboole_0('#skF_4', '#skF_3'))=k3_xboole_0('#skF_4', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_102845, c_108010])).
% 22.18/13.76  tff(c_108245, plain, (k3_xboole_0('#skF_4', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_32, c_108159])).
% 22.18/13.76  tff(c_108247, plain, $false, inference(negUnitSimplification, [status(thm)], [c_27244, c_108245])).
% 22.18/13.76  tff(c_108248, plain, (r1_xboole_0('#skF_5', '#skF_6')), inference(splitRight, [status(thm)], [c_27116])).
% 22.18/13.76  tff(c_108330, plain, (![A_1848, B_1849]: (k3_xboole_0(A_1848, B_1849)=k1_xboole_0 | ~r1_xboole_0(A_1848, B_1849))), inference(cnfTransformation, [status(thm)], [f_31])).
% 22.18/13.76  tff(c_108370, plain, (k3_xboole_0('#skF_5', '#skF_6')=k1_xboole_0), inference(resolution, [status(thm)], [c_108248, c_108330])).
% 22.18/13.76  tff(c_108805, plain, (![A_1865, B_1866]: (k2_xboole_0(k3_xboole_0(A_1865, B_1866), k4_xboole_0(A_1865, B_1866))=A_1865)), inference(cnfTransformation, [status(thm)], [f_83])).
% 22.18/13.76  tff(c_108889, plain, (![A_15]: (k2_xboole_0(k1_xboole_0, k4_xboole_0(A_15, k1_xboole_0))=A_15)), inference(superposition, [status(thm), theory('equality')], [c_16, c_108805])).
% 22.18/13.76  tff(c_108917, plain, (![A_15]: (k2_xboole_0(k1_xboole_0, A_15)=A_15)), inference(demodulation, [status(thm), theory('equality')], [c_24, c_108889])).
% 22.18/13.76  tff(c_27117, plain, (r1_xboole_0('#skF_2', '#skF_3')), inference(splitRight, [status(thm)], [c_58])).
% 22.18/13.76  tff(c_108249, plain, (r1_xboole_0('#skF_2', '#skF_4')), inference(splitRight, [status(thm)], [c_27116])).
% 22.18/13.76  tff(c_54, plain, (~r1_xboole_0('#skF_2', '#skF_4') | ~r1_xboole_0('#skF_2', '#skF_3') | r1_xboole_0('#skF_5', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_116])).
% 22.18/13.76  tff(c_108261, plain, (r1_xboole_0('#skF_5', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_27117, c_108249, c_54])).
% 22.18/13.76  tff(c_108367, plain, (k3_xboole_0('#skF_5', '#skF_7')=k1_xboole_0), inference(resolution, [status(thm)], [c_108261, c_108330])).
% 22.18/13.76  tff(c_109828, plain, (![A_1896, B_1897, C_1898]: (k2_xboole_0(k3_xboole_0(A_1896, B_1897), k3_xboole_0(A_1896, C_1898))=k3_xboole_0(A_1896, k2_xboole_0(B_1897, C_1898)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 22.18/13.76  tff(c_109930, plain, (![B_1897]: (k3_xboole_0('#skF_5', k2_xboole_0(B_1897, '#skF_7'))=k2_xboole_0(k3_xboole_0('#skF_5', B_1897), k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_108367, c_109828])).
% 22.18/13.76  tff(c_109965, plain, (![B_1897]: (k3_xboole_0('#skF_5', k2_xboole_0(B_1897, '#skF_7'))=k3_xboole_0('#skF_5', B_1897))), inference(demodulation, [status(thm), theory('equality')], [c_108917, c_2, c_109930])).
% 22.18/13.76  tff(c_62, plain, (~r1_xboole_0('#skF_2', '#skF_4') | ~r1_xboole_0('#skF_2', '#skF_3') | ~r1_xboole_0('#skF_5', k2_xboole_0('#skF_6', '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_116])).
% 22.18/13.76  tff(c_108385, plain, (~r1_xboole_0('#skF_5', k2_xboole_0('#skF_6', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_27117, c_108249, c_62])).
% 22.18/13.76  tff(c_108389, plain, (k3_xboole_0('#skF_5', k2_xboole_0('#skF_6', '#skF_7'))!=k1_xboole_0), inference(resolution, [status(thm)], [c_6, c_108385])).
% 22.18/13.76  tff(c_124470, plain, (k3_xboole_0('#skF_5', '#skF_6')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_109965, c_108389])).
% 22.18/13.76  tff(c_124473, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_108370, c_124470])).
% 22.18/13.76  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 22.18/13.76  
% 22.18/13.76  Inference rules
% 22.18/13.76  ----------------------
% 22.18/13.76  #Ref     : 0
% 22.18/13.76  #Sup     : 31700
% 22.18/13.76  #Fact    : 0
% 22.18/13.76  #Define  : 0
% 22.18/13.76  #Split   : 40
% 22.18/13.76  #Chain   : 0
% 22.18/13.76  #Close   : 0
% 22.18/13.76  
% 22.18/13.76  Ordering : KBO
% 22.18/13.76  
% 22.18/13.76  Simplification rules
% 22.18/13.76  ----------------------
% 22.18/13.76  #Subsume      : 974
% 22.18/13.76  #Demod        : 28498
% 22.18/13.76  #Tautology    : 19867
% 22.18/13.76  #SimpNegUnit  : 234
% 22.18/13.76  #BackRed      : 17
% 22.18/13.76  
% 22.18/13.76  #Partial instantiations: 0
% 22.18/13.76  #Strategies tried      : 1
% 22.18/13.76  
% 22.18/13.76  Timing (in seconds)
% 22.18/13.76  ----------------------
% 22.18/13.76  Preprocessing        : 0.32
% 22.18/13.76  Parsing              : 0.18
% 22.18/13.76  CNF conversion       : 0.02
% 22.18/13.76  Main loop            : 12.66
% 22.18/13.76  Inferencing          : 1.85
% 22.18/13.76  Reduction            : 7.07
% 22.18/13.76  Demodulation         : 6.06
% 22.18/13.76  BG Simplification    : 0.22
% 22.18/13.76  Subsumption          : 2.86
% 22.18/13.76  Abstraction          : 0.33
% 22.18/13.76  MUC search           : 0.00
% 22.18/13.76  Cooper               : 0.00
% 22.18/13.76  Total                : 13.03
% 22.18/13.76  Index Insertion      : 0.00
% 22.18/13.76  Index Deletion       : 0.00
% 22.18/13.76  Index Matching       : 0.00
% 22.18/13.76  BG Taut test         : 0.00
%------------------------------------------------------------------------------

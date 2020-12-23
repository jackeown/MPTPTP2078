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
% DateTime   : Thu Dec  3 09:52:34 EST 2020

% Result     : Theorem 7.51s
% Output     : CNFRefutation 7.51s
% Verified   : 
% Statistics : Number of formulae       :  106 ( 195 expanded)
%              Number of leaves         :   37 (  77 expanded)
%              Depth                    :   11
%              Number of atoms          :  100 ( 228 expanded)
%              Number of equality atoms :   66 ( 153 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_47,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_33,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_91,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
    <=> A != B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).

tff(f_97,negated_conjecture,(
    ~ ! [A,B] :
        ( k4_xboole_0(A,k1_tarski(B)) = A
      <=> ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).

tff(f_49,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_xboole_1)).

tff(f_45,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_43,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_84,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),B) = k1_tarski(A)
    <=> ~ r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l33_zfmisc_1)).

tff(f_51,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_86,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_71,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k4_xboole_0(B,A))
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_xboole_1)).

tff(c_20,plain,(
    ! [A_19] : k5_xboole_0(A_19,A_19) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_6,plain,(
    ! [A_5] : k3_xboole_0(A_5,A_5) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_12710,plain,(
    ! [A_342,B_343] : k5_xboole_0(A_342,k3_xboole_0(A_342,B_343)) = k4_xboole_0(A_342,B_343) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_12727,plain,(
    ! [A_5] : k5_xboole_0(A_5,A_5) = k4_xboole_0(A_5,A_5) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_12710])).

tff(c_12730,plain,(
    ! [A_5] : k4_xboole_0(A_5,A_5) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_12727])).

tff(c_12334,plain,(
    ! [A_312,B_313] : k5_xboole_0(A_312,k3_xboole_0(A_312,B_313)) = k4_xboole_0(A_312,B_313) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_12351,plain,(
    ! [A_5] : k5_xboole_0(A_5,A_5) = k4_xboole_0(A_5,A_5) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_12334])).

tff(c_12354,plain,(
    ! [A_5] : k4_xboole_0(A_5,A_5) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_12351])).

tff(c_56,plain,(
    ! [B_71] : k4_xboole_0(k1_tarski(B_71),k1_tarski(B_71)) != k1_tarski(B_71) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_12355,plain,(
    ! [B_71] : k1_tarski(B_71) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12354,c_56])).

tff(c_62,plain,
    ( ~ r2_hidden('#skF_2','#skF_1')
    | r2_hidden('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_120,plain,(
    ~ r2_hidden('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_62])).

tff(c_8,plain,(
    ! [A_7,B_8] : k5_xboole_0(A_7,k3_xboole_0(A_7,B_8)) = k4_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_1120,plain,(
    ! [A_149,B_150] : k5_xboole_0(k5_xboole_0(A_149,B_150),k2_xboole_0(A_149,B_150)) = k3_xboole_0(A_149,B_150) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_18,plain,(
    ! [A_16,B_17,C_18] : k5_xboole_0(k5_xboole_0(A_16,B_17),C_18) = k5_xboole_0(A_16,k5_xboole_0(B_17,C_18)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_8516,plain,(
    ! [A_262,B_263] : k5_xboole_0(A_262,k5_xboole_0(B_263,k2_xboole_0(A_262,B_263))) = k3_xboole_0(A_262,B_263) ),
    inference(superposition,[status(thm),theory(equality)],[c_1120,c_18])).

tff(c_134,plain,(
    ! [B_79,A_80] : k5_xboole_0(B_79,A_80) = k5_xboole_0(A_80,B_79) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_16,plain,(
    ! [A_15] : k5_xboole_0(A_15,k1_xboole_0) = A_15 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_150,plain,(
    ! [A_80] : k5_xboole_0(k1_xboole_0,A_80) = A_80 ),
    inference(superposition,[status(thm),theory(equality)],[c_134,c_16])).

tff(c_801,plain,(
    ! [A_140,B_141,C_142] : k5_xboole_0(k5_xboole_0(A_140,B_141),C_142) = k5_xboole_0(A_140,k5_xboole_0(B_141,C_142)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_865,plain,(
    ! [A_19,C_142] : k5_xboole_0(A_19,k5_xboole_0(A_19,C_142)) = k5_xboole_0(k1_xboole_0,C_142) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_801])).

tff(c_878,plain,(
    ! [A_19,C_142] : k5_xboole_0(A_19,k5_xboole_0(A_19,C_142)) = C_142 ),
    inference(demodulation,[status(thm),theory(equality)],[c_150,c_865])).

tff(c_8572,plain,(
    ! [B_263,A_262] : k5_xboole_0(B_263,k2_xboole_0(A_262,B_263)) = k5_xboole_0(A_262,k3_xboole_0(A_262,B_263)) ),
    inference(superposition,[status(thm),theory(equality)],[c_8516,c_878])).

tff(c_8690,plain,(
    ! [B_263,A_262] : k5_xboole_0(B_263,k2_xboole_0(A_262,B_263)) = k4_xboole_0(A_262,B_263) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_8572])).

tff(c_2,plain,(
    ! [B_2,A_1] : k5_xboole_0(B_2,A_1) = k5_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_52,plain,(
    ! [A_66,B_67] :
      ( k4_xboole_0(k1_tarski(A_66),B_67) = k1_tarski(A_66)
      | r2_hidden(A_66,B_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_24,plain,(
    ! [B_23,A_22] : k2_tarski(B_23,A_22) = k2_tarski(A_22,B_23) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_265,plain,(
    ! [A_86,B_87] : k3_tarski(k2_tarski(A_86,B_87)) = k2_xboole_0(A_86,B_87) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_315,plain,(
    ! [A_96,B_97] : k3_tarski(k2_tarski(A_96,B_97)) = k2_xboole_0(B_97,A_96) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_265])).

tff(c_54,plain,(
    ! [A_68,B_69] : k3_tarski(k2_tarski(A_68,B_69)) = k2_xboole_0(A_68,B_69) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_321,plain,(
    ! [B_97,A_96] : k2_xboole_0(B_97,A_96) = k2_xboole_0(A_96,B_97) ),
    inference(superposition,[status(thm),theory(equality)],[c_315,c_54])).

tff(c_8715,plain,(
    ! [B_264,A_265] : k5_xboole_0(B_264,k2_xboole_0(A_265,B_264)) = k4_xboole_0(A_265,B_264) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_8572])).

tff(c_879,plain,(
    ! [A_143,C_144] : k5_xboole_0(A_143,k5_xboole_0(A_143,C_144)) = C_144 ),
    inference(demodulation,[status(thm),theory(equality)],[c_150,c_865])).

tff(c_922,plain,(
    ! [A_1,B_2] : k5_xboole_0(A_1,k5_xboole_0(B_2,A_1)) = B_2 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_879])).

tff(c_9085,plain,(
    ! [A_268,B_269] : k5_xboole_0(k2_xboole_0(A_268,B_269),k4_xboole_0(A_268,B_269)) = B_269 ),
    inference(superposition,[status(thm),theory(equality)],[c_8715,c_922])).

tff(c_10068,plain,(
    ! [A_279,B_280] : k5_xboole_0(k2_xboole_0(A_279,B_280),k4_xboole_0(B_280,A_279)) = A_279 ),
    inference(superposition,[status(thm),theory(equality)],[c_321,c_9085])).

tff(c_10184,plain,(
    ! [B_67,A_66] :
      ( k5_xboole_0(k2_xboole_0(B_67,k1_tarski(A_66)),k1_tarski(A_66)) = B_67
      | r2_hidden(A_66,B_67) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_10068])).

tff(c_12021,plain,(
    ! [B_299,A_300] :
      ( k4_xboole_0(B_299,k1_tarski(A_300)) = B_299
      | r2_hidden(A_300,B_299) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8690,c_2,c_10184])).

tff(c_60,plain,
    ( k4_xboole_0('#skF_1',k1_tarski('#skF_2')) != '#skF_1'
    | r2_hidden('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_294,plain,(
    k4_xboole_0('#skF_1',k1_tarski('#skF_2')) != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_60])).

tff(c_12109,plain,(
    r2_hidden('#skF_2','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_12021,c_294])).

tff(c_12176,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_120,c_12109])).

tff(c_12177,plain,(
    r2_hidden('#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_44,plain,(
    ! [A_60,B_61] :
      ( r1_tarski(k1_tarski(A_60),B_61)
      | ~ r2_hidden(A_60,B_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_12178,plain,(
    k4_xboole_0('#skF_1',k1_tarski('#skF_2')) = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_64,plain,
    ( k4_xboole_0('#skF_1',k1_tarski('#skF_2')) != '#skF_1'
    | k4_xboole_0('#skF_3',k1_tarski('#skF_4')) = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_12187,plain,(
    k4_xboole_0('#skF_3',k1_tarski('#skF_4')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12178,c_64])).

tff(c_12,plain,(
    ! [A_11,B_12] :
      ( k1_xboole_0 = A_11
      | ~ r1_tarski(A_11,k4_xboole_0(B_12,A_11)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_12191,plain,
    ( k1_tarski('#skF_4') = k1_xboole_0
    | ~ r1_tarski(k1_tarski('#skF_4'),'#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_12187,c_12])).

tff(c_12293,plain,(
    ~ r1_tarski(k1_tarski('#skF_4'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_12191])).

tff(c_12300,plain,(
    ~ r2_hidden('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_12293])).

tff(c_12304,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12177,c_12300])).

tff(c_12305,plain,(
    k1_tarski('#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_12191])).

tff(c_12367,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_12355,c_12305])).

tff(c_12368,plain,(
    r2_hidden('#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_12369,plain,(
    r2_hidden('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_66,plain,
    ( ~ r2_hidden('#skF_2','#skF_1')
    | k4_xboole_0('#skF_3',k1_tarski('#skF_4')) = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_12370,plain,(
    ~ r2_hidden('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_66])).

tff(c_12372,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12369,c_12370])).

tff(c_12373,plain,(
    k4_xboole_0('#skF_3',k1_tarski('#skF_4')) = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_12524,plain,(
    ! [A_322,B_323] :
      ( k1_xboole_0 = A_322
      | ~ r1_tarski(A_322,k4_xboole_0(B_323,A_322)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_12527,plain,
    ( k1_tarski('#skF_4') = k1_xboole_0
    | ~ r1_tarski(k1_tarski('#skF_4'),'#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_12373,c_12524])).

tff(c_12578,plain,(
    ~ r1_tarski(k1_tarski('#skF_4'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_12527])).

tff(c_12581,plain,(
    ~ r2_hidden('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_12578])).

tff(c_12585,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12368,c_12581])).

tff(c_12586,plain,(
    k1_tarski('#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_12527])).

tff(c_12598,plain,(
    k4_xboole_0(k1_tarski('#skF_4'),k1_xboole_0) != k1_tarski('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_12586,c_56])).

tff(c_12608,plain,(
    k4_xboole_0(k1_xboole_0,k1_xboole_0) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12586,c_12586,c_12598])).

tff(c_12734,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12730,c_12608])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:26:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.51/2.92  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.51/2.93  
% 7.51/2.93  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.51/2.93  %$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 7.51/2.93  
% 7.51/2.93  %Foreground sorts:
% 7.51/2.93  
% 7.51/2.93  
% 7.51/2.93  %Background operators:
% 7.51/2.93  
% 7.51/2.93  
% 7.51/2.93  %Foreground operators:
% 7.51/2.93  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.51/2.93  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.51/2.93  tff(k1_tarski, type, k1_tarski: $i > $i).
% 7.51/2.93  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 7.51/2.93  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.51/2.93  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 7.51/2.93  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 7.51/2.93  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.51/2.93  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 7.51/2.93  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 7.51/2.93  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 7.51/2.93  tff('#skF_2', type, '#skF_2': $i).
% 7.51/2.93  tff('#skF_3', type, '#skF_3': $i).
% 7.51/2.93  tff('#skF_1', type, '#skF_1': $i).
% 7.51/2.93  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 7.51/2.93  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 7.51/2.93  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.51/2.93  tff(k3_tarski, type, k3_tarski: $i > $i).
% 7.51/2.93  tff('#skF_4', type, '#skF_4': $i).
% 7.51/2.93  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.51/2.93  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 7.51/2.93  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 7.51/2.93  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 7.51/2.93  
% 7.51/2.95  tff(f_47, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_xboole_1)).
% 7.51/2.95  tff(f_31, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 7.51/2.95  tff(f_33, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 7.51/2.95  tff(f_91, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 7.51/2.95  tff(f_97, negated_conjecture, ~(![A, B]: ((k4_xboole_0(A, k1_tarski(B)) = A) <=> ~r2_hidden(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 7.51/2.95  tff(f_49, axiom, (![A, B]: (k3_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k2_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t95_xboole_1)).
% 7.51/2.95  tff(f_45, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_xboole_1)).
% 7.51/2.95  tff(f_27, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 7.51/2.95  tff(f_43, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 7.51/2.95  tff(f_84, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), B) = k1_tarski(A)) <=> ~r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l33_zfmisc_1)).
% 7.51/2.95  tff(f_51, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 7.51/2.95  tff(f_86, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 7.51/2.95  tff(f_71, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 7.51/2.95  tff(f_39, axiom, (![A, B]: (r1_tarski(A, k4_xboole_0(B, A)) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_xboole_1)).
% 7.51/2.95  tff(c_20, plain, (![A_19]: (k5_xboole_0(A_19, A_19)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_47])).
% 7.51/2.95  tff(c_6, plain, (![A_5]: (k3_xboole_0(A_5, A_5)=A_5)), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.51/2.95  tff(c_12710, plain, (![A_342, B_343]: (k5_xboole_0(A_342, k3_xboole_0(A_342, B_343))=k4_xboole_0(A_342, B_343))), inference(cnfTransformation, [status(thm)], [f_33])).
% 7.51/2.95  tff(c_12727, plain, (![A_5]: (k5_xboole_0(A_5, A_5)=k4_xboole_0(A_5, A_5))), inference(superposition, [status(thm), theory('equality')], [c_6, c_12710])).
% 7.51/2.95  tff(c_12730, plain, (![A_5]: (k4_xboole_0(A_5, A_5)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_20, c_12727])).
% 7.51/2.95  tff(c_12334, plain, (![A_312, B_313]: (k5_xboole_0(A_312, k3_xboole_0(A_312, B_313))=k4_xboole_0(A_312, B_313))), inference(cnfTransformation, [status(thm)], [f_33])).
% 7.51/2.95  tff(c_12351, plain, (![A_5]: (k5_xboole_0(A_5, A_5)=k4_xboole_0(A_5, A_5))), inference(superposition, [status(thm), theory('equality')], [c_6, c_12334])).
% 7.51/2.95  tff(c_12354, plain, (![A_5]: (k4_xboole_0(A_5, A_5)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_20, c_12351])).
% 7.51/2.95  tff(c_56, plain, (![B_71]: (k4_xboole_0(k1_tarski(B_71), k1_tarski(B_71))!=k1_tarski(B_71))), inference(cnfTransformation, [status(thm)], [f_91])).
% 7.51/2.95  tff(c_12355, plain, (![B_71]: (k1_tarski(B_71)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_12354, c_56])).
% 7.51/2.95  tff(c_62, plain, (~r2_hidden('#skF_2', '#skF_1') | r2_hidden('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_97])).
% 7.51/2.95  tff(c_120, plain, (~r2_hidden('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_62])).
% 7.51/2.95  tff(c_8, plain, (![A_7, B_8]: (k5_xboole_0(A_7, k3_xboole_0(A_7, B_8))=k4_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_33])).
% 7.51/2.95  tff(c_1120, plain, (![A_149, B_150]: (k5_xboole_0(k5_xboole_0(A_149, B_150), k2_xboole_0(A_149, B_150))=k3_xboole_0(A_149, B_150))), inference(cnfTransformation, [status(thm)], [f_49])).
% 7.51/2.95  tff(c_18, plain, (![A_16, B_17, C_18]: (k5_xboole_0(k5_xboole_0(A_16, B_17), C_18)=k5_xboole_0(A_16, k5_xboole_0(B_17, C_18)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 7.51/2.95  tff(c_8516, plain, (![A_262, B_263]: (k5_xboole_0(A_262, k5_xboole_0(B_263, k2_xboole_0(A_262, B_263)))=k3_xboole_0(A_262, B_263))), inference(superposition, [status(thm), theory('equality')], [c_1120, c_18])).
% 7.51/2.95  tff(c_134, plain, (![B_79, A_80]: (k5_xboole_0(B_79, A_80)=k5_xboole_0(A_80, B_79))), inference(cnfTransformation, [status(thm)], [f_27])).
% 7.51/2.95  tff(c_16, plain, (![A_15]: (k5_xboole_0(A_15, k1_xboole_0)=A_15)), inference(cnfTransformation, [status(thm)], [f_43])).
% 7.51/2.95  tff(c_150, plain, (![A_80]: (k5_xboole_0(k1_xboole_0, A_80)=A_80)), inference(superposition, [status(thm), theory('equality')], [c_134, c_16])).
% 7.51/2.95  tff(c_801, plain, (![A_140, B_141, C_142]: (k5_xboole_0(k5_xboole_0(A_140, B_141), C_142)=k5_xboole_0(A_140, k5_xboole_0(B_141, C_142)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 7.51/2.95  tff(c_865, plain, (![A_19, C_142]: (k5_xboole_0(A_19, k5_xboole_0(A_19, C_142))=k5_xboole_0(k1_xboole_0, C_142))), inference(superposition, [status(thm), theory('equality')], [c_20, c_801])).
% 7.51/2.95  tff(c_878, plain, (![A_19, C_142]: (k5_xboole_0(A_19, k5_xboole_0(A_19, C_142))=C_142)), inference(demodulation, [status(thm), theory('equality')], [c_150, c_865])).
% 7.51/2.95  tff(c_8572, plain, (![B_263, A_262]: (k5_xboole_0(B_263, k2_xboole_0(A_262, B_263))=k5_xboole_0(A_262, k3_xboole_0(A_262, B_263)))), inference(superposition, [status(thm), theory('equality')], [c_8516, c_878])).
% 7.51/2.95  tff(c_8690, plain, (![B_263, A_262]: (k5_xboole_0(B_263, k2_xboole_0(A_262, B_263))=k4_xboole_0(A_262, B_263))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_8572])).
% 7.51/2.95  tff(c_2, plain, (![B_2, A_1]: (k5_xboole_0(B_2, A_1)=k5_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 7.51/2.95  tff(c_52, plain, (![A_66, B_67]: (k4_xboole_0(k1_tarski(A_66), B_67)=k1_tarski(A_66) | r2_hidden(A_66, B_67))), inference(cnfTransformation, [status(thm)], [f_84])).
% 7.51/2.95  tff(c_24, plain, (![B_23, A_22]: (k2_tarski(B_23, A_22)=k2_tarski(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_51])).
% 7.51/2.95  tff(c_265, plain, (![A_86, B_87]: (k3_tarski(k2_tarski(A_86, B_87))=k2_xboole_0(A_86, B_87))), inference(cnfTransformation, [status(thm)], [f_86])).
% 7.51/2.95  tff(c_315, plain, (![A_96, B_97]: (k3_tarski(k2_tarski(A_96, B_97))=k2_xboole_0(B_97, A_96))), inference(superposition, [status(thm), theory('equality')], [c_24, c_265])).
% 7.51/2.95  tff(c_54, plain, (![A_68, B_69]: (k3_tarski(k2_tarski(A_68, B_69))=k2_xboole_0(A_68, B_69))), inference(cnfTransformation, [status(thm)], [f_86])).
% 7.51/2.95  tff(c_321, plain, (![B_97, A_96]: (k2_xboole_0(B_97, A_96)=k2_xboole_0(A_96, B_97))), inference(superposition, [status(thm), theory('equality')], [c_315, c_54])).
% 7.51/2.95  tff(c_8715, plain, (![B_264, A_265]: (k5_xboole_0(B_264, k2_xboole_0(A_265, B_264))=k4_xboole_0(A_265, B_264))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_8572])).
% 7.51/2.95  tff(c_879, plain, (![A_143, C_144]: (k5_xboole_0(A_143, k5_xboole_0(A_143, C_144))=C_144)), inference(demodulation, [status(thm), theory('equality')], [c_150, c_865])).
% 7.51/2.95  tff(c_922, plain, (![A_1, B_2]: (k5_xboole_0(A_1, k5_xboole_0(B_2, A_1))=B_2)), inference(superposition, [status(thm), theory('equality')], [c_2, c_879])).
% 7.51/2.95  tff(c_9085, plain, (![A_268, B_269]: (k5_xboole_0(k2_xboole_0(A_268, B_269), k4_xboole_0(A_268, B_269))=B_269)), inference(superposition, [status(thm), theory('equality')], [c_8715, c_922])).
% 7.51/2.95  tff(c_10068, plain, (![A_279, B_280]: (k5_xboole_0(k2_xboole_0(A_279, B_280), k4_xboole_0(B_280, A_279))=A_279)), inference(superposition, [status(thm), theory('equality')], [c_321, c_9085])).
% 7.51/2.95  tff(c_10184, plain, (![B_67, A_66]: (k5_xboole_0(k2_xboole_0(B_67, k1_tarski(A_66)), k1_tarski(A_66))=B_67 | r2_hidden(A_66, B_67))), inference(superposition, [status(thm), theory('equality')], [c_52, c_10068])).
% 7.51/2.95  tff(c_12021, plain, (![B_299, A_300]: (k4_xboole_0(B_299, k1_tarski(A_300))=B_299 | r2_hidden(A_300, B_299))), inference(demodulation, [status(thm), theory('equality')], [c_8690, c_2, c_10184])).
% 7.51/2.95  tff(c_60, plain, (k4_xboole_0('#skF_1', k1_tarski('#skF_2'))!='#skF_1' | r2_hidden('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_97])).
% 7.51/2.95  tff(c_294, plain, (k4_xboole_0('#skF_1', k1_tarski('#skF_2'))!='#skF_1'), inference(splitLeft, [status(thm)], [c_60])).
% 7.51/2.95  tff(c_12109, plain, (r2_hidden('#skF_2', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_12021, c_294])).
% 7.51/2.95  tff(c_12176, plain, $false, inference(negUnitSimplification, [status(thm)], [c_120, c_12109])).
% 7.51/2.95  tff(c_12177, plain, (r2_hidden('#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_60])).
% 7.51/2.95  tff(c_44, plain, (![A_60, B_61]: (r1_tarski(k1_tarski(A_60), B_61) | ~r2_hidden(A_60, B_61))), inference(cnfTransformation, [status(thm)], [f_71])).
% 7.51/2.95  tff(c_12178, plain, (k4_xboole_0('#skF_1', k1_tarski('#skF_2'))='#skF_1'), inference(splitRight, [status(thm)], [c_60])).
% 7.51/2.95  tff(c_64, plain, (k4_xboole_0('#skF_1', k1_tarski('#skF_2'))!='#skF_1' | k4_xboole_0('#skF_3', k1_tarski('#skF_4'))='#skF_3'), inference(cnfTransformation, [status(thm)], [f_97])).
% 7.51/2.95  tff(c_12187, plain, (k4_xboole_0('#skF_3', k1_tarski('#skF_4'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_12178, c_64])).
% 7.51/2.95  tff(c_12, plain, (![A_11, B_12]: (k1_xboole_0=A_11 | ~r1_tarski(A_11, k4_xboole_0(B_12, A_11)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 7.51/2.95  tff(c_12191, plain, (k1_tarski('#skF_4')=k1_xboole_0 | ~r1_tarski(k1_tarski('#skF_4'), '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_12187, c_12])).
% 7.51/2.95  tff(c_12293, plain, (~r1_tarski(k1_tarski('#skF_4'), '#skF_3')), inference(splitLeft, [status(thm)], [c_12191])).
% 7.51/2.95  tff(c_12300, plain, (~r2_hidden('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_44, c_12293])).
% 7.51/2.95  tff(c_12304, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12177, c_12300])).
% 7.51/2.95  tff(c_12305, plain, (k1_tarski('#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_12191])).
% 7.51/2.95  tff(c_12367, plain, $false, inference(negUnitSimplification, [status(thm)], [c_12355, c_12305])).
% 7.51/2.95  tff(c_12368, plain, (r2_hidden('#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_62])).
% 7.51/2.95  tff(c_12369, plain, (r2_hidden('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_62])).
% 7.51/2.95  tff(c_66, plain, (~r2_hidden('#skF_2', '#skF_1') | k4_xboole_0('#skF_3', k1_tarski('#skF_4'))='#skF_3'), inference(cnfTransformation, [status(thm)], [f_97])).
% 7.51/2.95  tff(c_12370, plain, (~r2_hidden('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_66])).
% 7.51/2.95  tff(c_12372, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12369, c_12370])).
% 7.51/2.95  tff(c_12373, plain, (k4_xboole_0('#skF_3', k1_tarski('#skF_4'))='#skF_3'), inference(splitRight, [status(thm)], [c_66])).
% 7.51/2.95  tff(c_12524, plain, (![A_322, B_323]: (k1_xboole_0=A_322 | ~r1_tarski(A_322, k4_xboole_0(B_323, A_322)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 7.51/2.95  tff(c_12527, plain, (k1_tarski('#skF_4')=k1_xboole_0 | ~r1_tarski(k1_tarski('#skF_4'), '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_12373, c_12524])).
% 7.51/2.95  tff(c_12578, plain, (~r1_tarski(k1_tarski('#skF_4'), '#skF_3')), inference(splitLeft, [status(thm)], [c_12527])).
% 7.51/2.95  tff(c_12581, plain, (~r2_hidden('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_44, c_12578])).
% 7.51/2.95  tff(c_12585, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12368, c_12581])).
% 7.51/2.95  tff(c_12586, plain, (k1_tarski('#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_12527])).
% 7.51/2.95  tff(c_12598, plain, (k4_xboole_0(k1_tarski('#skF_4'), k1_xboole_0)!=k1_tarski('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_12586, c_56])).
% 7.51/2.95  tff(c_12608, plain, (k4_xboole_0(k1_xboole_0, k1_xboole_0)!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_12586, c_12586, c_12598])).
% 7.51/2.95  tff(c_12734, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12730, c_12608])).
% 7.51/2.95  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.51/2.95  
% 7.51/2.95  Inference rules
% 7.51/2.95  ----------------------
% 7.51/2.95  #Ref     : 0
% 7.51/2.95  #Sup     : 3083
% 7.51/2.95  #Fact    : 0
% 7.51/2.95  #Define  : 0
% 7.51/2.95  #Split   : 6
% 7.51/2.95  #Chain   : 0
% 7.51/2.95  #Close   : 0
% 7.51/2.95  
% 7.51/2.95  Ordering : KBO
% 7.51/2.95  
% 7.51/2.95  Simplification rules
% 7.51/2.95  ----------------------
% 7.51/2.95  #Subsume      : 272
% 7.51/2.95  #Demod        : 3324
% 7.51/2.95  #Tautology    : 1761
% 7.51/2.95  #SimpNegUnit  : 109
% 7.51/2.95  #BackRed      : 9
% 7.51/2.95  
% 7.51/2.95  #Partial instantiations: 0
% 7.51/2.95  #Strategies tried      : 1
% 7.51/2.95  
% 7.51/2.95  Timing (in seconds)
% 7.51/2.95  ----------------------
% 7.51/2.96  Preprocessing        : 0.34
% 7.51/2.96  Parsing              : 0.18
% 7.51/2.96  CNF conversion       : 0.02
% 7.51/2.96  Main loop            : 1.84
% 7.51/2.96  Inferencing          : 0.46
% 7.51/2.96  Reduction            : 0.94
% 7.51/2.96  Demodulation         : 0.80
% 7.51/2.96  BG Simplification    : 0.06
% 7.51/2.96  Subsumption          : 0.27
% 7.51/2.96  Abstraction          : 0.09
% 7.51/2.96  MUC search           : 0.00
% 7.51/2.96  Cooper               : 0.00
% 7.51/2.96  Total                : 2.22
% 7.51/2.96  Index Insertion      : 0.00
% 7.51/2.96  Index Deletion       : 0.00
% 7.51/2.96  Index Matching       : 0.00
% 7.51/2.96  BG Taut test         : 0.00
%------------------------------------------------------------------------------

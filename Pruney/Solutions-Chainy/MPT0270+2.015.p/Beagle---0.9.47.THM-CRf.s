%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:52:54 EST 2020

% Result     : Theorem 11.25s
% Output     : CNFRefutation 11.43s
% Verified   : 
% Statistics : Number of formulae       :  165 ( 626 expanded)
%              Number of leaves         :   37 ( 233 expanded)
%              Depth                    :   15
%              Number of atoms          :  156 ( 630 expanded)
%              Number of equality atoms :  129 ( 587 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

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

tff(f_93,negated_conjecture,(
    ~ ! [A,B] :
        ( k4_xboole_0(k1_tarski(A),B) = k1_tarski(A)
      <=> ~ r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_zfmisc_1)).

tff(f_80,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_zfmisc_1)).

tff(f_53,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_75,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_33,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_47,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_51,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_49,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k2_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

tff(f_41,axiom,(
    ! [A,B] : k2_xboole_0(A,k2_xboole_0(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => k4_xboole_0(k2_xboole_0(A,B),B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_87,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k4_xboole_0(B,k1_tarski(C)))
    <=> ( r2_hidden(A,B)
        & A != C ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_zfmisc_1)).

tff(c_60,plain,
    ( ~ r2_hidden('#skF_1','#skF_2')
    | r2_hidden('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_185,plain,(
    ~ r2_hidden('#skF_1','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_60])).

tff(c_50,plain,(
    ! [A_76,B_77] :
      ( r1_xboole_0(k1_tarski(A_76),B_77)
      | r2_hidden(A_76,B_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_26,plain,(
    ! [B_26,A_25] : k2_tarski(B_26,A_25) = k2_tarski(A_25,B_26) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_196,plain,(
    ! [A_94,B_95] : k3_tarski(k2_tarski(A_94,B_95)) = k2_xboole_0(A_94,B_95) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_225,plain,(
    ! [A_99,B_100] : k3_tarski(k2_tarski(A_99,B_100)) = k2_xboole_0(B_100,A_99) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_196])).

tff(c_48,plain,(
    ! [A_74,B_75] : k3_tarski(k2_tarski(A_74,B_75)) = k2_xboole_0(A_74,B_75) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_231,plain,(
    ! [B_100,A_99] : k2_xboole_0(B_100,A_99) = k2_xboole_0(A_99,B_100) ),
    inference(superposition,[status(thm),theory(equality)],[c_225,c_48])).

tff(c_8,plain,(
    ! [A_7,B_8] : k5_xboole_0(A_7,k3_xboole_0(A_7,B_8)) = k4_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_1125,plain,(
    ! [A_147,B_148,C_149] : k5_xboole_0(k5_xboole_0(A_147,B_148),C_149) = k5_xboole_0(A_147,k5_xboole_0(B_148,C_149)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_24,plain,(
    ! [A_23,B_24] : k5_xboole_0(k5_xboole_0(A_23,B_24),k2_xboole_0(A_23,B_24)) = k3_xboole_0(A_23,B_24) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_5545,plain,(
    ! [A_270,B_271] : k5_xboole_0(A_270,k5_xboole_0(B_271,k2_xboole_0(A_270,B_271))) = k3_xboole_0(A_270,B_271) ),
    inference(superposition,[status(thm),theory(equality)],[c_1125,c_24])).

tff(c_6,plain,(
    ! [A_5] : k3_xboole_0(A_5,A_5) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_22,plain,(
    ! [A_22] : k5_xboole_0(A_22,A_22) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_4,plain,(
    ! [A_3] : k2_xboole_0(A_3,A_3) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_692,plain,(
    ! [A_133,B_134] : k5_xboole_0(k5_xboole_0(A_133,B_134),k2_xboole_0(A_133,B_134)) = k3_xboole_0(A_133,B_134) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_746,plain,(
    ! [A_3] : k5_xboole_0(k5_xboole_0(A_3,A_3),A_3) = k3_xboole_0(A_3,A_3) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_692])).

tff(c_757,plain,(
    ! [A_3] : k5_xboole_0(k1_xboole_0,A_3) = A_3 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_22,c_746])).

tff(c_1202,plain,(
    ! [A_22,C_149] : k5_xboole_0(A_22,k5_xboole_0(A_22,C_149)) = k5_xboole_0(k1_xboole_0,C_149) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_1125])).

tff(c_1215,plain,(
    ! [A_22,C_149] : k5_xboole_0(A_22,k5_xboole_0(A_22,C_149)) = C_149 ),
    inference(demodulation,[status(thm),theory(equality)],[c_757,c_1202])).

tff(c_5595,plain,(
    ! [B_271,A_270] : k5_xboole_0(B_271,k2_xboole_0(A_270,B_271)) = k5_xboole_0(A_270,k3_xboole_0(A_270,B_271)) ),
    inference(superposition,[status(thm),theory(equality)],[c_5545,c_1215])).

tff(c_5725,plain,(
    ! [B_272,A_273] : k5_xboole_0(B_272,k2_xboole_0(A_273,B_272)) = k4_xboole_0(A_273,B_272) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_5595])).

tff(c_5830,plain,(
    ! [B_100,A_99] : k5_xboole_0(B_100,k2_xboole_0(B_100,A_99)) = k4_xboole_0(A_99,B_100) ),
    inference(superposition,[status(thm),theory(equality)],[c_231,c_5725])).

tff(c_16,plain,(
    ! [A_15,B_16] : k2_xboole_0(A_15,k2_xboole_0(A_15,B_16)) = k2_xboole_0(A_15,B_16) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_6084,plain,(
    ! [B_280,A_281] : k5_xboole_0(B_280,k2_xboole_0(B_280,A_281)) = k4_xboole_0(A_281,B_280) ),
    inference(superposition,[status(thm),theory(equality)],[c_231,c_5725])).

tff(c_6191,plain,(
    ! [A_15,B_16] : k5_xboole_0(A_15,k2_xboole_0(A_15,B_16)) = k4_xboole_0(k2_xboole_0(A_15,B_16),A_15) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_6084])).

tff(c_6225,plain,(
    ! [A_15,B_16] : k4_xboole_0(k2_xboole_0(A_15,B_16),A_15) = k4_xboole_0(B_16,A_15) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5830,c_6191])).

tff(c_545,plain,(
    ! [A_118,B_119] :
      ( k4_xboole_0(k2_xboole_0(A_118,B_119),B_119) = A_118
      | ~ r1_xboole_0(A_118,B_119) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_588,plain,(
    ! [A_99,B_100] :
      ( k4_xboole_0(k2_xboole_0(A_99,B_100),A_99) = B_100
      | ~ r1_xboole_0(B_100,A_99) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_231,c_545])).

tff(c_8654,plain,(
    ! [B_321,A_322] :
      ( k4_xboole_0(B_321,A_322) = B_321
      | ~ r1_xboole_0(B_321,A_322) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6225,c_588])).

tff(c_14875,plain,(
    ! [A_383,B_384] :
      ( k4_xboole_0(k1_tarski(A_383),B_384) = k1_tarski(A_383)
      | r2_hidden(A_383,B_384) ) ),
    inference(resolution,[status(thm)],[c_50,c_8654])).

tff(c_58,plain,
    ( k4_xboole_0(k1_tarski('#skF_1'),'#skF_2') != k1_tarski('#skF_1')
    | r2_hidden('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_186,plain,(
    k4_xboole_0(k1_tarski('#skF_1'),'#skF_2') != k1_tarski('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_58])).

tff(c_15002,plain,(
    r2_hidden('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_14875,c_186])).

tff(c_15070,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_185,c_15002])).

tff(c_15071,plain,(
    r2_hidden('#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_15592,plain,(
    ! [A_424,B_425] : k5_xboole_0(k5_xboole_0(A_424,B_425),k2_xboole_0(A_424,B_425)) = k3_xboole_0(A_424,B_425) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_15646,plain,(
    ! [A_3] : k5_xboole_0(k5_xboole_0(A_3,A_3),A_3) = k3_xboole_0(A_3,A_3) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_15592])).

tff(c_15659,plain,(
    ! [A_426] : k5_xboole_0(k1_xboole_0,A_426) = A_426 ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_6,c_15646])).

tff(c_2,plain,(
    ! [B_2,A_1] : k5_xboole_0(B_2,A_1) = k5_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_15672,plain,(
    ! [A_426] : k5_xboole_0(A_426,k1_xboole_0) = A_426 ),
    inference(superposition,[status(thm),theory(equality)],[c_15659,c_2])).

tff(c_15657,plain,(
    ! [A_3] : k5_xboole_0(k1_xboole_0,A_3) = A_3 ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_6,c_15646])).

tff(c_15756,plain,(
    ! [A_428,B_429,C_430] : k5_xboole_0(k5_xboole_0(A_428,B_429),C_430) = k5_xboole_0(A_428,k5_xboole_0(B_429,C_430)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_15833,plain,(
    ! [A_22,C_430] : k5_xboole_0(A_22,k5_xboole_0(A_22,C_430)) = k5_xboole_0(k1_xboole_0,C_430) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_15756])).

tff(c_15984,plain,(
    ! [A_438,C_439] : k5_xboole_0(A_438,k5_xboole_0(A_438,C_439)) = C_439 ),
    inference(demodulation,[status(thm),theory(equality)],[c_15657,c_15833])).

tff(c_16033,plain,(
    ! [A_7,B_8] : k5_xboole_0(A_7,k4_xboole_0(A_7,B_8)) = k3_xboole_0(A_7,B_8) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_15984])).

tff(c_18965,plain,(
    ! [A_536,B_537] : k5_xboole_0(A_536,k5_xboole_0(B_537,k2_xboole_0(A_536,B_537))) = k3_xboole_0(A_536,B_537) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_15756])).

tff(c_15846,plain,(
    ! [A_22,C_430] : k5_xboole_0(A_22,k5_xboole_0(A_22,C_430)) = C_430 ),
    inference(demodulation,[status(thm),theory(equality)],[c_15657,c_15833])).

tff(c_19008,plain,(
    ! [B_537,A_536] : k5_xboole_0(B_537,k2_xboole_0(A_536,B_537)) = k5_xboole_0(A_536,k3_xboole_0(A_536,B_537)) ),
    inference(superposition,[status(thm),theory(equality)],[c_18965,c_15846])).

tff(c_19100,plain,(
    ! [B_537,A_536] : k5_xboole_0(B_537,k2_xboole_0(A_536,B_537)) = k4_xboole_0(A_536,B_537) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_19008])).

tff(c_15072,plain,(
    k4_xboole_0(k1_tarski('#skF_1'),'#skF_2') = k1_tarski('#skF_1') ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_62,plain,
    ( k4_xboole_0(k1_tarski('#skF_1'),'#skF_2') != k1_tarski('#skF_1')
    | k4_xboole_0(k1_tarski('#skF_3'),'#skF_4') = k1_tarski('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_15265,plain,(
    k4_xboole_0(k1_tarski('#skF_3'),'#skF_4') = k1_tarski('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_15072,c_62])).

tff(c_15086,plain,(
    ! [A_387,B_388] : k3_tarski(k2_tarski(A_387,B_388)) = k2_xboole_0(A_387,B_388) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_15115,plain,(
    ! [A_392,B_393] : k3_tarski(k2_tarski(A_392,B_393)) = k2_xboole_0(B_393,A_392) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_15086])).

tff(c_15121,plain,(
    ! [B_393,A_392] : k2_xboole_0(B_393,A_392) = k2_xboole_0(A_392,B_393) ),
    inference(superposition,[status(thm),theory(equality)],[c_15115,c_48])).

tff(c_16036,plain,(
    ! [A_1,B_2] : k5_xboole_0(A_1,k5_xboole_0(B_2,A_1)) = B_2 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_15984])).

tff(c_18348,plain,(
    ! [A_523,B_524] : k5_xboole_0(k2_xboole_0(A_523,B_524),k5_xboole_0(A_523,B_524)) = k3_xboole_0(A_523,B_524) ),
    inference(superposition,[status(thm),theory(equality)],[c_15592,c_2])).

tff(c_18482,plain,(
    ! [A_15,B_16] : k5_xboole_0(k2_xboole_0(A_15,B_16),k5_xboole_0(A_15,k2_xboole_0(A_15,B_16))) = k3_xboole_0(A_15,k2_xboole_0(A_15,B_16)) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_18348])).

tff(c_18539,plain,(
    ! [A_525,B_526] : k3_xboole_0(A_525,k2_xboole_0(A_525,B_526)) = A_525 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16036,c_18482])).

tff(c_18589,plain,(
    ! [A_392,B_393] : k3_xboole_0(A_392,k2_xboole_0(B_393,A_392)) = A_392 ),
    inference(superposition,[status(thm),theory(equality)],[c_15121,c_18539])).

tff(c_15270,plain,(
    ! [A_401,B_402] : k2_xboole_0(A_401,k2_xboole_0(A_401,B_402)) = k2_xboole_0(A_401,B_402) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_15296,plain,(
    ! [A_392,B_393] : k2_xboole_0(A_392,k2_xboole_0(B_393,A_392)) = k2_xboole_0(A_392,B_393) ),
    inference(superposition,[status(thm),theory(equality)],[c_15121,c_15270])).

tff(c_19119,plain,(
    ! [B_538,A_539] : k5_xboole_0(B_538,k2_xboole_0(A_539,B_538)) = k4_xboole_0(A_539,B_538) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_19008])).

tff(c_15601,plain,(
    ! [A_424,B_425] : k5_xboole_0(k2_xboole_0(A_424,B_425),k5_xboole_0(A_424,B_425)) = k3_xboole_0(A_424,B_425) ),
    inference(superposition,[status(thm),theory(equality)],[c_15592,c_2])).

tff(c_19125,plain,(
    ! [B_538,A_539] : k5_xboole_0(k2_xboole_0(B_538,k2_xboole_0(A_539,B_538)),k4_xboole_0(A_539,B_538)) = k3_xboole_0(B_538,k2_xboole_0(A_539,B_538)) ),
    inference(superposition,[status(thm),theory(equality)],[c_19119,c_15601])).

tff(c_19229,plain,(
    ! [B_540,A_541] : k5_xboole_0(k2_xboole_0(B_540,A_541),k4_xboole_0(A_541,B_540)) = B_540 ),
    inference(demodulation,[status(thm),theory(equality)],[c_18589,c_15296,c_19125])).

tff(c_19313,plain,(
    k5_xboole_0(k2_xboole_0('#skF_4',k1_tarski('#skF_3')),k1_tarski('#skF_3')) = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_15265,c_19229])).

tff(c_17292,plain,(
    ! [A_514,A_512,B_513] : k5_xboole_0(A_514,k5_xboole_0(A_512,B_513)) = k5_xboole_0(A_512,k5_xboole_0(B_513,A_514)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_15756])).

tff(c_17696,plain,(
    ! [A_515,A_516] : k5_xboole_0(k1_xboole_0,k5_xboole_0(A_515,A_516)) = k5_xboole_0(A_516,A_515) ),
    inference(superposition,[status(thm),theory(equality)],[c_15657,c_17292])).

tff(c_17723,plain,(
    ! [A_515,A_516] : k5_xboole_0(k5_xboole_0(A_515,A_516),k5_xboole_0(A_516,A_515)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_17696,c_16036])).

tff(c_19362,plain,(
    k5_xboole_0('#skF_4',k5_xboole_0(k1_tarski('#skF_3'),k2_xboole_0('#skF_4',k1_tarski('#skF_3')))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_19313,c_17723])).

tff(c_19409,plain,(
    k3_xboole_0('#skF_4',k1_tarski('#skF_3')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16033,c_19100,c_19362])).

tff(c_16557,plain,(
    ! [A_465,B_466] : k5_xboole_0(A_465,k4_xboole_0(A_465,B_466)) = k3_xboole_0(A_465,B_466) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_15984])).

tff(c_16186,plain,(
    ! [A_443,B_444] : k5_xboole_0(A_443,k5_xboole_0(B_444,A_443)) = B_444 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_15984])).

tff(c_16189,plain,(
    ! [B_444,A_443] : k5_xboole_0(k5_xboole_0(B_444,A_443),B_444) = A_443 ),
    inference(superposition,[status(thm),theory(equality)],[c_16186,c_16036])).

tff(c_16566,plain,(
    ! [A_465,B_466] : k5_xboole_0(k3_xboole_0(A_465,B_466),A_465) = k4_xboole_0(A_465,B_466) ),
    inference(superposition,[status(thm),theory(equality)],[c_16557,c_16189])).

tff(c_19417,plain,(
    k4_xboole_0('#skF_4',k1_tarski('#skF_3')) = k5_xboole_0(k1_xboole_0,'#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_19409,c_16566])).

tff(c_19429,plain,(
    k4_xboole_0('#skF_4',k1_tarski('#skF_3')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_15672,c_2,c_19417])).

tff(c_54,plain,(
    ! [C_80,B_79] : ~ r2_hidden(C_80,k4_xboole_0(B_79,k1_tarski(C_80))) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_19460,plain,(
    ~ r2_hidden('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_19429,c_54])).

tff(c_19471,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_15071,c_19460])).

tff(c_19472,plain,(
    r2_hidden('#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_20653,plain,(
    ! [A_606,B_607] : k5_xboole_0(k5_xboole_0(A_606,B_607),k2_xboole_0(A_606,B_607)) = k3_xboole_0(A_606,B_607) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_20741,plain,(
    ! [A_3] : k5_xboole_0(k5_xboole_0(A_3,A_3),A_3) = k3_xboole_0(A_3,A_3) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_20653])).

tff(c_20758,plain,(
    ! [A_608] : k5_xboole_0(k1_xboole_0,A_608) = A_608 ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_6,c_20741])).

tff(c_20782,plain,(
    ! [A_608] : k5_xboole_0(A_608,k1_xboole_0) = A_608 ),
    inference(superposition,[status(thm),theory(equality)],[c_20758,c_2])).

tff(c_20752,plain,(
    ! [A_3] : k5_xboole_0(k1_xboole_0,A_3) = A_3 ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_6,c_20741])).

tff(c_20108,plain,(
    ! [A_592,B_593,C_594] : k5_xboole_0(k5_xboole_0(A_592,B_593),C_594) = k5_xboole_0(A_592,k5_xboole_0(B_593,C_594)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_20158,plain,(
    ! [A_22,C_594] : k5_xboole_0(A_22,k5_xboole_0(A_22,C_594)) = k5_xboole_0(k1_xboole_0,C_594) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_20108])).

tff(c_21014,plain,(
    ! [A_620,C_621] : k5_xboole_0(A_620,k5_xboole_0(A_620,C_621)) = C_621 ),
    inference(demodulation,[status(thm),theory(equality)],[c_20752,c_20158])).

tff(c_21063,plain,(
    ! [A_7,B_8] : k5_xboole_0(A_7,k4_xboole_0(A_7,B_8)) = k3_xboole_0(A_7,B_8) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_21014])).

tff(c_20,plain,(
    ! [A_19,B_20,C_21] : k5_xboole_0(k5_xboole_0(A_19,B_20),C_21) = k5_xboole_0(A_19,k5_xboole_0(B_20,C_21)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_24788,plain,(
    ! [A_717,B_718] : k5_xboole_0(A_717,k5_xboole_0(B_718,k2_xboole_0(A_717,B_718))) = k3_xboole_0(A_717,B_718) ),
    inference(superposition,[status(thm),theory(equality)],[c_20653,c_20])).

tff(c_20755,plain,(
    ! [A_22,C_594] : k5_xboole_0(A_22,k5_xboole_0(A_22,C_594)) = C_594 ),
    inference(demodulation,[status(thm),theory(equality)],[c_20752,c_20158])).

tff(c_24841,plain,(
    ! [B_718,A_717] : k5_xboole_0(B_718,k2_xboole_0(A_717,B_718)) = k5_xboole_0(A_717,k3_xboole_0(A_717,B_718)) ),
    inference(superposition,[status(thm),theory(equality)],[c_24788,c_20755])).

tff(c_24945,plain,(
    ! [B_718,A_717] : k5_xboole_0(B_718,k2_xboole_0(A_717,B_718)) = k4_xboole_0(A_717,B_718) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_24841])).

tff(c_19473,plain,(
    r2_hidden('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_64,plain,
    ( ~ r2_hidden('#skF_1','#skF_2')
    | k4_xboole_0(k1_tarski('#skF_3'),'#skF_4') = k1_tarski('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_19671,plain,(
    k4_xboole_0(k1_tarski('#skF_3'),'#skF_4') = k1_tarski('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_19473,c_64])).

tff(c_19484,plain,(
    ! [A_546,B_547] : k3_tarski(k2_tarski(A_546,B_547)) = k2_xboole_0(A_546,B_547) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_19513,plain,(
    ! [B_549,A_550] : k3_tarski(k2_tarski(B_549,A_550)) = k2_xboole_0(A_550,B_549) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_19484])).

tff(c_19519,plain,(
    ! [B_549,A_550] : k2_xboole_0(B_549,A_550) = k2_xboole_0(A_550,B_549) ),
    inference(superposition,[status(thm),theory(equality)],[c_19513,c_48])).

tff(c_21069,plain,(
    ! [B_2,A_1] : k5_xboole_0(B_2,k5_xboole_0(A_1,B_2)) = A_1 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_21014])).

tff(c_22275,plain,(
    ! [B_682,A_683] : k5_xboole_0(k5_xboole_0(B_682,A_683),k2_xboole_0(A_683,B_682)) = k3_xboole_0(A_683,B_682) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_20653])).

tff(c_22393,plain,(
    ! [A_15,B_16] : k5_xboole_0(k5_xboole_0(k2_xboole_0(A_15,B_16),A_15),k2_xboole_0(A_15,B_16)) = k3_xboole_0(A_15,k2_xboole_0(A_15,B_16)) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_22275])).

tff(c_22455,plain,(
    ! [A_684,B_685] : k3_xboole_0(A_684,k2_xboole_0(A_684,B_685)) = A_684 ),
    inference(demodulation,[status(thm),theory(equality)],[c_21069,c_2,c_2,c_22393])).

tff(c_22505,plain,(
    ! [A_550,B_549] : k3_xboole_0(A_550,k2_xboole_0(B_549,A_550)) = A_550 ),
    inference(superposition,[status(thm),theory(equality)],[c_19519,c_22455])).

tff(c_19719,plain,(
    ! [A_561,B_562] : k2_xboole_0(A_561,k2_xboole_0(A_561,B_562)) = k2_xboole_0(A_561,B_562) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_19748,plain,(
    ! [A_550,B_549] : k2_xboole_0(A_550,k2_xboole_0(B_549,A_550)) = k2_xboole_0(A_550,B_549) ),
    inference(superposition,[status(thm),theory(equality)],[c_19519,c_19719])).

tff(c_24964,plain,(
    ! [B_719,A_720] : k5_xboole_0(B_719,k2_xboole_0(A_720,B_719)) = k4_xboole_0(A_720,B_719) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_24841])).

tff(c_20677,plain,(
    ! [A_606,B_607] : k5_xboole_0(k2_xboole_0(A_606,B_607),k5_xboole_0(A_606,B_607)) = k3_xboole_0(A_606,B_607) ),
    inference(superposition,[status(thm),theory(equality)],[c_20653,c_2])).

tff(c_24973,plain,(
    ! [B_719,A_720] : k5_xboole_0(k2_xboole_0(B_719,k2_xboole_0(A_720,B_719)),k4_xboole_0(A_720,B_719)) = k3_xboole_0(B_719,k2_xboole_0(A_720,B_719)) ),
    inference(superposition,[status(thm),theory(equality)],[c_24964,c_20677])).

tff(c_25092,plain,(
    ! [B_721,A_722] : k5_xboole_0(k2_xboole_0(B_721,A_722),k4_xboole_0(A_722,B_721)) = B_721 ),
    inference(demodulation,[status(thm),theory(equality)],[c_22505,c_19748,c_24973])).

tff(c_25188,plain,(
    k5_xboole_0(k2_xboole_0('#skF_4',k1_tarski('#skF_3')),k1_tarski('#skF_3')) = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_19671,c_25092])).

tff(c_22881,plain,(
    ! [A_697,A_695,B_696] : k5_xboole_0(A_697,k5_xboole_0(A_695,B_696)) = k5_xboole_0(A_695,k5_xboole_0(B_696,A_697)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_20108])).

tff(c_23330,plain,(
    ! [A_698,A_699] : k5_xboole_0(k1_xboole_0,k5_xboole_0(A_698,A_699)) = k5_xboole_0(A_699,A_698) ),
    inference(superposition,[status(thm),theory(equality)],[c_20752,c_22881])).

tff(c_23363,plain,(
    ! [A_698,A_699] : k5_xboole_0(k5_xboole_0(A_698,A_699),k5_xboole_0(A_699,A_698)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_23330,c_21069])).

tff(c_25246,plain,(
    k5_xboole_0('#skF_4',k5_xboole_0(k1_tarski('#skF_3'),k2_xboole_0('#skF_4',k1_tarski('#skF_3')))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_25188,c_23363])).

tff(c_25299,plain,(
    k3_xboole_0('#skF_4',k1_tarski('#skF_3')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_21063,c_24945,c_25246])).

tff(c_21436,plain,(
    ! [A_648,B_649] : k5_xboole_0(A_648,k4_xboole_0(A_648,B_649)) = k3_xboole_0(A_648,B_649) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_21014])).

tff(c_21101,plain,(
    ! [B_629,A_630] : k5_xboole_0(B_629,k5_xboole_0(A_630,B_629)) = A_630 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_21014])).

tff(c_21104,plain,(
    ! [A_630,B_629] : k5_xboole_0(k5_xboole_0(A_630,B_629),A_630) = B_629 ),
    inference(superposition,[status(thm),theory(equality)],[c_21101,c_21069])).

tff(c_21442,plain,(
    ! [A_648,B_649] : k5_xboole_0(k3_xboole_0(A_648,B_649),A_648) = k4_xboole_0(A_648,B_649) ),
    inference(superposition,[status(thm),theory(equality)],[c_21436,c_21104])).

tff(c_25308,plain,(
    k4_xboole_0('#skF_4',k1_tarski('#skF_3')) = k5_xboole_0(k1_xboole_0,'#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_25299,c_21442])).

tff(c_25320,plain,(
    k4_xboole_0('#skF_4',k1_tarski('#skF_3')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_20782,c_2,c_25308])).

tff(c_25354,plain,(
    ~ r2_hidden('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_25320,c_54])).

tff(c_25366,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_19472,c_25354])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:23:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 11.25/4.31  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.25/4.32  
% 11.25/4.32  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.25/4.32  %$ r2_hidden > r1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 11.25/4.32  
% 11.25/4.32  %Foreground sorts:
% 11.25/4.32  
% 11.25/4.32  
% 11.25/4.32  %Background operators:
% 11.25/4.32  
% 11.25/4.32  
% 11.25/4.32  %Foreground operators:
% 11.25/4.32  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 11.25/4.32  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 11.25/4.32  tff(k1_tarski, type, k1_tarski: $i > $i).
% 11.25/4.32  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 11.25/4.32  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 11.25/4.32  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 11.25/4.32  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 11.25/4.32  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 11.25/4.32  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 11.25/4.32  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 11.25/4.32  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 11.25/4.32  tff('#skF_2', type, '#skF_2': $i).
% 11.25/4.32  tff('#skF_3', type, '#skF_3': $i).
% 11.25/4.32  tff('#skF_1', type, '#skF_1': $i).
% 11.25/4.32  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 11.25/4.32  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 11.25/4.32  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 11.25/4.32  tff(k3_tarski, type, k3_tarski: $i > $i).
% 11.25/4.32  tff('#skF_4', type, '#skF_4': $i).
% 11.25/4.32  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 11.25/4.32  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 11.25/4.32  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 11.25/4.32  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 11.25/4.32  
% 11.43/4.35  tff(f_93, negated_conjecture, ~(![A, B]: ((k4_xboole_0(k1_tarski(A), B) = k1_tarski(A)) <=> ~r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t67_zfmisc_1)).
% 11.43/4.35  tff(f_80, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t56_zfmisc_1)).
% 11.43/4.35  tff(f_53, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 11.43/4.35  tff(f_75, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 11.43/4.35  tff(f_33, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 11.43/4.35  tff(f_47, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_xboole_1)).
% 11.43/4.35  tff(f_51, axiom, (![A, B]: (k3_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k2_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t95_xboole_1)).
% 11.43/4.35  tff(f_31, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 11.43/4.35  tff(f_49, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_xboole_1)).
% 11.43/4.35  tff(f_29, axiom, (![A, B]: (k2_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 11.43/4.35  tff(f_41, axiom, (![A, B]: (k2_xboole_0(A, k2_xboole_0(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_xboole_1)).
% 11.43/4.35  tff(f_45, axiom, (![A, B]: (r1_xboole_0(A, B) => (k4_xboole_0(k2_xboole_0(A, B), B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t88_xboole_1)).
% 11.43/4.35  tff(f_27, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 11.43/4.35  tff(f_87, axiom, (![A, B, C]: (r2_hidden(A, k4_xboole_0(B, k1_tarski(C))) <=> (r2_hidden(A, B) & ~(A = C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_zfmisc_1)).
% 11.43/4.35  tff(c_60, plain, (~r2_hidden('#skF_1', '#skF_2') | r2_hidden('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_93])).
% 11.43/4.35  tff(c_185, plain, (~r2_hidden('#skF_1', '#skF_2')), inference(splitLeft, [status(thm)], [c_60])).
% 11.43/4.35  tff(c_50, plain, (![A_76, B_77]: (r1_xboole_0(k1_tarski(A_76), B_77) | r2_hidden(A_76, B_77))), inference(cnfTransformation, [status(thm)], [f_80])).
% 11.43/4.35  tff(c_26, plain, (![B_26, A_25]: (k2_tarski(B_26, A_25)=k2_tarski(A_25, B_26))), inference(cnfTransformation, [status(thm)], [f_53])).
% 11.43/4.35  tff(c_196, plain, (![A_94, B_95]: (k3_tarski(k2_tarski(A_94, B_95))=k2_xboole_0(A_94, B_95))), inference(cnfTransformation, [status(thm)], [f_75])).
% 11.43/4.35  tff(c_225, plain, (![A_99, B_100]: (k3_tarski(k2_tarski(A_99, B_100))=k2_xboole_0(B_100, A_99))), inference(superposition, [status(thm), theory('equality')], [c_26, c_196])).
% 11.43/4.35  tff(c_48, plain, (![A_74, B_75]: (k3_tarski(k2_tarski(A_74, B_75))=k2_xboole_0(A_74, B_75))), inference(cnfTransformation, [status(thm)], [f_75])).
% 11.43/4.35  tff(c_231, plain, (![B_100, A_99]: (k2_xboole_0(B_100, A_99)=k2_xboole_0(A_99, B_100))), inference(superposition, [status(thm), theory('equality')], [c_225, c_48])).
% 11.43/4.35  tff(c_8, plain, (![A_7, B_8]: (k5_xboole_0(A_7, k3_xboole_0(A_7, B_8))=k4_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_33])).
% 11.43/4.35  tff(c_1125, plain, (![A_147, B_148, C_149]: (k5_xboole_0(k5_xboole_0(A_147, B_148), C_149)=k5_xboole_0(A_147, k5_xboole_0(B_148, C_149)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 11.43/4.35  tff(c_24, plain, (![A_23, B_24]: (k5_xboole_0(k5_xboole_0(A_23, B_24), k2_xboole_0(A_23, B_24))=k3_xboole_0(A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_51])).
% 11.43/4.35  tff(c_5545, plain, (![A_270, B_271]: (k5_xboole_0(A_270, k5_xboole_0(B_271, k2_xboole_0(A_270, B_271)))=k3_xboole_0(A_270, B_271))), inference(superposition, [status(thm), theory('equality')], [c_1125, c_24])).
% 11.43/4.35  tff(c_6, plain, (![A_5]: (k3_xboole_0(A_5, A_5)=A_5)), inference(cnfTransformation, [status(thm)], [f_31])).
% 11.43/4.35  tff(c_22, plain, (![A_22]: (k5_xboole_0(A_22, A_22)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_49])).
% 11.43/4.35  tff(c_4, plain, (![A_3]: (k2_xboole_0(A_3, A_3)=A_3)), inference(cnfTransformation, [status(thm)], [f_29])).
% 11.43/4.35  tff(c_692, plain, (![A_133, B_134]: (k5_xboole_0(k5_xboole_0(A_133, B_134), k2_xboole_0(A_133, B_134))=k3_xboole_0(A_133, B_134))), inference(cnfTransformation, [status(thm)], [f_51])).
% 11.43/4.35  tff(c_746, plain, (![A_3]: (k5_xboole_0(k5_xboole_0(A_3, A_3), A_3)=k3_xboole_0(A_3, A_3))), inference(superposition, [status(thm), theory('equality')], [c_4, c_692])).
% 11.43/4.35  tff(c_757, plain, (![A_3]: (k5_xboole_0(k1_xboole_0, A_3)=A_3)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_22, c_746])).
% 11.43/4.35  tff(c_1202, plain, (![A_22, C_149]: (k5_xboole_0(A_22, k5_xboole_0(A_22, C_149))=k5_xboole_0(k1_xboole_0, C_149))), inference(superposition, [status(thm), theory('equality')], [c_22, c_1125])).
% 11.43/4.35  tff(c_1215, plain, (![A_22, C_149]: (k5_xboole_0(A_22, k5_xboole_0(A_22, C_149))=C_149)), inference(demodulation, [status(thm), theory('equality')], [c_757, c_1202])).
% 11.43/4.35  tff(c_5595, plain, (![B_271, A_270]: (k5_xboole_0(B_271, k2_xboole_0(A_270, B_271))=k5_xboole_0(A_270, k3_xboole_0(A_270, B_271)))), inference(superposition, [status(thm), theory('equality')], [c_5545, c_1215])).
% 11.43/4.35  tff(c_5725, plain, (![B_272, A_273]: (k5_xboole_0(B_272, k2_xboole_0(A_273, B_272))=k4_xboole_0(A_273, B_272))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_5595])).
% 11.43/4.35  tff(c_5830, plain, (![B_100, A_99]: (k5_xboole_0(B_100, k2_xboole_0(B_100, A_99))=k4_xboole_0(A_99, B_100))), inference(superposition, [status(thm), theory('equality')], [c_231, c_5725])).
% 11.43/4.35  tff(c_16, plain, (![A_15, B_16]: (k2_xboole_0(A_15, k2_xboole_0(A_15, B_16))=k2_xboole_0(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_41])).
% 11.43/4.35  tff(c_6084, plain, (![B_280, A_281]: (k5_xboole_0(B_280, k2_xboole_0(B_280, A_281))=k4_xboole_0(A_281, B_280))), inference(superposition, [status(thm), theory('equality')], [c_231, c_5725])).
% 11.43/4.35  tff(c_6191, plain, (![A_15, B_16]: (k5_xboole_0(A_15, k2_xboole_0(A_15, B_16))=k4_xboole_0(k2_xboole_0(A_15, B_16), A_15))), inference(superposition, [status(thm), theory('equality')], [c_16, c_6084])).
% 11.43/4.35  tff(c_6225, plain, (![A_15, B_16]: (k4_xboole_0(k2_xboole_0(A_15, B_16), A_15)=k4_xboole_0(B_16, A_15))), inference(demodulation, [status(thm), theory('equality')], [c_5830, c_6191])).
% 11.43/4.35  tff(c_545, plain, (![A_118, B_119]: (k4_xboole_0(k2_xboole_0(A_118, B_119), B_119)=A_118 | ~r1_xboole_0(A_118, B_119))), inference(cnfTransformation, [status(thm)], [f_45])).
% 11.43/4.35  tff(c_588, plain, (![A_99, B_100]: (k4_xboole_0(k2_xboole_0(A_99, B_100), A_99)=B_100 | ~r1_xboole_0(B_100, A_99))), inference(superposition, [status(thm), theory('equality')], [c_231, c_545])).
% 11.43/4.35  tff(c_8654, plain, (![B_321, A_322]: (k4_xboole_0(B_321, A_322)=B_321 | ~r1_xboole_0(B_321, A_322))), inference(demodulation, [status(thm), theory('equality')], [c_6225, c_588])).
% 11.43/4.35  tff(c_14875, plain, (![A_383, B_384]: (k4_xboole_0(k1_tarski(A_383), B_384)=k1_tarski(A_383) | r2_hidden(A_383, B_384))), inference(resolution, [status(thm)], [c_50, c_8654])).
% 11.43/4.35  tff(c_58, plain, (k4_xboole_0(k1_tarski('#skF_1'), '#skF_2')!=k1_tarski('#skF_1') | r2_hidden('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_93])).
% 11.43/4.35  tff(c_186, plain, (k4_xboole_0(k1_tarski('#skF_1'), '#skF_2')!=k1_tarski('#skF_1')), inference(splitLeft, [status(thm)], [c_58])).
% 11.43/4.35  tff(c_15002, plain, (r2_hidden('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_14875, c_186])).
% 11.43/4.35  tff(c_15070, plain, $false, inference(negUnitSimplification, [status(thm)], [c_185, c_15002])).
% 11.43/4.35  tff(c_15071, plain, (r2_hidden('#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_58])).
% 11.43/4.35  tff(c_15592, plain, (![A_424, B_425]: (k5_xboole_0(k5_xboole_0(A_424, B_425), k2_xboole_0(A_424, B_425))=k3_xboole_0(A_424, B_425))), inference(cnfTransformation, [status(thm)], [f_51])).
% 11.43/4.35  tff(c_15646, plain, (![A_3]: (k5_xboole_0(k5_xboole_0(A_3, A_3), A_3)=k3_xboole_0(A_3, A_3))), inference(superposition, [status(thm), theory('equality')], [c_4, c_15592])).
% 11.43/4.35  tff(c_15659, plain, (![A_426]: (k5_xboole_0(k1_xboole_0, A_426)=A_426)), inference(demodulation, [status(thm), theory('equality')], [c_22, c_6, c_15646])).
% 11.43/4.35  tff(c_2, plain, (![B_2, A_1]: (k5_xboole_0(B_2, A_1)=k5_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 11.43/4.35  tff(c_15672, plain, (![A_426]: (k5_xboole_0(A_426, k1_xboole_0)=A_426)), inference(superposition, [status(thm), theory('equality')], [c_15659, c_2])).
% 11.43/4.35  tff(c_15657, plain, (![A_3]: (k5_xboole_0(k1_xboole_0, A_3)=A_3)), inference(demodulation, [status(thm), theory('equality')], [c_22, c_6, c_15646])).
% 11.43/4.35  tff(c_15756, plain, (![A_428, B_429, C_430]: (k5_xboole_0(k5_xboole_0(A_428, B_429), C_430)=k5_xboole_0(A_428, k5_xboole_0(B_429, C_430)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 11.43/4.35  tff(c_15833, plain, (![A_22, C_430]: (k5_xboole_0(A_22, k5_xboole_0(A_22, C_430))=k5_xboole_0(k1_xboole_0, C_430))), inference(superposition, [status(thm), theory('equality')], [c_22, c_15756])).
% 11.43/4.35  tff(c_15984, plain, (![A_438, C_439]: (k5_xboole_0(A_438, k5_xboole_0(A_438, C_439))=C_439)), inference(demodulation, [status(thm), theory('equality')], [c_15657, c_15833])).
% 11.43/4.35  tff(c_16033, plain, (![A_7, B_8]: (k5_xboole_0(A_7, k4_xboole_0(A_7, B_8))=k3_xboole_0(A_7, B_8))), inference(superposition, [status(thm), theory('equality')], [c_8, c_15984])).
% 11.43/4.35  tff(c_18965, plain, (![A_536, B_537]: (k5_xboole_0(A_536, k5_xboole_0(B_537, k2_xboole_0(A_536, B_537)))=k3_xboole_0(A_536, B_537))), inference(superposition, [status(thm), theory('equality')], [c_24, c_15756])).
% 11.43/4.35  tff(c_15846, plain, (![A_22, C_430]: (k5_xboole_0(A_22, k5_xboole_0(A_22, C_430))=C_430)), inference(demodulation, [status(thm), theory('equality')], [c_15657, c_15833])).
% 11.43/4.35  tff(c_19008, plain, (![B_537, A_536]: (k5_xboole_0(B_537, k2_xboole_0(A_536, B_537))=k5_xboole_0(A_536, k3_xboole_0(A_536, B_537)))), inference(superposition, [status(thm), theory('equality')], [c_18965, c_15846])).
% 11.43/4.35  tff(c_19100, plain, (![B_537, A_536]: (k5_xboole_0(B_537, k2_xboole_0(A_536, B_537))=k4_xboole_0(A_536, B_537))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_19008])).
% 11.43/4.35  tff(c_15072, plain, (k4_xboole_0(k1_tarski('#skF_1'), '#skF_2')=k1_tarski('#skF_1')), inference(splitRight, [status(thm)], [c_58])).
% 11.43/4.35  tff(c_62, plain, (k4_xboole_0(k1_tarski('#skF_1'), '#skF_2')!=k1_tarski('#skF_1') | k4_xboole_0(k1_tarski('#skF_3'), '#skF_4')=k1_tarski('#skF_3')), inference(cnfTransformation, [status(thm)], [f_93])).
% 11.43/4.35  tff(c_15265, plain, (k4_xboole_0(k1_tarski('#skF_3'), '#skF_4')=k1_tarski('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_15072, c_62])).
% 11.43/4.35  tff(c_15086, plain, (![A_387, B_388]: (k3_tarski(k2_tarski(A_387, B_388))=k2_xboole_0(A_387, B_388))), inference(cnfTransformation, [status(thm)], [f_75])).
% 11.43/4.35  tff(c_15115, plain, (![A_392, B_393]: (k3_tarski(k2_tarski(A_392, B_393))=k2_xboole_0(B_393, A_392))), inference(superposition, [status(thm), theory('equality')], [c_26, c_15086])).
% 11.43/4.35  tff(c_15121, plain, (![B_393, A_392]: (k2_xboole_0(B_393, A_392)=k2_xboole_0(A_392, B_393))), inference(superposition, [status(thm), theory('equality')], [c_15115, c_48])).
% 11.43/4.35  tff(c_16036, plain, (![A_1, B_2]: (k5_xboole_0(A_1, k5_xboole_0(B_2, A_1))=B_2)), inference(superposition, [status(thm), theory('equality')], [c_2, c_15984])).
% 11.43/4.35  tff(c_18348, plain, (![A_523, B_524]: (k5_xboole_0(k2_xboole_0(A_523, B_524), k5_xboole_0(A_523, B_524))=k3_xboole_0(A_523, B_524))), inference(superposition, [status(thm), theory('equality')], [c_15592, c_2])).
% 11.43/4.35  tff(c_18482, plain, (![A_15, B_16]: (k5_xboole_0(k2_xboole_0(A_15, B_16), k5_xboole_0(A_15, k2_xboole_0(A_15, B_16)))=k3_xboole_0(A_15, k2_xboole_0(A_15, B_16)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_18348])).
% 11.43/4.35  tff(c_18539, plain, (![A_525, B_526]: (k3_xboole_0(A_525, k2_xboole_0(A_525, B_526))=A_525)), inference(demodulation, [status(thm), theory('equality')], [c_16036, c_18482])).
% 11.43/4.35  tff(c_18589, plain, (![A_392, B_393]: (k3_xboole_0(A_392, k2_xboole_0(B_393, A_392))=A_392)), inference(superposition, [status(thm), theory('equality')], [c_15121, c_18539])).
% 11.43/4.35  tff(c_15270, plain, (![A_401, B_402]: (k2_xboole_0(A_401, k2_xboole_0(A_401, B_402))=k2_xboole_0(A_401, B_402))), inference(cnfTransformation, [status(thm)], [f_41])).
% 11.43/4.35  tff(c_15296, plain, (![A_392, B_393]: (k2_xboole_0(A_392, k2_xboole_0(B_393, A_392))=k2_xboole_0(A_392, B_393))), inference(superposition, [status(thm), theory('equality')], [c_15121, c_15270])).
% 11.43/4.35  tff(c_19119, plain, (![B_538, A_539]: (k5_xboole_0(B_538, k2_xboole_0(A_539, B_538))=k4_xboole_0(A_539, B_538))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_19008])).
% 11.43/4.35  tff(c_15601, plain, (![A_424, B_425]: (k5_xboole_0(k2_xboole_0(A_424, B_425), k5_xboole_0(A_424, B_425))=k3_xboole_0(A_424, B_425))), inference(superposition, [status(thm), theory('equality')], [c_15592, c_2])).
% 11.43/4.35  tff(c_19125, plain, (![B_538, A_539]: (k5_xboole_0(k2_xboole_0(B_538, k2_xboole_0(A_539, B_538)), k4_xboole_0(A_539, B_538))=k3_xboole_0(B_538, k2_xboole_0(A_539, B_538)))), inference(superposition, [status(thm), theory('equality')], [c_19119, c_15601])).
% 11.43/4.35  tff(c_19229, plain, (![B_540, A_541]: (k5_xboole_0(k2_xboole_0(B_540, A_541), k4_xboole_0(A_541, B_540))=B_540)), inference(demodulation, [status(thm), theory('equality')], [c_18589, c_15296, c_19125])).
% 11.43/4.35  tff(c_19313, plain, (k5_xboole_0(k2_xboole_0('#skF_4', k1_tarski('#skF_3')), k1_tarski('#skF_3'))='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_15265, c_19229])).
% 11.43/4.35  tff(c_17292, plain, (![A_514, A_512, B_513]: (k5_xboole_0(A_514, k5_xboole_0(A_512, B_513))=k5_xboole_0(A_512, k5_xboole_0(B_513, A_514)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_15756])).
% 11.43/4.35  tff(c_17696, plain, (![A_515, A_516]: (k5_xboole_0(k1_xboole_0, k5_xboole_0(A_515, A_516))=k5_xboole_0(A_516, A_515))), inference(superposition, [status(thm), theory('equality')], [c_15657, c_17292])).
% 11.43/4.35  tff(c_17723, plain, (![A_515, A_516]: (k5_xboole_0(k5_xboole_0(A_515, A_516), k5_xboole_0(A_516, A_515))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_17696, c_16036])).
% 11.43/4.35  tff(c_19362, plain, (k5_xboole_0('#skF_4', k5_xboole_0(k1_tarski('#skF_3'), k2_xboole_0('#skF_4', k1_tarski('#skF_3'))))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_19313, c_17723])).
% 11.43/4.35  tff(c_19409, plain, (k3_xboole_0('#skF_4', k1_tarski('#skF_3'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_16033, c_19100, c_19362])).
% 11.43/4.35  tff(c_16557, plain, (![A_465, B_466]: (k5_xboole_0(A_465, k4_xboole_0(A_465, B_466))=k3_xboole_0(A_465, B_466))), inference(superposition, [status(thm), theory('equality')], [c_8, c_15984])).
% 11.43/4.35  tff(c_16186, plain, (![A_443, B_444]: (k5_xboole_0(A_443, k5_xboole_0(B_444, A_443))=B_444)), inference(superposition, [status(thm), theory('equality')], [c_2, c_15984])).
% 11.43/4.35  tff(c_16189, plain, (![B_444, A_443]: (k5_xboole_0(k5_xboole_0(B_444, A_443), B_444)=A_443)), inference(superposition, [status(thm), theory('equality')], [c_16186, c_16036])).
% 11.43/4.35  tff(c_16566, plain, (![A_465, B_466]: (k5_xboole_0(k3_xboole_0(A_465, B_466), A_465)=k4_xboole_0(A_465, B_466))), inference(superposition, [status(thm), theory('equality')], [c_16557, c_16189])).
% 11.43/4.35  tff(c_19417, plain, (k4_xboole_0('#skF_4', k1_tarski('#skF_3'))=k5_xboole_0(k1_xboole_0, '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_19409, c_16566])).
% 11.43/4.35  tff(c_19429, plain, (k4_xboole_0('#skF_4', k1_tarski('#skF_3'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_15672, c_2, c_19417])).
% 11.43/4.35  tff(c_54, plain, (![C_80, B_79]: (~r2_hidden(C_80, k4_xboole_0(B_79, k1_tarski(C_80))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 11.43/4.35  tff(c_19460, plain, (~r2_hidden('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_19429, c_54])).
% 11.43/4.35  tff(c_19471, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_15071, c_19460])).
% 11.43/4.35  tff(c_19472, plain, (r2_hidden('#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_60])).
% 11.43/4.35  tff(c_20653, plain, (![A_606, B_607]: (k5_xboole_0(k5_xboole_0(A_606, B_607), k2_xboole_0(A_606, B_607))=k3_xboole_0(A_606, B_607))), inference(cnfTransformation, [status(thm)], [f_51])).
% 11.43/4.35  tff(c_20741, plain, (![A_3]: (k5_xboole_0(k5_xboole_0(A_3, A_3), A_3)=k3_xboole_0(A_3, A_3))), inference(superposition, [status(thm), theory('equality')], [c_4, c_20653])).
% 11.43/4.35  tff(c_20758, plain, (![A_608]: (k5_xboole_0(k1_xboole_0, A_608)=A_608)), inference(demodulation, [status(thm), theory('equality')], [c_22, c_6, c_20741])).
% 11.43/4.35  tff(c_20782, plain, (![A_608]: (k5_xboole_0(A_608, k1_xboole_0)=A_608)), inference(superposition, [status(thm), theory('equality')], [c_20758, c_2])).
% 11.43/4.35  tff(c_20752, plain, (![A_3]: (k5_xboole_0(k1_xboole_0, A_3)=A_3)), inference(demodulation, [status(thm), theory('equality')], [c_22, c_6, c_20741])).
% 11.43/4.35  tff(c_20108, plain, (![A_592, B_593, C_594]: (k5_xboole_0(k5_xboole_0(A_592, B_593), C_594)=k5_xboole_0(A_592, k5_xboole_0(B_593, C_594)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 11.43/4.35  tff(c_20158, plain, (![A_22, C_594]: (k5_xboole_0(A_22, k5_xboole_0(A_22, C_594))=k5_xboole_0(k1_xboole_0, C_594))), inference(superposition, [status(thm), theory('equality')], [c_22, c_20108])).
% 11.43/4.35  tff(c_21014, plain, (![A_620, C_621]: (k5_xboole_0(A_620, k5_xboole_0(A_620, C_621))=C_621)), inference(demodulation, [status(thm), theory('equality')], [c_20752, c_20158])).
% 11.43/4.35  tff(c_21063, plain, (![A_7, B_8]: (k5_xboole_0(A_7, k4_xboole_0(A_7, B_8))=k3_xboole_0(A_7, B_8))), inference(superposition, [status(thm), theory('equality')], [c_8, c_21014])).
% 11.43/4.35  tff(c_20, plain, (![A_19, B_20, C_21]: (k5_xboole_0(k5_xboole_0(A_19, B_20), C_21)=k5_xboole_0(A_19, k5_xboole_0(B_20, C_21)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 11.43/4.35  tff(c_24788, plain, (![A_717, B_718]: (k5_xboole_0(A_717, k5_xboole_0(B_718, k2_xboole_0(A_717, B_718)))=k3_xboole_0(A_717, B_718))), inference(superposition, [status(thm), theory('equality')], [c_20653, c_20])).
% 11.43/4.35  tff(c_20755, plain, (![A_22, C_594]: (k5_xboole_0(A_22, k5_xboole_0(A_22, C_594))=C_594)), inference(demodulation, [status(thm), theory('equality')], [c_20752, c_20158])).
% 11.43/4.35  tff(c_24841, plain, (![B_718, A_717]: (k5_xboole_0(B_718, k2_xboole_0(A_717, B_718))=k5_xboole_0(A_717, k3_xboole_0(A_717, B_718)))), inference(superposition, [status(thm), theory('equality')], [c_24788, c_20755])).
% 11.43/4.35  tff(c_24945, plain, (![B_718, A_717]: (k5_xboole_0(B_718, k2_xboole_0(A_717, B_718))=k4_xboole_0(A_717, B_718))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_24841])).
% 11.43/4.35  tff(c_19473, plain, (r2_hidden('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_60])).
% 11.43/4.35  tff(c_64, plain, (~r2_hidden('#skF_1', '#skF_2') | k4_xboole_0(k1_tarski('#skF_3'), '#skF_4')=k1_tarski('#skF_3')), inference(cnfTransformation, [status(thm)], [f_93])).
% 11.43/4.35  tff(c_19671, plain, (k4_xboole_0(k1_tarski('#skF_3'), '#skF_4')=k1_tarski('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_19473, c_64])).
% 11.43/4.35  tff(c_19484, plain, (![A_546, B_547]: (k3_tarski(k2_tarski(A_546, B_547))=k2_xboole_0(A_546, B_547))), inference(cnfTransformation, [status(thm)], [f_75])).
% 11.43/4.35  tff(c_19513, plain, (![B_549, A_550]: (k3_tarski(k2_tarski(B_549, A_550))=k2_xboole_0(A_550, B_549))), inference(superposition, [status(thm), theory('equality')], [c_26, c_19484])).
% 11.43/4.35  tff(c_19519, plain, (![B_549, A_550]: (k2_xboole_0(B_549, A_550)=k2_xboole_0(A_550, B_549))), inference(superposition, [status(thm), theory('equality')], [c_19513, c_48])).
% 11.43/4.35  tff(c_21069, plain, (![B_2, A_1]: (k5_xboole_0(B_2, k5_xboole_0(A_1, B_2))=A_1)), inference(superposition, [status(thm), theory('equality')], [c_2, c_21014])).
% 11.43/4.35  tff(c_22275, plain, (![B_682, A_683]: (k5_xboole_0(k5_xboole_0(B_682, A_683), k2_xboole_0(A_683, B_682))=k3_xboole_0(A_683, B_682))), inference(superposition, [status(thm), theory('equality')], [c_2, c_20653])).
% 11.43/4.35  tff(c_22393, plain, (![A_15, B_16]: (k5_xboole_0(k5_xboole_0(k2_xboole_0(A_15, B_16), A_15), k2_xboole_0(A_15, B_16))=k3_xboole_0(A_15, k2_xboole_0(A_15, B_16)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_22275])).
% 11.43/4.35  tff(c_22455, plain, (![A_684, B_685]: (k3_xboole_0(A_684, k2_xboole_0(A_684, B_685))=A_684)), inference(demodulation, [status(thm), theory('equality')], [c_21069, c_2, c_2, c_22393])).
% 11.43/4.35  tff(c_22505, plain, (![A_550, B_549]: (k3_xboole_0(A_550, k2_xboole_0(B_549, A_550))=A_550)), inference(superposition, [status(thm), theory('equality')], [c_19519, c_22455])).
% 11.43/4.35  tff(c_19719, plain, (![A_561, B_562]: (k2_xboole_0(A_561, k2_xboole_0(A_561, B_562))=k2_xboole_0(A_561, B_562))), inference(cnfTransformation, [status(thm)], [f_41])).
% 11.43/4.35  tff(c_19748, plain, (![A_550, B_549]: (k2_xboole_0(A_550, k2_xboole_0(B_549, A_550))=k2_xboole_0(A_550, B_549))), inference(superposition, [status(thm), theory('equality')], [c_19519, c_19719])).
% 11.43/4.35  tff(c_24964, plain, (![B_719, A_720]: (k5_xboole_0(B_719, k2_xboole_0(A_720, B_719))=k4_xboole_0(A_720, B_719))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_24841])).
% 11.43/4.35  tff(c_20677, plain, (![A_606, B_607]: (k5_xboole_0(k2_xboole_0(A_606, B_607), k5_xboole_0(A_606, B_607))=k3_xboole_0(A_606, B_607))), inference(superposition, [status(thm), theory('equality')], [c_20653, c_2])).
% 11.43/4.35  tff(c_24973, plain, (![B_719, A_720]: (k5_xboole_0(k2_xboole_0(B_719, k2_xboole_0(A_720, B_719)), k4_xboole_0(A_720, B_719))=k3_xboole_0(B_719, k2_xboole_0(A_720, B_719)))), inference(superposition, [status(thm), theory('equality')], [c_24964, c_20677])).
% 11.43/4.35  tff(c_25092, plain, (![B_721, A_722]: (k5_xboole_0(k2_xboole_0(B_721, A_722), k4_xboole_0(A_722, B_721))=B_721)), inference(demodulation, [status(thm), theory('equality')], [c_22505, c_19748, c_24973])).
% 11.43/4.35  tff(c_25188, plain, (k5_xboole_0(k2_xboole_0('#skF_4', k1_tarski('#skF_3')), k1_tarski('#skF_3'))='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_19671, c_25092])).
% 11.43/4.35  tff(c_22881, plain, (![A_697, A_695, B_696]: (k5_xboole_0(A_697, k5_xboole_0(A_695, B_696))=k5_xboole_0(A_695, k5_xboole_0(B_696, A_697)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_20108])).
% 11.43/4.35  tff(c_23330, plain, (![A_698, A_699]: (k5_xboole_0(k1_xboole_0, k5_xboole_0(A_698, A_699))=k5_xboole_0(A_699, A_698))), inference(superposition, [status(thm), theory('equality')], [c_20752, c_22881])).
% 11.43/4.35  tff(c_23363, plain, (![A_698, A_699]: (k5_xboole_0(k5_xboole_0(A_698, A_699), k5_xboole_0(A_699, A_698))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_23330, c_21069])).
% 11.43/4.35  tff(c_25246, plain, (k5_xboole_0('#skF_4', k5_xboole_0(k1_tarski('#skF_3'), k2_xboole_0('#skF_4', k1_tarski('#skF_3'))))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_25188, c_23363])).
% 11.43/4.35  tff(c_25299, plain, (k3_xboole_0('#skF_4', k1_tarski('#skF_3'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_21063, c_24945, c_25246])).
% 11.43/4.35  tff(c_21436, plain, (![A_648, B_649]: (k5_xboole_0(A_648, k4_xboole_0(A_648, B_649))=k3_xboole_0(A_648, B_649))), inference(superposition, [status(thm), theory('equality')], [c_8, c_21014])).
% 11.43/4.35  tff(c_21101, plain, (![B_629, A_630]: (k5_xboole_0(B_629, k5_xboole_0(A_630, B_629))=A_630)), inference(superposition, [status(thm), theory('equality')], [c_2, c_21014])).
% 11.43/4.35  tff(c_21104, plain, (![A_630, B_629]: (k5_xboole_0(k5_xboole_0(A_630, B_629), A_630)=B_629)), inference(superposition, [status(thm), theory('equality')], [c_21101, c_21069])).
% 11.43/4.35  tff(c_21442, plain, (![A_648, B_649]: (k5_xboole_0(k3_xboole_0(A_648, B_649), A_648)=k4_xboole_0(A_648, B_649))), inference(superposition, [status(thm), theory('equality')], [c_21436, c_21104])).
% 11.43/4.35  tff(c_25308, plain, (k4_xboole_0('#skF_4', k1_tarski('#skF_3'))=k5_xboole_0(k1_xboole_0, '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_25299, c_21442])).
% 11.43/4.35  tff(c_25320, plain, (k4_xboole_0('#skF_4', k1_tarski('#skF_3'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_20782, c_2, c_25308])).
% 11.43/4.35  tff(c_25354, plain, (~r2_hidden('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_25320, c_54])).
% 11.43/4.35  tff(c_25366, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_19472, c_25354])).
% 11.43/4.35  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.43/4.35  
% 11.43/4.35  Inference rules
% 11.43/4.35  ----------------------
% 11.43/4.35  #Ref     : 0
% 11.43/4.35  #Sup     : 6401
% 11.43/4.35  #Fact    : 0
% 11.43/4.35  #Define  : 0
% 11.43/4.35  #Split   : 2
% 11.43/4.35  #Chain   : 0
% 11.43/4.35  #Close   : 0
% 11.43/4.35  
% 11.43/4.35  Ordering : KBO
% 11.43/4.35  
% 11.43/4.35  Simplification rules
% 11.43/4.35  ----------------------
% 11.43/4.35  #Subsume      : 444
% 11.43/4.35  #Demod        : 6916
% 11.43/4.35  #Tautology    : 3571
% 11.43/4.35  #SimpNegUnit  : 24
% 11.43/4.35  #BackRed      : 10
% 11.43/4.35  
% 11.43/4.35  #Partial instantiations: 0
% 11.43/4.35  #Strategies tried      : 1
% 11.43/4.35  
% 11.43/4.35  Timing (in seconds)
% 11.43/4.35  ----------------------
% 11.43/4.35  Preprocessing        : 0.38
% 11.43/4.35  Parsing              : 0.20
% 11.43/4.35  CNF conversion       : 0.03
% 11.43/4.35  Main loop            : 3.15
% 11.43/4.35  Inferencing          : 0.72
% 11.43/4.35  Reduction            : 1.78
% 11.43/4.35  Demodulation         : 1.57
% 11.43/4.35  BG Simplification    : 0.10
% 11.43/4.35  Subsumption          : 0.40
% 11.43/4.35  Abstraction          : 0.17
% 11.43/4.35  MUC search           : 0.00
% 11.43/4.35  Cooper               : 0.00
% 11.43/4.35  Total                : 3.59
% 11.43/4.35  Index Insertion      : 0.00
% 11.43/4.35  Index Deletion       : 0.00
% 11.43/4.35  Index Matching       : 0.00
% 11.43/4.35  BG Taut test         : 0.00
%------------------------------------------------------------------------------

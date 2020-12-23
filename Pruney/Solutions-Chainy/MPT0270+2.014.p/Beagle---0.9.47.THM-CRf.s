%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:52:54 EST 2020

% Result     : Theorem 11.19s
% Output     : CNFRefutation 11.37s
% Verified   : 
% Statistics : Number of formulae       :  159 ( 539 expanded)
%              Number of leaves         :   37 ( 202 expanded)
%              Depth                    :   15
%              Number of atoms          :  150 ( 543 expanded)
%              Number of equality atoms :  123 ( 500 expanded)
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_zfmisc_1)).

tff(f_78,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_53,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_80,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_33,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_47,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_51,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_49,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k2_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

tff(f_41,axiom,(
    ! [A,B] : k2_xboole_0(A,k2_xboole_0(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => k4_xboole_0(k2_xboole_0(A,B),B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_87,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k4_xboole_0(B,k1_tarski(C)))
    <=> ( r2_hidden(A,B)
        & A != C ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_zfmisc_1)).

tff(c_60,plain,
    ( ~ r2_hidden('#skF_1','#skF_2')
    | r2_hidden('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_185,plain,(
    ~ r2_hidden('#skF_1','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_60])).

tff(c_48,plain,(
    ! [A_74,B_75] :
      ( r1_xboole_0(k1_tarski(A_74),B_75)
      | r2_hidden(A_74,B_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_26,plain,(
    ! [B_26,A_25] : k2_tarski(B_26,A_25) = k2_tarski(A_25,B_26) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_197,plain,(
    ! [A_96,B_97] : k3_tarski(k2_tarski(A_96,B_97)) = k2_xboole_0(A_96,B_97) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_250,plain,(
    ! [A_101,B_102] : k3_tarski(k2_tarski(A_101,B_102)) = k2_xboole_0(B_102,A_101) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_197])).

tff(c_50,plain,(
    ! [A_76,B_77] : k3_tarski(k2_tarski(A_76,B_77)) = k2_xboole_0(A_76,B_77) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_256,plain,(
    ! [B_102,A_101] : k2_xboole_0(B_102,A_101) = k2_xboole_0(A_101,B_102) ),
    inference(superposition,[status(thm),theory(equality)],[c_250,c_50])).

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

tff(c_5827,plain,(
    ! [B_102,A_101] : k5_xboole_0(B_102,k2_xboole_0(B_102,A_101)) = k4_xboole_0(A_101,B_102) ),
    inference(superposition,[status(thm),theory(equality)],[c_256,c_5725])).

tff(c_16,plain,(
    ! [A_15,B_16] : k2_xboole_0(A_15,k2_xboole_0(A_15,B_16)) = k2_xboole_0(A_15,B_16) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_6084,plain,(
    ! [B_280,A_281] : k5_xboole_0(B_280,k2_xboole_0(B_280,A_281)) = k4_xboole_0(A_281,B_280) ),
    inference(superposition,[status(thm),theory(equality)],[c_256,c_5725])).

tff(c_6200,plain,(
    ! [A_15,B_16] : k5_xboole_0(A_15,k2_xboole_0(A_15,B_16)) = k4_xboole_0(k2_xboole_0(A_15,B_16),A_15) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_6084])).

tff(c_6228,plain,(
    ! [A_15,B_16] : k4_xboole_0(k2_xboole_0(A_15,B_16),A_15) = k4_xboole_0(B_16,A_15) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5827,c_6200])).

tff(c_545,plain,(
    ! [A_118,B_119] :
      ( k4_xboole_0(k2_xboole_0(A_118,B_119),B_119) = A_118
      | ~ r1_xboole_0(A_118,B_119) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_582,plain,(
    ! [B_102,A_101] :
      ( k4_xboole_0(k2_xboole_0(B_102,A_101),B_102) = A_101
      | ~ r1_xboole_0(A_101,B_102) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_256,c_545])).

tff(c_8654,plain,(
    ! [A_321,B_322] :
      ( k4_xboole_0(A_321,B_322) = A_321
      | ~ r1_xboole_0(A_321,B_322) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6228,c_582])).

tff(c_14961,plain,(
    ! [A_383,B_384] :
      ( k4_xboole_0(k1_tarski(A_383),B_384) = k1_tarski(A_383)
      | r2_hidden(A_383,B_384) ) ),
    inference(resolution,[status(thm)],[c_48,c_8654])).

tff(c_58,plain,
    ( k4_xboole_0(k1_tarski('#skF_1'),'#skF_2') != k1_tarski('#skF_1')
    | r2_hidden('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_186,plain,(
    k4_xboole_0(k1_tarski('#skF_1'),'#skF_2') != k1_tarski('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_58])).

tff(c_15088,plain,(
    r2_hidden('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_14961,c_186])).

tff(c_15156,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_185,c_15088])).

tff(c_15157,plain,(
    r2_hidden('#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_15678,plain,(
    ! [A_424,B_425] : k5_xboole_0(k5_xboole_0(A_424,B_425),k2_xboole_0(A_424,B_425)) = k3_xboole_0(A_424,B_425) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_15732,plain,(
    ! [A_3] : k5_xboole_0(k5_xboole_0(A_3,A_3),A_3) = k3_xboole_0(A_3,A_3) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_15678])).

tff(c_15745,plain,(
    ! [A_426] : k5_xboole_0(k1_xboole_0,A_426) = A_426 ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_6,c_15732])).

tff(c_2,plain,(
    ! [B_2,A_1] : k5_xboole_0(B_2,A_1) = k5_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_15758,plain,(
    ! [A_426] : k5_xboole_0(A_426,k1_xboole_0) = A_426 ),
    inference(superposition,[status(thm),theory(equality)],[c_15745,c_2])).

tff(c_15743,plain,(
    ! [A_3] : k5_xboole_0(k1_xboole_0,A_3) = A_3 ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_6,c_15732])).

tff(c_15842,plain,(
    ! [A_428,B_429,C_430] : k5_xboole_0(k5_xboole_0(A_428,B_429),C_430) = k5_xboole_0(A_428,k5_xboole_0(B_429,C_430)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_15919,plain,(
    ! [A_22,C_430] : k5_xboole_0(A_22,k5_xboole_0(A_22,C_430)) = k5_xboole_0(k1_xboole_0,C_430) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_15842])).

tff(c_16070,plain,(
    ! [A_438,C_439] : k5_xboole_0(A_438,k5_xboole_0(A_438,C_439)) = C_439 ),
    inference(demodulation,[status(thm),theory(equality)],[c_15743,c_15919])).

tff(c_16119,plain,(
    ! [A_7,B_8] : k5_xboole_0(A_7,k4_xboole_0(A_7,B_8)) = k3_xboole_0(A_7,B_8) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_16070])).

tff(c_19051,plain,(
    ! [A_536,B_537] : k5_xboole_0(A_536,k5_xboole_0(B_537,k2_xboole_0(A_536,B_537))) = k3_xboole_0(A_536,B_537) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_15842])).

tff(c_15932,plain,(
    ! [A_22,C_430] : k5_xboole_0(A_22,k5_xboole_0(A_22,C_430)) = C_430 ),
    inference(demodulation,[status(thm),theory(equality)],[c_15743,c_15919])).

tff(c_19094,plain,(
    ! [B_537,A_536] : k5_xboole_0(B_537,k2_xboole_0(A_536,B_537)) = k5_xboole_0(A_536,k3_xboole_0(A_536,B_537)) ),
    inference(superposition,[status(thm),theory(equality)],[c_19051,c_15932])).

tff(c_19186,plain,(
    ! [B_537,A_536] : k5_xboole_0(B_537,k2_xboole_0(A_536,B_537)) = k4_xboole_0(A_536,B_537) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_19094])).

tff(c_15158,plain,(
    k4_xboole_0(k1_tarski('#skF_1'),'#skF_2') = k1_tarski('#skF_1') ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_62,plain,
    ( k4_xboole_0(k1_tarski('#skF_1'),'#skF_2') != k1_tarski('#skF_1')
    | k4_xboole_0(k1_tarski('#skF_3'),'#skF_4') = k1_tarski('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_15364,plain,(
    k4_xboole_0(k1_tarski('#skF_3'),'#skF_4') = k1_tarski('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_15158,c_62])).

tff(c_15173,plain,(
    ! [A_389,B_390] : k3_tarski(k2_tarski(A_389,B_390)) = k2_xboole_0(A_389,B_390) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_15201,plain,(
    ! [B_392,A_393] : k3_tarski(k2_tarski(B_392,A_393)) = k2_xboole_0(A_393,B_392) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_15173])).

tff(c_15207,plain,(
    ! [B_392,A_393] : k2_xboole_0(B_392,A_393) = k2_xboole_0(A_393,B_392) ),
    inference(superposition,[status(thm),theory(equality)],[c_15201,c_50])).

tff(c_16122,plain,(
    ! [A_1,B_2] : k5_xboole_0(A_1,k5_xboole_0(B_2,A_1)) = B_2 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_16070])).

tff(c_18434,plain,(
    ! [A_523,B_524] : k5_xboole_0(k2_xboole_0(A_523,B_524),k5_xboole_0(A_523,B_524)) = k3_xboole_0(A_523,B_524) ),
    inference(superposition,[status(thm),theory(equality)],[c_15678,c_2])).

tff(c_18568,plain,(
    ! [A_15,B_16] : k5_xboole_0(k2_xboole_0(A_15,B_16),k5_xboole_0(A_15,k2_xboole_0(A_15,B_16))) = k3_xboole_0(A_15,k2_xboole_0(A_15,B_16)) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_18434])).

tff(c_18625,plain,(
    ! [A_525,B_526] : k3_xboole_0(A_525,k2_xboole_0(A_525,B_526)) = A_525 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16122,c_18568])).

tff(c_18675,plain,(
    ! [A_393,B_392] : k3_xboole_0(A_393,k2_xboole_0(B_392,A_393)) = A_393 ),
    inference(superposition,[status(thm),theory(equality)],[c_15207,c_18625])).

tff(c_15373,plain,(
    ! [A_400,B_401] : k2_xboole_0(A_400,k2_xboole_0(A_400,B_401)) = k2_xboole_0(A_400,B_401) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_15402,plain,(
    ! [A_393,B_392] : k2_xboole_0(A_393,k2_xboole_0(B_392,A_393)) = k2_xboole_0(A_393,B_392) ),
    inference(superposition,[status(thm),theory(equality)],[c_15207,c_15373])).

tff(c_19205,plain,(
    ! [B_538,A_539] : k5_xboole_0(B_538,k2_xboole_0(A_539,B_538)) = k4_xboole_0(A_539,B_538) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_19094])).

tff(c_15687,plain,(
    ! [A_424,B_425] : k5_xboole_0(k2_xboole_0(A_424,B_425),k5_xboole_0(A_424,B_425)) = k3_xboole_0(A_424,B_425) ),
    inference(superposition,[status(thm),theory(equality)],[c_15678,c_2])).

tff(c_19211,plain,(
    ! [B_538,A_539] : k5_xboole_0(k2_xboole_0(B_538,k2_xboole_0(A_539,B_538)),k4_xboole_0(A_539,B_538)) = k3_xboole_0(B_538,k2_xboole_0(A_539,B_538)) ),
    inference(superposition,[status(thm),theory(equality)],[c_19205,c_15687])).

tff(c_19315,plain,(
    ! [B_540,A_541] : k5_xboole_0(k2_xboole_0(B_540,A_541),k4_xboole_0(A_541,B_540)) = B_540 ),
    inference(demodulation,[status(thm),theory(equality)],[c_18675,c_15402,c_19211])).

tff(c_19396,plain,(
    k5_xboole_0(k2_xboole_0('#skF_4',k1_tarski('#skF_3')),k1_tarski('#skF_3')) = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_15364,c_19315])).

tff(c_17378,plain,(
    ! [A_514,A_512,B_513] : k5_xboole_0(A_514,k5_xboole_0(A_512,B_513)) = k5_xboole_0(A_512,k5_xboole_0(B_513,A_514)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_15842])).

tff(c_17782,plain,(
    ! [A_515,A_516] : k5_xboole_0(k1_xboole_0,k5_xboole_0(A_515,A_516)) = k5_xboole_0(A_516,A_515) ),
    inference(superposition,[status(thm),theory(equality)],[c_15743,c_17378])).

tff(c_17809,plain,(
    ! [A_515,A_516] : k5_xboole_0(k5_xboole_0(A_515,A_516),k5_xboole_0(A_516,A_515)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_17782,c_16122])).

tff(c_19448,plain,(
    k5_xboole_0('#skF_4',k5_xboole_0(k1_tarski('#skF_3'),k2_xboole_0('#skF_4',k1_tarski('#skF_3')))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_19396,c_17809])).

tff(c_19495,plain,(
    k3_xboole_0('#skF_4',k1_tarski('#skF_3')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16119,c_19186,c_19448])).

tff(c_16643,plain,(
    ! [A_465,B_466] : k5_xboole_0(A_465,k4_xboole_0(A_465,B_466)) = k3_xboole_0(A_465,B_466) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_16070])).

tff(c_16272,plain,(
    ! [A_443,B_444] : k5_xboole_0(A_443,k5_xboole_0(B_444,A_443)) = B_444 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_16070])).

tff(c_16275,plain,(
    ! [B_444,A_443] : k5_xboole_0(k5_xboole_0(B_444,A_443),B_444) = A_443 ),
    inference(superposition,[status(thm),theory(equality)],[c_16272,c_16122])).

tff(c_16652,plain,(
    ! [A_465,B_466] : k5_xboole_0(k3_xboole_0(A_465,B_466),A_465) = k4_xboole_0(A_465,B_466) ),
    inference(superposition,[status(thm),theory(equality)],[c_16643,c_16275])).

tff(c_19503,plain,(
    k4_xboole_0('#skF_4',k1_tarski('#skF_3')) = k5_xboole_0(k1_xboole_0,'#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_19495,c_16652])).

tff(c_19515,plain,(
    k4_xboole_0('#skF_4',k1_tarski('#skF_3')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_15758,c_2,c_19503])).

tff(c_54,plain,(
    ! [C_80,B_79] : ~ r2_hidden(C_80,k4_xboole_0(B_79,k1_tarski(C_80))) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_19546,plain,(
    ~ r2_hidden('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_19515,c_54])).

tff(c_19557,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_15157,c_19546])).

tff(c_19558,plain,(
    r2_hidden('#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_19559,plain,(
    r2_hidden('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_64,plain,
    ( ~ r2_hidden('#skF_1','#skF_2')
    | k4_xboole_0(k1_tarski('#skF_3'),'#skF_4') = k1_tarski('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_19757,plain,(
    k4_xboole_0(k1_tarski('#skF_3'),'#skF_4') = k1_tarski('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_19559,c_64])).

tff(c_19560,plain,(
    ! [A_542,B_543] : k3_tarski(k2_tarski(A_542,B_543)) = k2_xboole_0(A_542,B_543) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_19599,plain,(
    ! [B_549,A_550] : k3_tarski(k2_tarski(B_549,A_550)) = k2_xboole_0(A_550,B_549) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_19560])).

tff(c_19605,plain,(
    ! [B_549,A_550] : k2_xboole_0(B_549,A_550) = k2_xboole_0(A_550,B_549) ),
    inference(superposition,[status(thm),theory(equality)],[c_19599,c_50])).

tff(c_20350,plain,(
    ! [A_592,B_593] : k5_xboole_0(k5_xboole_0(A_592,B_593),k2_xboole_0(A_592,B_593)) = k3_xboole_0(A_592,B_593) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_20429,plain,(
    ! [A_3] : k5_xboole_0(k5_xboole_0(A_3,A_3),A_3) = k3_xboole_0(A_3,A_3) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_20350])).

tff(c_20444,plain,(
    ! [A_594] : k5_xboole_0(k1_xboole_0,A_594) = A_594 ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_6,c_20429])).

tff(c_20479,plain,(
    ! [A_594] : k5_xboole_0(A_594,k1_xboole_0) = A_594 ),
    inference(superposition,[status(thm),theory(equality)],[c_20444,c_2])).

tff(c_20120,plain,(
    ! [A_585,B_586,C_587] : k5_xboole_0(k5_xboole_0(A_585,B_586),C_587) = k5_xboole_0(A_585,k5_xboole_0(B_586,C_587)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_20140,plain,(
    ! [A_585,B_586] : k5_xboole_0(A_585,k5_xboole_0(B_586,k5_xboole_0(A_585,B_586))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_20120,c_22])).

tff(c_20440,plain,(
    ! [A_3] : k5_xboole_0(k1_xboole_0,A_3) = A_3 ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_6,c_20429])).

tff(c_20170,plain,(
    ! [A_22,C_587] : k5_xboole_0(A_22,k5_xboole_0(A_22,C_587)) = k5_xboole_0(k1_xboole_0,C_587) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_20120])).

tff(c_20863,plain,(
    ! [A_611,C_612] : k5_xboole_0(A_611,k5_xboole_0(A_611,C_612)) = C_612 ),
    inference(demodulation,[status(thm),theory(equality)],[c_20440,c_20170])).

tff(c_20916,plain,(
    ! [B_586,A_585] : k5_xboole_0(B_586,k5_xboole_0(A_585,B_586)) = k5_xboole_0(A_585,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_20140,c_20863])).

tff(c_20953,plain,(
    ! [B_586,A_585] : k5_xboole_0(B_586,k5_xboole_0(A_585,B_586)) = A_585 ),
    inference(demodulation,[status(thm),theory(equality)],[c_20479,c_20916])).

tff(c_22345,plain,(
    ! [B_684,A_685] : k5_xboole_0(k5_xboole_0(B_684,A_685),k2_xboole_0(A_685,B_684)) = k3_xboole_0(A_685,B_684) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_20350])).

tff(c_22466,plain,(
    ! [A_15,B_16] : k5_xboole_0(k5_xboole_0(k2_xboole_0(A_15,B_16),A_15),k2_xboole_0(A_15,B_16)) = k3_xboole_0(A_15,k2_xboole_0(A_15,B_16)) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_22345])).

tff(c_22526,plain,(
    ! [A_686,B_687] : k3_xboole_0(A_686,k2_xboole_0(A_686,B_687)) = A_686 ),
    inference(demodulation,[status(thm),theory(equality)],[c_20953,c_2,c_2,c_22466])).

tff(c_22576,plain,(
    ! [A_550,B_549] : k3_xboole_0(A_550,k2_xboole_0(B_549,A_550)) = A_550 ),
    inference(superposition,[status(thm),theory(equality)],[c_19605,c_22526])).

tff(c_19767,plain,(
    ! [A_557,B_558] : k2_xboole_0(A_557,k2_xboole_0(A_557,B_558)) = k2_xboole_0(A_557,B_558) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_19799,plain,(
    ! [B_549,A_550] : k2_xboole_0(B_549,k2_xboole_0(A_550,B_549)) = k2_xboole_0(B_549,A_550) ),
    inference(superposition,[status(thm),theory(equality)],[c_19605,c_19767])).

tff(c_20,plain,(
    ! [A_19,B_20,C_21] : k5_xboole_0(k5_xboole_0(A_19,B_20),C_21) = k5_xboole_0(A_19,k5_xboole_0(B_20,C_21)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_25603,plain,(
    ! [A_729,B_730] : k5_xboole_0(A_729,k5_xboole_0(B_730,k2_xboole_0(A_729,B_730))) = k3_xboole_0(A_729,B_730) ),
    inference(superposition,[status(thm),theory(equality)],[c_20350,c_20])).

tff(c_20862,plain,(
    ! [A_22,C_587] : k5_xboole_0(A_22,k5_xboole_0(A_22,C_587)) = C_587 ),
    inference(demodulation,[status(thm),theory(equality)],[c_20440,c_20170])).

tff(c_25656,plain,(
    ! [B_730,A_729] : k5_xboole_0(B_730,k2_xboole_0(A_729,B_730)) = k5_xboole_0(A_729,k3_xboole_0(A_729,B_730)) ),
    inference(superposition,[status(thm),theory(equality)],[c_25603,c_20862])).

tff(c_25787,plain,(
    ! [B_731,A_732] : k5_xboole_0(B_731,k2_xboole_0(A_732,B_731)) = k4_xboole_0(A_732,B_731) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_25656])).

tff(c_20420,plain,(
    ! [A_592,B_593] : k5_xboole_0(k2_xboole_0(A_592,B_593),k5_xboole_0(A_592,B_593)) = k3_xboole_0(A_592,B_593) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_20350])).

tff(c_25811,plain,(
    ! [B_731,A_732] : k5_xboole_0(k2_xboole_0(B_731,k2_xboole_0(A_732,B_731)),k4_xboole_0(A_732,B_731)) = k3_xboole_0(B_731,k2_xboole_0(A_732,B_731)) ),
    inference(superposition,[status(thm),theory(equality)],[c_25787,c_20420])).

tff(c_26077,plain,(
    ! [B_735,A_736] : k5_xboole_0(k2_xboole_0(B_735,A_736),k4_xboole_0(A_736,B_735)) = B_735 ),
    inference(demodulation,[status(thm),theory(equality)],[c_22576,c_19799,c_25811])).

tff(c_26179,plain,(
    k5_xboole_0(k2_xboole_0('#skF_4',k1_tarski('#skF_3')),k1_tarski('#skF_3')) = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_19757,c_26077])).

tff(c_24030,plain,(
    ! [C_715,A_716,B_717] : k5_xboole_0(C_715,k5_xboole_0(A_716,B_717)) = k5_xboole_0(A_716,k5_xboole_0(B_717,C_715)) ),
    inference(superposition,[status(thm),theory(equality)],[c_20120,c_2])).

tff(c_24371,plain,(
    ! [A_3,C_715] : k5_xboole_0(k1_xboole_0,k5_xboole_0(A_3,C_715)) = k5_xboole_0(C_715,A_3) ),
    inference(superposition,[status(thm),theory(equality)],[c_20440,c_24030])).

tff(c_25802,plain,(
    ! [A_732,B_731] : k5_xboole_0(k2_xboole_0(A_732,B_731),B_731) = k5_xboole_0(k1_xboole_0,k4_xboole_0(A_732,B_731)) ),
    inference(superposition,[status(thm),theory(equality)],[c_25787,c_24371])).

tff(c_25909,plain,(
    ! [A_732,B_731] : k5_xboole_0(k2_xboole_0(A_732,B_731),B_731) = k4_xboole_0(A_732,B_731) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20440,c_25802])).

tff(c_26228,plain,(
    k4_xboole_0('#skF_4',k1_tarski('#skF_3')) = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_26179,c_25909])).

tff(c_26329,plain,(
    ~ r2_hidden('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_26228,c_54])).

tff(c_26339,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_19558,c_26329])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n009.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 15:53:41 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 11.19/4.32  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.37/4.33  
% 11.37/4.33  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.37/4.34  %$ r2_hidden > r1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 11.37/4.34  
% 11.37/4.34  %Foreground sorts:
% 11.37/4.34  
% 11.37/4.34  
% 11.37/4.34  %Background operators:
% 11.37/4.34  
% 11.37/4.34  
% 11.37/4.34  %Foreground operators:
% 11.37/4.34  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 11.37/4.34  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 11.37/4.34  tff(k1_tarski, type, k1_tarski: $i > $i).
% 11.37/4.34  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 11.37/4.34  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 11.37/4.34  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 11.37/4.34  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 11.37/4.34  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 11.37/4.34  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 11.37/4.34  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 11.37/4.34  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 11.37/4.34  tff('#skF_2', type, '#skF_2': $i).
% 11.37/4.34  tff('#skF_3', type, '#skF_3': $i).
% 11.37/4.34  tff('#skF_1', type, '#skF_1': $i).
% 11.37/4.34  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 11.37/4.34  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 11.37/4.34  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 11.37/4.34  tff(k3_tarski, type, k3_tarski: $i > $i).
% 11.37/4.34  tff('#skF_4', type, '#skF_4': $i).
% 11.37/4.34  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 11.37/4.34  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 11.37/4.34  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 11.37/4.34  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 11.37/4.34  
% 11.37/4.37  tff(f_93, negated_conjecture, ~(![A, B]: ((k4_xboole_0(k1_tarski(A), B) = k1_tarski(A)) <=> ~r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t67_zfmisc_1)).
% 11.37/4.37  tff(f_78, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 11.37/4.37  tff(f_53, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 11.37/4.37  tff(f_80, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 11.37/4.37  tff(f_33, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 11.37/4.37  tff(f_47, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_xboole_1)).
% 11.37/4.37  tff(f_51, axiom, (![A, B]: (k3_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k2_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t95_xboole_1)).
% 11.37/4.37  tff(f_31, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 11.37/4.37  tff(f_49, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 11.37/4.37  tff(f_29, axiom, (![A, B]: (k2_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 11.37/4.37  tff(f_41, axiom, (![A, B]: (k2_xboole_0(A, k2_xboole_0(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_xboole_1)).
% 11.37/4.37  tff(f_45, axiom, (![A, B]: (r1_xboole_0(A, B) => (k4_xboole_0(k2_xboole_0(A, B), B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t88_xboole_1)).
% 11.37/4.37  tff(f_27, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 11.37/4.37  tff(f_87, axiom, (![A, B, C]: (r2_hidden(A, k4_xboole_0(B, k1_tarski(C))) <=> (r2_hidden(A, B) & ~(A = C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_zfmisc_1)).
% 11.37/4.37  tff(c_60, plain, (~r2_hidden('#skF_1', '#skF_2') | r2_hidden('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_93])).
% 11.37/4.37  tff(c_185, plain, (~r2_hidden('#skF_1', '#skF_2')), inference(splitLeft, [status(thm)], [c_60])).
% 11.37/4.37  tff(c_48, plain, (![A_74, B_75]: (r1_xboole_0(k1_tarski(A_74), B_75) | r2_hidden(A_74, B_75))), inference(cnfTransformation, [status(thm)], [f_78])).
% 11.37/4.37  tff(c_26, plain, (![B_26, A_25]: (k2_tarski(B_26, A_25)=k2_tarski(A_25, B_26))), inference(cnfTransformation, [status(thm)], [f_53])).
% 11.37/4.37  tff(c_197, plain, (![A_96, B_97]: (k3_tarski(k2_tarski(A_96, B_97))=k2_xboole_0(A_96, B_97))), inference(cnfTransformation, [status(thm)], [f_80])).
% 11.37/4.37  tff(c_250, plain, (![A_101, B_102]: (k3_tarski(k2_tarski(A_101, B_102))=k2_xboole_0(B_102, A_101))), inference(superposition, [status(thm), theory('equality')], [c_26, c_197])).
% 11.37/4.37  tff(c_50, plain, (![A_76, B_77]: (k3_tarski(k2_tarski(A_76, B_77))=k2_xboole_0(A_76, B_77))), inference(cnfTransformation, [status(thm)], [f_80])).
% 11.37/4.37  tff(c_256, plain, (![B_102, A_101]: (k2_xboole_0(B_102, A_101)=k2_xboole_0(A_101, B_102))), inference(superposition, [status(thm), theory('equality')], [c_250, c_50])).
% 11.37/4.37  tff(c_8, plain, (![A_7, B_8]: (k5_xboole_0(A_7, k3_xboole_0(A_7, B_8))=k4_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_33])).
% 11.37/4.37  tff(c_1125, plain, (![A_147, B_148, C_149]: (k5_xboole_0(k5_xboole_0(A_147, B_148), C_149)=k5_xboole_0(A_147, k5_xboole_0(B_148, C_149)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 11.37/4.37  tff(c_24, plain, (![A_23, B_24]: (k5_xboole_0(k5_xboole_0(A_23, B_24), k2_xboole_0(A_23, B_24))=k3_xboole_0(A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_51])).
% 11.37/4.37  tff(c_5545, plain, (![A_270, B_271]: (k5_xboole_0(A_270, k5_xboole_0(B_271, k2_xboole_0(A_270, B_271)))=k3_xboole_0(A_270, B_271))), inference(superposition, [status(thm), theory('equality')], [c_1125, c_24])).
% 11.37/4.37  tff(c_6, plain, (![A_5]: (k3_xboole_0(A_5, A_5)=A_5)), inference(cnfTransformation, [status(thm)], [f_31])).
% 11.37/4.37  tff(c_22, plain, (![A_22]: (k5_xboole_0(A_22, A_22)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_49])).
% 11.37/4.37  tff(c_4, plain, (![A_3]: (k2_xboole_0(A_3, A_3)=A_3)), inference(cnfTransformation, [status(thm)], [f_29])).
% 11.37/4.37  tff(c_692, plain, (![A_133, B_134]: (k5_xboole_0(k5_xboole_0(A_133, B_134), k2_xboole_0(A_133, B_134))=k3_xboole_0(A_133, B_134))), inference(cnfTransformation, [status(thm)], [f_51])).
% 11.37/4.37  tff(c_746, plain, (![A_3]: (k5_xboole_0(k5_xboole_0(A_3, A_3), A_3)=k3_xboole_0(A_3, A_3))), inference(superposition, [status(thm), theory('equality')], [c_4, c_692])).
% 11.37/4.37  tff(c_757, plain, (![A_3]: (k5_xboole_0(k1_xboole_0, A_3)=A_3)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_22, c_746])).
% 11.37/4.37  tff(c_1202, plain, (![A_22, C_149]: (k5_xboole_0(A_22, k5_xboole_0(A_22, C_149))=k5_xboole_0(k1_xboole_0, C_149))), inference(superposition, [status(thm), theory('equality')], [c_22, c_1125])).
% 11.37/4.37  tff(c_1215, plain, (![A_22, C_149]: (k5_xboole_0(A_22, k5_xboole_0(A_22, C_149))=C_149)), inference(demodulation, [status(thm), theory('equality')], [c_757, c_1202])).
% 11.37/4.37  tff(c_5595, plain, (![B_271, A_270]: (k5_xboole_0(B_271, k2_xboole_0(A_270, B_271))=k5_xboole_0(A_270, k3_xboole_0(A_270, B_271)))), inference(superposition, [status(thm), theory('equality')], [c_5545, c_1215])).
% 11.37/4.37  tff(c_5725, plain, (![B_272, A_273]: (k5_xboole_0(B_272, k2_xboole_0(A_273, B_272))=k4_xboole_0(A_273, B_272))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_5595])).
% 11.37/4.37  tff(c_5827, plain, (![B_102, A_101]: (k5_xboole_0(B_102, k2_xboole_0(B_102, A_101))=k4_xboole_0(A_101, B_102))), inference(superposition, [status(thm), theory('equality')], [c_256, c_5725])).
% 11.37/4.37  tff(c_16, plain, (![A_15, B_16]: (k2_xboole_0(A_15, k2_xboole_0(A_15, B_16))=k2_xboole_0(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_41])).
% 11.37/4.37  tff(c_6084, plain, (![B_280, A_281]: (k5_xboole_0(B_280, k2_xboole_0(B_280, A_281))=k4_xboole_0(A_281, B_280))), inference(superposition, [status(thm), theory('equality')], [c_256, c_5725])).
% 11.37/4.37  tff(c_6200, plain, (![A_15, B_16]: (k5_xboole_0(A_15, k2_xboole_0(A_15, B_16))=k4_xboole_0(k2_xboole_0(A_15, B_16), A_15))), inference(superposition, [status(thm), theory('equality')], [c_16, c_6084])).
% 11.37/4.37  tff(c_6228, plain, (![A_15, B_16]: (k4_xboole_0(k2_xboole_0(A_15, B_16), A_15)=k4_xboole_0(B_16, A_15))), inference(demodulation, [status(thm), theory('equality')], [c_5827, c_6200])).
% 11.37/4.37  tff(c_545, plain, (![A_118, B_119]: (k4_xboole_0(k2_xboole_0(A_118, B_119), B_119)=A_118 | ~r1_xboole_0(A_118, B_119))), inference(cnfTransformation, [status(thm)], [f_45])).
% 11.37/4.37  tff(c_582, plain, (![B_102, A_101]: (k4_xboole_0(k2_xboole_0(B_102, A_101), B_102)=A_101 | ~r1_xboole_0(A_101, B_102))), inference(superposition, [status(thm), theory('equality')], [c_256, c_545])).
% 11.37/4.37  tff(c_8654, plain, (![A_321, B_322]: (k4_xboole_0(A_321, B_322)=A_321 | ~r1_xboole_0(A_321, B_322))), inference(demodulation, [status(thm), theory('equality')], [c_6228, c_582])).
% 11.37/4.37  tff(c_14961, plain, (![A_383, B_384]: (k4_xboole_0(k1_tarski(A_383), B_384)=k1_tarski(A_383) | r2_hidden(A_383, B_384))), inference(resolution, [status(thm)], [c_48, c_8654])).
% 11.37/4.37  tff(c_58, plain, (k4_xboole_0(k1_tarski('#skF_1'), '#skF_2')!=k1_tarski('#skF_1') | r2_hidden('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_93])).
% 11.37/4.37  tff(c_186, plain, (k4_xboole_0(k1_tarski('#skF_1'), '#skF_2')!=k1_tarski('#skF_1')), inference(splitLeft, [status(thm)], [c_58])).
% 11.37/4.37  tff(c_15088, plain, (r2_hidden('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_14961, c_186])).
% 11.37/4.37  tff(c_15156, plain, $false, inference(negUnitSimplification, [status(thm)], [c_185, c_15088])).
% 11.37/4.37  tff(c_15157, plain, (r2_hidden('#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_58])).
% 11.37/4.37  tff(c_15678, plain, (![A_424, B_425]: (k5_xboole_0(k5_xboole_0(A_424, B_425), k2_xboole_0(A_424, B_425))=k3_xboole_0(A_424, B_425))), inference(cnfTransformation, [status(thm)], [f_51])).
% 11.37/4.37  tff(c_15732, plain, (![A_3]: (k5_xboole_0(k5_xboole_0(A_3, A_3), A_3)=k3_xboole_0(A_3, A_3))), inference(superposition, [status(thm), theory('equality')], [c_4, c_15678])).
% 11.37/4.37  tff(c_15745, plain, (![A_426]: (k5_xboole_0(k1_xboole_0, A_426)=A_426)), inference(demodulation, [status(thm), theory('equality')], [c_22, c_6, c_15732])).
% 11.37/4.37  tff(c_2, plain, (![B_2, A_1]: (k5_xboole_0(B_2, A_1)=k5_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 11.37/4.37  tff(c_15758, plain, (![A_426]: (k5_xboole_0(A_426, k1_xboole_0)=A_426)), inference(superposition, [status(thm), theory('equality')], [c_15745, c_2])).
% 11.37/4.37  tff(c_15743, plain, (![A_3]: (k5_xboole_0(k1_xboole_0, A_3)=A_3)), inference(demodulation, [status(thm), theory('equality')], [c_22, c_6, c_15732])).
% 11.37/4.37  tff(c_15842, plain, (![A_428, B_429, C_430]: (k5_xboole_0(k5_xboole_0(A_428, B_429), C_430)=k5_xboole_0(A_428, k5_xboole_0(B_429, C_430)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 11.37/4.37  tff(c_15919, plain, (![A_22, C_430]: (k5_xboole_0(A_22, k5_xboole_0(A_22, C_430))=k5_xboole_0(k1_xboole_0, C_430))), inference(superposition, [status(thm), theory('equality')], [c_22, c_15842])).
% 11.37/4.37  tff(c_16070, plain, (![A_438, C_439]: (k5_xboole_0(A_438, k5_xboole_0(A_438, C_439))=C_439)), inference(demodulation, [status(thm), theory('equality')], [c_15743, c_15919])).
% 11.37/4.37  tff(c_16119, plain, (![A_7, B_8]: (k5_xboole_0(A_7, k4_xboole_0(A_7, B_8))=k3_xboole_0(A_7, B_8))), inference(superposition, [status(thm), theory('equality')], [c_8, c_16070])).
% 11.37/4.37  tff(c_19051, plain, (![A_536, B_537]: (k5_xboole_0(A_536, k5_xboole_0(B_537, k2_xboole_0(A_536, B_537)))=k3_xboole_0(A_536, B_537))), inference(superposition, [status(thm), theory('equality')], [c_24, c_15842])).
% 11.37/4.37  tff(c_15932, plain, (![A_22, C_430]: (k5_xboole_0(A_22, k5_xboole_0(A_22, C_430))=C_430)), inference(demodulation, [status(thm), theory('equality')], [c_15743, c_15919])).
% 11.37/4.37  tff(c_19094, plain, (![B_537, A_536]: (k5_xboole_0(B_537, k2_xboole_0(A_536, B_537))=k5_xboole_0(A_536, k3_xboole_0(A_536, B_537)))), inference(superposition, [status(thm), theory('equality')], [c_19051, c_15932])).
% 11.37/4.37  tff(c_19186, plain, (![B_537, A_536]: (k5_xboole_0(B_537, k2_xboole_0(A_536, B_537))=k4_xboole_0(A_536, B_537))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_19094])).
% 11.37/4.37  tff(c_15158, plain, (k4_xboole_0(k1_tarski('#skF_1'), '#skF_2')=k1_tarski('#skF_1')), inference(splitRight, [status(thm)], [c_58])).
% 11.37/4.37  tff(c_62, plain, (k4_xboole_0(k1_tarski('#skF_1'), '#skF_2')!=k1_tarski('#skF_1') | k4_xboole_0(k1_tarski('#skF_3'), '#skF_4')=k1_tarski('#skF_3')), inference(cnfTransformation, [status(thm)], [f_93])).
% 11.37/4.37  tff(c_15364, plain, (k4_xboole_0(k1_tarski('#skF_3'), '#skF_4')=k1_tarski('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_15158, c_62])).
% 11.37/4.37  tff(c_15173, plain, (![A_389, B_390]: (k3_tarski(k2_tarski(A_389, B_390))=k2_xboole_0(A_389, B_390))), inference(cnfTransformation, [status(thm)], [f_80])).
% 11.37/4.37  tff(c_15201, plain, (![B_392, A_393]: (k3_tarski(k2_tarski(B_392, A_393))=k2_xboole_0(A_393, B_392))), inference(superposition, [status(thm), theory('equality')], [c_26, c_15173])).
% 11.37/4.37  tff(c_15207, plain, (![B_392, A_393]: (k2_xboole_0(B_392, A_393)=k2_xboole_0(A_393, B_392))), inference(superposition, [status(thm), theory('equality')], [c_15201, c_50])).
% 11.37/4.37  tff(c_16122, plain, (![A_1, B_2]: (k5_xboole_0(A_1, k5_xboole_0(B_2, A_1))=B_2)), inference(superposition, [status(thm), theory('equality')], [c_2, c_16070])).
% 11.37/4.37  tff(c_18434, plain, (![A_523, B_524]: (k5_xboole_0(k2_xboole_0(A_523, B_524), k5_xboole_0(A_523, B_524))=k3_xboole_0(A_523, B_524))), inference(superposition, [status(thm), theory('equality')], [c_15678, c_2])).
% 11.37/4.37  tff(c_18568, plain, (![A_15, B_16]: (k5_xboole_0(k2_xboole_0(A_15, B_16), k5_xboole_0(A_15, k2_xboole_0(A_15, B_16)))=k3_xboole_0(A_15, k2_xboole_0(A_15, B_16)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_18434])).
% 11.37/4.37  tff(c_18625, plain, (![A_525, B_526]: (k3_xboole_0(A_525, k2_xboole_0(A_525, B_526))=A_525)), inference(demodulation, [status(thm), theory('equality')], [c_16122, c_18568])).
% 11.37/4.37  tff(c_18675, plain, (![A_393, B_392]: (k3_xboole_0(A_393, k2_xboole_0(B_392, A_393))=A_393)), inference(superposition, [status(thm), theory('equality')], [c_15207, c_18625])).
% 11.37/4.37  tff(c_15373, plain, (![A_400, B_401]: (k2_xboole_0(A_400, k2_xboole_0(A_400, B_401))=k2_xboole_0(A_400, B_401))), inference(cnfTransformation, [status(thm)], [f_41])).
% 11.37/4.37  tff(c_15402, plain, (![A_393, B_392]: (k2_xboole_0(A_393, k2_xboole_0(B_392, A_393))=k2_xboole_0(A_393, B_392))), inference(superposition, [status(thm), theory('equality')], [c_15207, c_15373])).
% 11.37/4.37  tff(c_19205, plain, (![B_538, A_539]: (k5_xboole_0(B_538, k2_xboole_0(A_539, B_538))=k4_xboole_0(A_539, B_538))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_19094])).
% 11.37/4.37  tff(c_15687, plain, (![A_424, B_425]: (k5_xboole_0(k2_xboole_0(A_424, B_425), k5_xboole_0(A_424, B_425))=k3_xboole_0(A_424, B_425))), inference(superposition, [status(thm), theory('equality')], [c_15678, c_2])).
% 11.37/4.37  tff(c_19211, plain, (![B_538, A_539]: (k5_xboole_0(k2_xboole_0(B_538, k2_xboole_0(A_539, B_538)), k4_xboole_0(A_539, B_538))=k3_xboole_0(B_538, k2_xboole_0(A_539, B_538)))), inference(superposition, [status(thm), theory('equality')], [c_19205, c_15687])).
% 11.37/4.37  tff(c_19315, plain, (![B_540, A_541]: (k5_xboole_0(k2_xboole_0(B_540, A_541), k4_xboole_0(A_541, B_540))=B_540)), inference(demodulation, [status(thm), theory('equality')], [c_18675, c_15402, c_19211])).
% 11.37/4.37  tff(c_19396, plain, (k5_xboole_0(k2_xboole_0('#skF_4', k1_tarski('#skF_3')), k1_tarski('#skF_3'))='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_15364, c_19315])).
% 11.37/4.37  tff(c_17378, plain, (![A_514, A_512, B_513]: (k5_xboole_0(A_514, k5_xboole_0(A_512, B_513))=k5_xboole_0(A_512, k5_xboole_0(B_513, A_514)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_15842])).
% 11.37/4.37  tff(c_17782, plain, (![A_515, A_516]: (k5_xboole_0(k1_xboole_0, k5_xboole_0(A_515, A_516))=k5_xboole_0(A_516, A_515))), inference(superposition, [status(thm), theory('equality')], [c_15743, c_17378])).
% 11.37/4.37  tff(c_17809, plain, (![A_515, A_516]: (k5_xboole_0(k5_xboole_0(A_515, A_516), k5_xboole_0(A_516, A_515))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_17782, c_16122])).
% 11.37/4.37  tff(c_19448, plain, (k5_xboole_0('#skF_4', k5_xboole_0(k1_tarski('#skF_3'), k2_xboole_0('#skF_4', k1_tarski('#skF_3'))))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_19396, c_17809])).
% 11.37/4.37  tff(c_19495, plain, (k3_xboole_0('#skF_4', k1_tarski('#skF_3'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_16119, c_19186, c_19448])).
% 11.37/4.37  tff(c_16643, plain, (![A_465, B_466]: (k5_xboole_0(A_465, k4_xboole_0(A_465, B_466))=k3_xboole_0(A_465, B_466))), inference(superposition, [status(thm), theory('equality')], [c_8, c_16070])).
% 11.37/4.37  tff(c_16272, plain, (![A_443, B_444]: (k5_xboole_0(A_443, k5_xboole_0(B_444, A_443))=B_444)), inference(superposition, [status(thm), theory('equality')], [c_2, c_16070])).
% 11.37/4.37  tff(c_16275, plain, (![B_444, A_443]: (k5_xboole_0(k5_xboole_0(B_444, A_443), B_444)=A_443)), inference(superposition, [status(thm), theory('equality')], [c_16272, c_16122])).
% 11.37/4.37  tff(c_16652, plain, (![A_465, B_466]: (k5_xboole_0(k3_xboole_0(A_465, B_466), A_465)=k4_xboole_0(A_465, B_466))), inference(superposition, [status(thm), theory('equality')], [c_16643, c_16275])).
% 11.37/4.37  tff(c_19503, plain, (k4_xboole_0('#skF_4', k1_tarski('#skF_3'))=k5_xboole_0(k1_xboole_0, '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_19495, c_16652])).
% 11.37/4.37  tff(c_19515, plain, (k4_xboole_0('#skF_4', k1_tarski('#skF_3'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_15758, c_2, c_19503])).
% 11.37/4.37  tff(c_54, plain, (![C_80, B_79]: (~r2_hidden(C_80, k4_xboole_0(B_79, k1_tarski(C_80))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 11.37/4.37  tff(c_19546, plain, (~r2_hidden('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_19515, c_54])).
% 11.37/4.37  tff(c_19557, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_15157, c_19546])).
% 11.37/4.37  tff(c_19558, plain, (r2_hidden('#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_60])).
% 11.37/4.37  tff(c_19559, plain, (r2_hidden('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_60])).
% 11.37/4.37  tff(c_64, plain, (~r2_hidden('#skF_1', '#skF_2') | k4_xboole_0(k1_tarski('#skF_3'), '#skF_4')=k1_tarski('#skF_3')), inference(cnfTransformation, [status(thm)], [f_93])).
% 11.37/4.37  tff(c_19757, plain, (k4_xboole_0(k1_tarski('#skF_3'), '#skF_4')=k1_tarski('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_19559, c_64])).
% 11.37/4.37  tff(c_19560, plain, (![A_542, B_543]: (k3_tarski(k2_tarski(A_542, B_543))=k2_xboole_0(A_542, B_543))), inference(cnfTransformation, [status(thm)], [f_80])).
% 11.37/4.37  tff(c_19599, plain, (![B_549, A_550]: (k3_tarski(k2_tarski(B_549, A_550))=k2_xboole_0(A_550, B_549))), inference(superposition, [status(thm), theory('equality')], [c_26, c_19560])).
% 11.37/4.37  tff(c_19605, plain, (![B_549, A_550]: (k2_xboole_0(B_549, A_550)=k2_xboole_0(A_550, B_549))), inference(superposition, [status(thm), theory('equality')], [c_19599, c_50])).
% 11.37/4.37  tff(c_20350, plain, (![A_592, B_593]: (k5_xboole_0(k5_xboole_0(A_592, B_593), k2_xboole_0(A_592, B_593))=k3_xboole_0(A_592, B_593))), inference(cnfTransformation, [status(thm)], [f_51])).
% 11.37/4.37  tff(c_20429, plain, (![A_3]: (k5_xboole_0(k5_xboole_0(A_3, A_3), A_3)=k3_xboole_0(A_3, A_3))), inference(superposition, [status(thm), theory('equality')], [c_4, c_20350])).
% 11.37/4.37  tff(c_20444, plain, (![A_594]: (k5_xboole_0(k1_xboole_0, A_594)=A_594)), inference(demodulation, [status(thm), theory('equality')], [c_22, c_6, c_20429])).
% 11.37/4.37  tff(c_20479, plain, (![A_594]: (k5_xboole_0(A_594, k1_xboole_0)=A_594)), inference(superposition, [status(thm), theory('equality')], [c_20444, c_2])).
% 11.37/4.37  tff(c_20120, plain, (![A_585, B_586, C_587]: (k5_xboole_0(k5_xboole_0(A_585, B_586), C_587)=k5_xboole_0(A_585, k5_xboole_0(B_586, C_587)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 11.37/4.37  tff(c_20140, plain, (![A_585, B_586]: (k5_xboole_0(A_585, k5_xboole_0(B_586, k5_xboole_0(A_585, B_586)))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_20120, c_22])).
% 11.37/4.37  tff(c_20440, plain, (![A_3]: (k5_xboole_0(k1_xboole_0, A_3)=A_3)), inference(demodulation, [status(thm), theory('equality')], [c_22, c_6, c_20429])).
% 11.37/4.37  tff(c_20170, plain, (![A_22, C_587]: (k5_xboole_0(A_22, k5_xboole_0(A_22, C_587))=k5_xboole_0(k1_xboole_0, C_587))), inference(superposition, [status(thm), theory('equality')], [c_22, c_20120])).
% 11.37/4.37  tff(c_20863, plain, (![A_611, C_612]: (k5_xboole_0(A_611, k5_xboole_0(A_611, C_612))=C_612)), inference(demodulation, [status(thm), theory('equality')], [c_20440, c_20170])).
% 11.37/4.37  tff(c_20916, plain, (![B_586, A_585]: (k5_xboole_0(B_586, k5_xboole_0(A_585, B_586))=k5_xboole_0(A_585, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_20140, c_20863])).
% 11.37/4.37  tff(c_20953, plain, (![B_586, A_585]: (k5_xboole_0(B_586, k5_xboole_0(A_585, B_586))=A_585)), inference(demodulation, [status(thm), theory('equality')], [c_20479, c_20916])).
% 11.37/4.37  tff(c_22345, plain, (![B_684, A_685]: (k5_xboole_0(k5_xboole_0(B_684, A_685), k2_xboole_0(A_685, B_684))=k3_xboole_0(A_685, B_684))), inference(superposition, [status(thm), theory('equality')], [c_2, c_20350])).
% 11.37/4.37  tff(c_22466, plain, (![A_15, B_16]: (k5_xboole_0(k5_xboole_0(k2_xboole_0(A_15, B_16), A_15), k2_xboole_0(A_15, B_16))=k3_xboole_0(A_15, k2_xboole_0(A_15, B_16)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_22345])).
% 11.37/4.37  tff(c_22526, plain, (![A_686, B_687]: (k3_xboole_0(A_686, k2_xboole_0(A_686, B_687))=A_686)), inference(demodulation, [status(thm), theory('equality')], [c_20953, c_2, c_2, c_22466])).
% 11.37/4.37  tff(c_22576, plain, (![A_550, B_549]: (k3_xboole_0(A_550, k2_xboole_0(B_549, A_550))=A_550)), inference(superposition, [status(thm), theory('equality')], [c_19605, c_22526])).
% 11.37/4.37  tff(c_19767, plain, (![A_557, B_558]: (k2_xboole_0(A_557, k2_xboole_0(A_557, B_558))=k2_xboole_0(A_557, B_558))), inference(cnfTransformation, [status(thm)], [f_41])).
% 11.37/4.37  tff(c_19799, plain, (![B_549, A_550]: (k2_xboole_0(B_549, k2_xboole_0(A_550, B_549))=k2_xboole_0(B_549, A_550))), inference(superposition, [status(thm), theory('equality')], [c_19605, c_19767])).
% 11.37/4.37  tff(c_20, plain, (![A_19, B_20, C_21]: (k5_xboole_0(k5_xboole_0(A_19, B_20), C_21)=k5_xboole_0(A_19, k5_xboole_0(B_20, C_21)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 11.37/4.37  tff(c_25603, plain, (![A_729, B_730]: (k5_xboole_0(A_729, k5_xboole_0(B_730, k2_xboole_0(A_729, B_730)))=k3_xboole_0(A_729, B_730))), inference(superposition, [status(thm), theory('equality')], [c_20350, c_20])).
% 11.37/4.37  tff(c_20862, plain, (![A_22, C_587]: (k5_xboole_0(A_22, k5_xboole_0(A_22, C_587))=C_587)), inference(demodulation, [status(thm), theory('equality')], [c_20440, c_20170])).
% 11.37/4.37  tff(c_25656, plain, (![B_730, A_729]: (k5_xboole_0(B_730, k2_xboole_0(A_729, B_730))=k5_xboole_0(A_729, k3_xboole_0(A_729, B_730)))), inference(superposition, [status(thm), theory('equality')], [c_25603, c_20862])).
% 11.37/4.37  tff(c_25787, plain, (![B_731, A_732]: (k5_xboole_0(B_731, k2_xboole_0(A_732, B_731))=k4_xboole_0(A_732, B_731))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_25656])).
% 11.37/4.37  tff(c_20420, plain, (![A_592, B_593]: (k5_xboole_0(k2_xboole_0(A_592, B_593), k5_xboole_0(A_592, B_593))=k3_xboole_0(A_592, B_593))), inference(superposition, [status(thm), theory('equality')], [c_2, c_20350])).
% 11.37/4.37  tff(c_25811, plain, (![B_731, A_732]: (k5_xboole_0(k2_xboole_0(B_731, k2_xboole_0(A_732, B_731)), k4_xboole_0(A_732, B_731))=k3_xboole_0(B_731, k2_xboole_0(A_732, B_731)))), inference(superposition, [status(thm), theory('equality')], [c_25787, c_20420])).
% 11.37/4.37  tff(c_26077, plain, (![B_735, A_736]: (k5_xboole_0(k2_xboole_0(B_735, A_736), k4_xboole_0(A_736, B_735))=B_735)), inference(demodulation, [status(thm), theory('equality')], [c_22576, c_19799, c_25811])).
% 11.37/4.37  tff(c_26179, plain, (k5_xboole_0(k2_xboole_0('#skF_4', k1_tarski('#skF_3')), k1_tarski('#skF_3'))='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_19757, c_26077])).
% 11.37/4.37  tff(c_24030, plain, (![C_715, A_716, B_717]: (k5_xboole_0(C_715, k5_xboole_0(A_716, B_717))=k5_xboole_0(A_716, k5_xboole_0(B_717, C_715)))), inference(superposition, [status(thm), theory('equality')], [c_20120, c_2])).
% 11.37/4.37  tff(c_24371, plain, (![A_3, C_715]: (k5_xboole_0(k1_xboole_0, k5_xboole_0(A_3, C_715))=k5_xboole_0(C_715, A_3))), inference(superposition, [status(thm), theory('equality')], [c_20440, c_24030])).
% 11.37/4.37  tff(c_25802, plain, (![A_732, B_731]: (k5_xboole_0(k2_xboole_0(A_732, B_731), B_731)=k5_xboole_0(k1_xboole_0, k4_xboole_0(A_732, B_731)))), inference(superposition, [status(thm), theory('equality')], [c_25787, c_24371])).
% 11.37/4.37  tff(c_25909, plain, (![A_732, B_731]: (k5_xboole_0(k2_xboole_0(A_732, B_731), B_731)=k4_xboole_0(A_732, B_731))), inference(demodulation, [status(thm), theory('equality')], [c_20440, c_25802])).
% 11.37/4.37  tff(c_26228, plain, (k4_xboole_0('#skF_4', k1_tarski('#skF_3'))='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_26179, c_25909])).
% 11.37/4.37  tff(c_26329, plain, (~r2_hidden('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_26228, c_54])).
% 11.37/4.37  tff(c_26339, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_19558, c_26329])).
% 11.37/4.37  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.37/4.37  
% 11.37/4.37  Inference rules
% 11.37/4.37  ----------------------
% 11.37/4.37  #Ref     : 0
% 11.37/4.37  #Sup     : 6660
% 11.37/4.37  #Fact    : 0
% 11.37/4.37  #Define  : 0
% 11.37/4.37  #Split   : 2
% 11.37/4.37  #Chain   : 0
% 11.37/4.37  #Close   : 0
% 11.37/4.37  
% 11.37/4.37  Ordering : KBO
% 11.37/4.37  
% 11.37/4.37  Simplification rules
% 11.37/4.37  ----------------------
% 11.37/4.37  #Subsume      : 493
% 11.37/4.37  #Demod        : 7096
% 11.37/4.37  #Tautology    : 3659
% 11.37/4.37  #SimpNegUnit  : 24
% 11.37/4.37  #BackRed      : 8
% 11.37/4.37  
% 11.37/4.37  #Partial instantiations: 0
% 11.37/4.37  #Strategies tried      : 1
% 11.37/4.37  
% 11.37/4.37  Timing (in seconds)
% 11.37/4.37  ----------------------
% 11.37/4.37  Preprocessing        : 0.34
% 11.37/4.37  Parsing              : 0.18
% 11.37/4.37  CNF conversion       : 0.02
% 11.37/4.37  Main loop            : 3.24
% 11.37/4.37  Inferencing          : 0.78
% 11.37/4.37  Reduction            : 1.77
% 11.37/4.37  Demodulation         : 1.57
% 11.37/4.37  BG Simplification    : 0.11
% 11.37/4.37  Subsumption          : 0.42
% 11.37/4.37  Abstraction          : 0.16
% 11.37/4.37  MUC search           : 0.00
% 11.37/4.37  Cooper               : 0.00
% 11.37/4.37  Total                : 3.63
% 11.37/4.37  Index Insertion      : 0.00
% 11.37/4.37  Index Deletion       : 0.00
% 11.37/4.37  Index Matching       : 0.00
% 11.37/4.37  BG Taut test         : 0.00
%------------------------------------------------------------------------------

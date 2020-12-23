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
% DateTime   : Thu Dec  3 09:53:21 EST 2020

% Result     : Theorem 8.89s
% Output     : CNFRefutation 9.26s
% Verified   : 
% Statistics : Number of formulae       :  327 (1709 expanded)
%              Number of leaves         :   37 ( 553 expanded)
%              Depth                    :   14
%              Number of atoms          :  382 (2671 expanded)
%              Number of equality atoms :  335 (2553 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

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

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

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

tff(f_43,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_37,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_41,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_29,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_61,axiom,(
    ! [A] : k3_tarski(k1_tarski(A)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_zfmisc_1)).

tff(f_47,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_59,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_45,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_xboole_1)).

tff(f_92,negated_conjecture,(
    ~ ! [A,B,C] :
        ( k4_xboole_0(A,k2_tarski(B,C)) = k1_xboole_0
      <=> ~ ( A != k1_xboole_0
            & A != k1_tarski(B)
            & A != k1_tarski(C)
            & A != k2_tarski(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_zfmisc_1)).

tff(f_39,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_76,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k2_tarski(B,C))
    <=> ~ ( A != k1_xboole_0
          & A != k1_tarski(B)
          & A != k1_tarski(C)
          & A != k2_tarski(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => B = k2_xboole_0(A,k4_xboole_0(B,A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_xboole_1)).

tff(c_16,plain,(
    ! [A_15] : k5_xboole_0(A_15,A_15) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_10,plain,(
    ! [A_9] : k5_xboole_0(A_9,k1_xboole_0) = A_9 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_16238,plain,(
    ! [A_610,B_611,C_612] : k5_xboole_0(k5_xboole_0(A_610,B_611),C_612) = k5_xboole_0(A_610,k5_xboole_0(B_611,C_612)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_16454,plain,(
    ! [A_620,C_621] : k5_xboole_0(A_620,k5_xboole_0(A_620,C_621)) = k5_xboole_0(k1_xboole_0,C_621) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_16238])).

tff(c_16522,plain,(
    ! [A_15] : k5_xboole_0(k1_xboole_0,A_15) = k5_xboole_0(A_15,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_16454])).

tff(c_16538,plain,(
    ! [A_15] : k5_xboole_0(k1_xboole_0,A_15) = A_15 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_16522])).

tff(c_16279,plain,(
    ! [A_15,C_612] : k5_xboole_0(A_15,k5_xboole_0(A_15,C_612)) = k5_xboole_0(k1_xboole_0,C_612) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_16238])).

tff(c_16539,plain,(
    ! [A_15,C_612] : k5_xboole_0(A_15,k5_xboole_0(A_15,C_612)) = C_612 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16538,c_16279])).

tff(c_16256,plain,(
    ! [A_610,B_611] : k5_xboole_0(A_610,k5_xboole_0(B_611,k5_xboole_0(A_610,B_611))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_16238,c_16])).

tff(c_16602,plain,(
    ! [A_623,C_624] : k5_xboole_0(A_623,k5_xboole_0(A_623,C_624)) = C_624 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16538,c_16279])).

tff(c_16646,plain,(
    ! [B_611,A_610] : k5_xboole_0(B_611,k5_xboole_0(A_610,B_611)) = k5_xboole_0(A_610,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_16256,c_16602])).

tff(c_16880,plain,(
    ! [B_637,A_638] : k5_xboole_0(B_637,k5_xboole_0(A_638,B_637)) = A_638 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_16646])).

tff(c_16919,plain,(
    ! [A_15,C_612] : k5_xboole_0(k5_xboole_0(A_15,C_612),C_612) = A_15 ),
    inference(superposition,[status(thm),theory(equality)],[c_16539,c_16880])).

tff(c_2,plain,(
    ! [A_1] : k3_xboole_0(A_1,A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_16169,plain,(
    ! [A_602,B_603] : k5_xboole_0(A_602,k3_xboole_0(A_602,B_603)) = k4_xboole_0(A_602,B_603) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_16178,plain,(
    ! [A_1] : k5_xboole_0(A_1,A_1) = k4_xboole_0(A_1,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_16169])).

tff(c_16181,plain,(
    ! [A_1] : k4_xboole_0(A_1,A_1) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_16178])).

tff(c_34,plain,(
    ! [A_45] : k3_tarski(k1_tarski(A_45)) = A_45 ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_20,plain,(
    ! [A_18] : k2_tarski(A_18,A_18) = k1_tarski(A_18) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_186,plain,(
    ! [A_69,B_70] : k3_tarski(k2_tarski(A_69,B_70)) = k2_xboole_0(A_69,B_70) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_195,plain,(
    ! [A_18] : k3_tarski(k1_tarski(A_18)) = k2_xboole_0(A_18,A_18) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_186])).

tff(c_198,plain,(
    ! [A_18] : k2_xboole_0(A_18,A_18) = A_18 ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_195])).

tff(c_13021,plain,(
    ! [A_456,B_457] : k5_xboole_0(k5_xboole_0(A_456,B_457),k2_xboole_0(A_456,B_457)) = k3_xboole_0(A_456,B_457) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_13075,plain,(
    ! [A_15] : k5_xboole_0(k1_xboole_0,k2_xboole_0(A_15,A_15)) = k3_xboole_0(A_15,A_15) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_13021])).

tff(c_13081,plain,(
    ! [A_15] : k5_xboole_0(k1_xboole_0,A_15) = A_15 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_198,c_13075])).

tff(c_13082,plain,(
    ! [A_458,B_459,C_460] : k5_xboole_0(k5_xboole_0(A_458,B_459),C_460) = k5_xboole_0(A_458,k5_xboole_0(B_459,C_460)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_13136,plain,(
    ! [A_15,C_460] : k5_xboole_0(A_15,k5_xboole_0(A_15,C_460)) = k5_xboole_0(k1_xboole_0,C_460) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_13082])).

tff(c_13310,plain,(
    ! [A_15,C_460] : k5_xboole_0(A_15,k5_xboole_0(A_15,C_460)) = C_460 ),
    inference(demodulation,[status(thm),theory(equality)],[c_13081,c_13136])).

tff(c_13376,plain,(
    ! [A_472,B_473] : k5_xboole_0(A_472,k5_xboole_0(B_473,k5_xboole_0(A_472,B_473))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_13082,c_16])).

tff(c_13384,plain,(
    ! [B_473,A_472] : k5_xboole_0(B_473,k5_xboole_0(A_472,B_473)) = k5_xboole_0(A_472,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_13376,c_13310])).

tff(c_13474,plain,(
    ! [B_474,A_475] : k5_xboole_0(B_474,k5_xboole_0(A_475,B_474)) = A_475 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_13384])).

tff(c_13510,plain,(
    ! [A_15,C_460] : k5_xboole_0(k5_xboole_0(A_15,C_460),C_460) = A_15 ),
    inference(superposition,[status(thm),theory(equality)],[c_13310,c_13474])).

tff(c_221,plain,(
    ! [A_73,B_74] : k5_xboole_0(A_73,k3_xboole_0(A_73,B_74)) = k4_xboole_0(A_73,B_74) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_230,plain,(
    ! [A_1] : k5_xboole_0(A_1,A_1) = k4_xboole_0(A_1,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_221])).

tff(c_233,plain,(
    ! [A_1] : k4_xboole_0(A_1,A_1) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_230])).

tff(c_401,plain,(
    ! [A_89,B_90] : k5_xboole_0(k5_xboole_0(A_89,B_90),k2_xboole_0(A_89,B_90)) = k3_xboole_0(A_89,B_90) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_446,plain,(
    ! [A_15] : k5_xboole_0(k1_xboole_0,k2_xboole_0(A_15,A_15)) = k3_xboole_0(A_15,A_15) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_401])).

tff(c_452,plain,(
    ! [A_15] : k5_xboole_0(k1_xboole_0,A_15) = A_15 ),
    inference(demodulation,[status(thm),theory(equality)],[c_198,c_2,c_446])).

tff(c_493,plain,(
    ! [A_92,B_93,C_94] : k5_xboole_0(k5_xboole_0(A_92,B_93),C_94) = k5_xboole_0(A_92,k5_xboole_0(B_93,C_94)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_550,plain,(
    ! [A_15,C_94] : k5_xboole_0(A_15,k5_xboole_0(A_15,C_94)) = k5_xboole_0(k1_xboole_0,C_94) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_493])).

tff(c_563,plain,(
    ! [A_15,C_94] : k5_xboole_0(A_15,k5_xboole_0(A_15,C_94)) = C_94 ),
    inference(demodulation,[status(thm),theory(equality)],[c_452,c_550])).

tff(c_10442,plain,(
    ! [A_346,B_347] : k5_xboole_0(A_346,k5_xboole_0(B_347,k5_xboole_0(A_346,B_347))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_493,c_16])).

tff(c_10450,plain,(
    ! [B_347,A_346] : k5_xboole_0(B_347,k5_xboole_0(A_346,B_347)) = k5_xboole_0(A_346,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_10442,c_563])).

tff(c_10540,plain,(
    ! [B_348,A_349] : k5_xboole_0(B_348,k5_xboole_0(A_349,B_348)) = A_349 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_10450])).

tff(c_10576,plain,(
    ! [A_15,C_94] : k5_xboole_0(k5_xboole_0(A_15,C_94),C_94) = A_15 ),
    inference(superposition,[status(thm),theory(equality)],[c_563,c_10540])).

tff(c_58,plain,
    ( k4_xboole_0('#skF_1',k2_tarski('#skF_2','#skF_3')) != k1_xboole_0
    | k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_128,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_58])).

tff(c_54,plain,
    ( k4_xboole_0('#skF_1',k2_tarski('#skF_2','#skF_3')) != k1_xboole_0
    | k1_tarski('#skF_5') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_348,plain,(
    k1_tarski('#skF_5') != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_54])).

tff(c_50,plain,
    ( k4_xboole_0('#skF_1',k2_tarski('#skF_2','#skF_3')) != k1_xboole_0
    | k1_tarski('#skF_6') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_219,plain,(
    k1_tarski('#skF_6') != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_46,plain,
    ( k4_xboole_0('#skF_1',k2_tarski('#skF_2','#skF_3')) != k1_xboole_0
    | k2_tarski('#skF_5','#skF_6') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_587,plain,(
    k2_tarski('#skF_5','#skF_6') != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_46])).

tff(c_749,plain,(
    ! [A_105,B_106] : k5_xboole_0(A_105,k5_xboole_0(B_106,k5_xboole_0(A_105,B_106))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_493,c_16])).

tff(c_757,plain,(
    ! [B_106,A_105] : k5_xboole_0(B_106,k5_xboole_0(A_105,B_106)) = k5_xboole_0(A_105,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_749,c_563])).

tff(c_847,plain,(
    ! [B_107,A_108] : k5_xboole_0(B_107,k5_xboole_0(A_108,B_107)) = A_108 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_757])).

tff(c_883,plain,(
    ! [A_15,C_94] : k5_xboole_0(k5_xboole_0(A_15,C_94),C_94) = A_15 ),
    inference(superposition,[status(thm),theory(equality)],[c_563,c_847])).

tff(c_64,plain,
    ( k2_tarski('#skF_2','#skF_3') = '#skF_1'
    | k1_tarski('#skF_3') = '#skF_1'
    | k1_tarski('#skF_2') = '#skF_1'
    | k1_xboole_0 = '#skF_1'
    | k4_xboole_0('#skF_4',k2_tarski('#skF_5','#skF_6')) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_2471,plain,(
    k4_xboole_0('#skF_4',k2_tarski('#skF_5','#skF_6')) = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_64])).

tff(c_4,plain,(
    ! [A_3,B_4] : k5_xboole_0(A_3,k3_xboole_0(A_3,B_4)) = k4_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_18,plain,(
    ! [A_16,B_17] : k5_xboole_0(k5_xboole_0(A_16,B_17),k2_xboole_0(A_16,B_17)) = k3_xboole_0(A_16,B_17) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_2676,plain,(
    ! [A_162,B_163] : k5_xboole_0(A_162,k5_xboole_0(B_163,k2_xboole_0(A_162,B_163))) = k3_xboole_0(A_162,B_163) ),
    inference(superposition,[status(thm),theory(equality)],[c_493,c_18])).

tff(c_2691,plain,(
    ! [B_163,A_162] : k5_xboole_0(B_163,k2_xboole_0(A_162,B_163)) = k5_xboole_0(A_162,k3_xboole_0(A_162,B_163)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2676,c_563])).

tff(c_3068,plain,(
    ! [B_172,A_173] : k5_xboole_0(B_172,k2_xboole_0(A_173,B_172)) = k4_xboole_0(A_173,B_172) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_2691])).

tff(c_3498,plain,(
    ! [B_183,A_184] : k5_xboole_0(B_183,k4_xboole_0(A_184,B_183)) = k2_xboole_0(A_184,B_183) ),
    inference(superposition,[status(thm),theory(equality)],[c_3068,c_563])).

tff(c_3559,plain,(
    k5_xboole_0(k2_tarski('#skF_5','#skF_6'),k1_xboole_0) = k2_xboole_0('#skF_4',k2_tarski('#skF_5','#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_2471,c_3498])).

tff(c_3600,plain,(
    k2_xboole_0('#skF_4',k2_tarski('#skF_5','#skF_6')) = k2_tarski('#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_3559])).

tff(c_12,plain,(
    ! [A_10,B_11] : r1_tarski(A_10,k2_xboole_0(A_10,B_11)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_4490,plain,(
    r1_tarski('#skF_4',k2_tarski('#skF_5','#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_3600,c_12])).

tff(c_36,plain,(
    ! [B_47,C_48,A_46] :
      ( k2_tarski(B_47,C_48) = A_46
      | k1_tarski(C_48) = A_46
      | k1_tarski(B_47) = A_46
      | k1_xboole_0 = A_46
      | ~ r1_tarski(A_46,k2_tarski(B_47,C_48)) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_4652,plain,
    ( k2_tarski('#skF_5','#skF_6') = '#skF_4'
    | k1_tarski('#skF_6') = '#skF_4'
    | k1_tarski('#skF_5') = '#skF_4'
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_4490,c_36])).

tff(c_4659,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_128,c_348,c_219,c_587,c_4652])).

tff(c_4660,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_tarski('#skF_2') = '#skF_1'
    | k1_tarski('#skF_3') = '#skF_1'
    | k2_tarski('#skF_2','#skF_3') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_4663,plain,(
    k2_tarski('#skF_2','#skF_3') = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_4660])).

tff(c_62,plain,
    ( k4_xboole_0('#skF_1',k2_tarski('#skF_2','#skF_3')) != k1_xboole_0
    | k4_xboole_0('#skF_4',k2_tarski('#skF_5','#skF_6')) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_924,plain,(
    k4_xboole_0('#skF_1',k2_tarski('#skF_2','#skF_3')) != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_62])).

tff(c_4664,plain,(
    k4_xboole_0('#skF_1','#skF_1') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4663,c_924])).

tff(c_4667,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_233,c_4664])).

tff(c_4668,plain,
    ( k1_tarski('#skF_3') = '#skF_1'
    | k1_tarski('#skF_2') = '#skF_1'
    | k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_4660])).

tff(c_4670,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_4668])).

tff(c_44,plain,(
    ! [B_47,C_48] : r1_tarski(k1_xboole_0,k2_tarski(B_47,C_48)) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_6,plain,(
    ! [A_5,B_6] : k2_xboole_0(A_5,k4_xboole_0(B_6,A_5)) = k2_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_8,plain,(
    ! [A_7,B_8] :
      ( k2_xboole_0(A_7,k4_xboole_0(B_8,A_7)) = B_8
      | ~ r1_tarski(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_135,plain,(
    ! [A_64,B_65] :
      ( k2_xboole_0(A_64,B_65) = B_65
      | ~ r1_tarski(A_64,B_65) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_8])).

tff(c_159,plain,(
    ! [B_47,C_48] : k2_xboole_0(k1_xboole_0,k2_tarski(B_47,C_48)) = k2_tarski(B_47,C_48) ),
    inference(resolution,[status(thm)],[c_44,c_135])).

tff(c_5180,plain,(
    ! [B_214,C_215] : k2_xboole_0('#skF_1',k2_tarski(B_214,C_215)) = k2_tarski(B_214,C_215) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4670,c_159])).

tff(c_5186,plain,(
    ! [B_214,C_215] : k5_xboole_0(k5_xboole_0('#skF_1',k2_tarski(B_214,C_215)),k2_tarski(B_214,C_215)) = k3_xboole_0('#skF_1',k2_tarski(B_214,C_215)) ),
    inference(superposition,[status(thm),theory(equality)],[c_5180,c_18])).

tff(c_5200,plain,(
    ! [B_214,C_215] : k3_xboole_0('#skF_1',k2_tarski(B_214,C_215)) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_883,c_5186])).

tff(c_4704,plain,(
    ! [A_200] : k5_xboole_0(A_200,A_200) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4670,c_16])).

tff(c_14,plain,(
    ! [A_12,B_13,C_14] : k5_xboole_0(k5_xboole_0(A_12,B_13),C_14) = k5_xboole_0(A_12,k5_xboole_0(B_13,C_14)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_4721,plain,(
    ! [A_200,C_14] : k5_xboole_0(A_200,k5_xboole_0(A_200,C_14)) = k5_xboole_0('#skF_1',C_14) ),
    inference(superposition,[status(thm),theory(equality)],[c_4704,c_14])).

tff(c_4839,plain,(
    ! [C_202] : k5_xboole_0('#skF_1',C_202) = C_202 ),
    inference(demodulation,[status(thm),theory(equality)],[c_563,c_4721])).

tff(c_4890,plain,(
    ! [B_4] : k4_xboole_0('#skF_1',B_4) = k3_xboole_0('#skF_1',B_4) ),
    inference(superposition,[status(thm),theory(equality)],[c_4839,c_4])).

tff(c_4685,plain,(
    k4_xboole_0('#skF_1',k2_tarski('#skF_2','#skF_3')) != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4670,c_924])).

tff(c_5125,plain,(
    k3_xboole_0('#skF_1',k2_tarski('#skF_2','#skF_3')) != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4890,c_4685])).

tff(c_5341,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5200,c_5125])).

tff(c_5342,plain,
    ( k1_tarski('#skF_2') = '#skF_1'
    | k1_tarski('#skF_3') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_4668])).

tff(c_5344,plain,(
    k1_tarski('#skF_3') = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_5342])).

tff(c_40,plain,(
    ! [C_48,B_47] : r1_tarski(k1_tarski(C_48),k2_tarski(B_47,C_48)) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_5524,plain,(
    ! [B_223] : r1_tarski('#skF_1',k2_tarski(B_223,'#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_5344,c_40])).

tff(c_65,plain,(
    ! [A_7,B_8] :
      ( k2_xboole_0(A_7,B_8) = B_8
      | ~ r1_tarski(A_7,B_8) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_8])).

tff(c_5558,plain,(
    ! [B_225] : k2_xboole_0('#skF_1',k2_tarski(B_225,'#skF_3')) = k2_tarski(B_225,'#skF_3') ),
    inference(resolution,[status(thm)],[c_5524,c_65])).

tff(c_5564,plain,(
    ! [B_225] : k5_xboole_0(k5_xboole_0('#skF_1',k2_tarski(B_225,'#skF_3')),k2_tarski(B_225,'#skF_3')) = k3_xboole_0('#skF_1',k2_tarski(B_225,'#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_5558,c_18])).

tff(c_5585,plain,(
    ! [B_226] : k3_xboole_0('#skF_1',k2_tarski(B_226,'#skF_3')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_883,c_5564])).

tff(c_5599,plain,(
    ! [B_226] : k4_xboole_0('#skF_1',k2_tarski(B_226,'#skF_3')) = k5_xboole_0('#skF_1','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_5585,c_4])).

tff(c_5608,plain,(
    ! [B_226] : k4_xboole_0('#skF_1',k2_tarski(B_226,'#skF_3')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_5599])).

tff(c_5613,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5608,c_924])).

tff(c_5614,plain,(
    k1_tarski('#skF_2') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_5342])).

tff(c_42,plain,(
    ! [B_47,C_48] : r1_tarski(k1_tarski(B_47),k2_tarski(B_47,C_48)) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_5811,plain,(
    ! [C_231] : r1_tarski('#skF_1',k2_tarski('#skF_2',C_231)) ),
    inference(superposition,[status(thm),theory(equality)],[c_5614,c_42])).

tff(c_5914,plain,(
    ! [C_235] : k2_xboole_0('#skF_1',k2_tarski('#skF_2',C_235)) = k2_tarski('#skF_2',C_235) ),
    inference(resolution,[status(thm)],[c_5811,c_65])).

tff(c_5924,plain,(
    ! [C_235] : k5_xboole_0(k5_xboole_0('#skF_1',k2_tarski('#skF_2',C_235)),k2_tarski('#skF_2',C_235)) = k3_xboole_0('#skF_1',k2_tarski('#skF_2',C_235)) ),
    inference(superposition,[status(thm),theory(equality)],[c_5914,c_18])).

tff(c_6251,plain,(
    ! [C_242] : k3_xboole_0('#skF_1',k2_tarski('#skF_2',C_242)) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_883,c_5924])).

tff(c_6268,plain,(
    ! [C_242] : k4_xboole_0('#skF_1',k2_tarski('#skF_2',C_242)) = k5_xboole_0('#skF_1','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_6251,c_4])).

tff(c_6281,plain,(
    ! [C_242] : k4_xboole_0('#skF_1',k2_tarski('#skF_2',C_242)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_6268])).

tff(c_6290,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6281,c_924])).

tff(c_6291,plain,(
    k4_xboole_0('#skF_4',k2_tarski('#skF_5','#skF_6')) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_8086,plain,(
    ! [A_295,B_296] : k5_xboole_0(A_295,k5_xboole_0(B_296,k2_xboole_0(A_295,B_296))) = k3_xboole_0(A_295,B_296) ),
    inference(superposition,[status(thm),theory(equality)],[c_493,c_18])).

tff(c_8101,plain,(
    ! [B_296,A_295] : k5_xboole_0(B_296,k2_xboole_0(A_295,B_296)) = k5_xboole_0(A_295,k3_xboole_0(A_295,B_296)) ),
    inference(superposition,[status(thm),theory(equality)],[c_8086,c_563])).

tff(c_8548,plain,(
    ! [B_309,A_310] : k5_xboole_0(B_309,k2_xboole_0(A_310,B_309)) = k4_xboole_0(A_310,B_309) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_8101])).

tff(c_8646,plain,(
    ! [B_311,A_312] : k5_xboole_0(B_311,k4_xboole_0(A_312,B_311)) = k2_xboole_0(A_312,B_311) ),
    inference(superposition,[status(thm),theory(equality)],[c_8548,c_563])).

tff(c_8713,plain,(
    k5_xboole_0(k2_tarski('#skF_5','#skF_6'),k1_xboole_0) = k2_xboole_0('#skF_4',k2_tarski('#skF_5','#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_6291,c_8646])).

tff(c_8746,plain,(
    k2_xboole_0('#skF_4',k2_tarski('#skF_5','#skF_6')) = k2_tarski('#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_8713])).

tff(c_10093,plain,(
    r1_tarski('#skF_4',k2_tarski('#skF_5','#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_8746,c_12])).

tff(c_10111,plain,
    ( k2_tarski('#skF_5','#skF_6') = '#skF_4'
    | k1_tarski('#skF_6') = '#skF_4'
    | k1_tarski('#skF_5') = '#skF_4'
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_10093,c_36])).

tff(c_10118,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_128,c_348,c_219,c_587,c_10111])).

tff(c_10120,plain,(
    k2_tarski('#skF_5','#skF_6') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_48,plain,
    ( k2_tarski('#skF_2','#skF_3') = '#skF_1'
    | k1_tarski('#skF_3') = '#skF_1'
    | k1_tarski('#skF_2') = '#skF_1'
    | k1_xboole_0 = '#skF_1'
    | k2_tarski('#skF_5','#skF_6') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_10968,plain,
    ( k2_tarski('#skF_2','#skF_3') = '#skF_1'
    | k1_tarski('#skF_3') = '#skF_1'
    | k1_tarski('#skF_2') = '#skF_1'
    | k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10120,c_48])).

tff(c_10969,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_10968])).

tff(c_11649,plain,(
    ! [B_388,C_389] : k2_xboole_0('#skF_1',k2_tarski(B_388,C_389)) = k2_tarski(B_388,C_389) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10969,c_159])).

tff(c_11655,plain,(
    ! [B_388,C_389] : k5_xboole_0(k5_xboole_0('#skF_1',k2_tarski(B_388,C_389)),k2_tarski(B_388,C_389)) = k3_xboole_0('#skF_1',k2_tarski(B_388,C_389)) ),
    inference(superposition,[status(thm),theory(equality)],[c_11649,c_18])).

tff(c_11672,plain,(
    ! [B_388,C_389] : k3_xboole_0('#skF_1',k2_tarski(B_388,C_389)) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10576,c_11655])).

tff(c_11067,plain,(
    ! [A_357] : k5_xboole_0(A_357,A_357) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10969,c_16])).

tff(c_11095,plain,(
    ! [A_357] : k5_xboole_0('#skF_1',k2_xboole_0(A_357,A_357)) = k3_xboole_0(A_357,A_357) ),
    inference(superposition,[status(thm),theory(equality)],[c_11067,c_18])).

tff(c_11137,plain,(
    ! [A_361] : k5_xboole_0('#skF_1',A_361) = A_361 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_198,c_11095])).

tff(c_11184,plain,(
    ! [B_4] : k4_xboole_0('#skF_1',B_4) = k3_xboole_0('#skF_1',B_4) ),
    inference(superposition,[status(thm),theory(equality)],[c_11137,c_4])).

tff(c_10119,plain,(
    k4_xboole_0('#skF_1',k2_tarski('#skF_2','#skF_3')) != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_10976,plain,(
    k4_xboole_0('#skF_1',k2_tarski('#skF_2','#skF_3')) != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10969,c_10119])).

tff(c_11496,plain,(
    k3_xboole_0('#skF_1',k2_tarski('#skF_2','#skF_3')) != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11184,c_10976])).

tff(c_11680,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_11672,c_11496])).

tff(c_11681,plain,
    ( k1_tarski('#skF_2') = '#skF_1'
    | k1_tarski('#skF_3') = '#skF_1'
    | k2_tarski('#skF_2','#skF_3') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_10968])).

tff(c_11866,plain,(
    k2_tarski('#skF_2','#skF_3') = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_11681])).

tff(c_11867,plain,(
    k4_xboole_0('#skF_1','#skF_1') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_11866,c_10119])).

tff(c_11870,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_233,c_11867])).

tff(c_11871,plain,
    ( k1_tarski('#skF_3') = '#skF_1'
    | k1_tarski('#skF_2') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_11681])).

tff(c_11873,plain,(
    k1_tarski('#skF_2') = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_11871])).

tff(c_12008,plain,(
    ! [C_401] : r1_tarski('#skF_1',k2_tarski('#skF_2',C_401)) ),
    inference(superposition,[status(thm),theory(equality)],[c_11873,c_42])).

tff(c_12320,plain,(
    ! [C_419] : k2_xboole_0('#skF_1',k2_tarski('#skF_2',C_419)) = k2_tarski('#skF_2',C_419) ),
    inference(resolution,[status(thm)],[c_12008,c_65])).

tff(c_12326,plain,(
    ! [C_419] : k5_xboole_0(k5_xboole_0('#skF_1',k2_tarski('#skF_2',C_419)),k2_tarski('#skF_2',C_419)) = k3_xboole_0('#skF_1',k2_tarski('#skF_2',C_419)) ),
    inference(superposition,[status(thm),theory(equality)],[c_12320,c_18])).

tff(c_12346,plain,(
    ! [C_420] : k3_xboole_0('#skF_1',k2_tarski('#skF_2',C_420)) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10576,c_12326])).

tff(c_12351,plain,(
    ! [C_420] : k4_xboole_0('#skF_1',k2_tarski('#skF_2',C_420)) = k5_xboole_0('#skF_1','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_12346,c_4])).

tff(c_12359,plain,(
    ! [C_420] : k4_xboole_0('#skF_1',k2_tarski('#skF_2',C_420)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_12351])).

tff(c_12364,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12359,c_10119])).

tff(c_12365,plain,(
    k1_tarski('#skF_3') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_11871])).

tff(c_12511,plain,(
    ! [B_428] : r1_tarski('#skF_1',k2_tarski(B_428,'#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_12365,c_40])).

tff(c_12799,plain,(
    ! [B_446] : k2_xboole_0('#skF_1',k2_tarski(B_446,'#skF_3')) = k2_tarski(B_446,'#skF_3') ),
    inference(resolution,[status(thm)],[c_12511,c_65])).

tff(c_12805,plain,(
    ! [B_446] : k5_xboole_0(k5_xboole_0('#skF_1',k2_tarski(B_446,'#skF_3')),k2_tarski(B_446,'#skF_3')) = k3_xboole_0('#skF_1',k2_tarski(B_446,'#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_12799,c_18])).

tff(c_12825,plain,(
    ! [B_447] : k3_xboole_0('#skF_1',k2_tarski(B_447,'#skF_3')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10576,c_12805])).

tff(c_12830,plain,(
    ! [B_447] : k4_xboole_0('#skF_1',k2_tarski(B_447,'#skF_3')) = k5_xboole_0('#skF_1','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_12825,c_4])).

tff(c_12838,plain,(
    ! [B_447] : k4_xboole_0('#skF_1',k2_tarski(B_447,'#skF_3')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_12830])).

tff(c_12843,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12838,c_10119])).

tff(c_12845,plain,(
    k1_tarski('#skF_5') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_56,plain,
    ( k2_tarski('#skF_2','#skF_3') = '#skF_1'
    | k1_tarski('#skF_3') = '#skF_1'
    | k1_tarski('#skF_2') = '#skF_1'
    | k1_xboole_0 = '#skF_1'
    | k1_tarski('#skF_5') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_13552,plain,
    ( k2_tarski('#skF_2','#skF_3') = '#skF_1'
    | k1_tarski('#skF_3') = '#skF_1'
    | k1_tarski('#skF_2') = '#skF_1'
    | k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12845,c_56])).

tff(c_13553,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_13552])).

tff(c_13570,plain,(
    ! [A_15] : k5_xboole_0(A_15,A_15) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_13553,c_16])).

tff(c_13610,plain,(
    ! [A_477] : k5_xboole_0(A_477,A_477) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_13553,c_16])).

tff(c_13632,plain,(
    ! [A_477] : k5_xboole_0('#skF_1',k2_xboole_0(A_477,A_477)) = k3_xboole_0(A_477,A_477) ),
    inference(superposition,[status(thm),theory(equality)],[c_13610,c_18])).

tff(c_13649,plain,(
    ! [A_477] : k5_xboole_0('#skF_1',A_477) = A_477 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_198,c_13632])).

tff(c_14458,plain,(
    ! [B_513,C_514] : k2_xboole_0('#skF_1',k2_tarski(B_513,C_514)) = k2_tarski(B_513,C_514) ),
    inference(demodulation,[status(thm),theory(equality)],[c_13553,c_159])).

tff(c_14464,plain,(
    ! [B_513,C_514] : k5_xboole_0(k5_xboole_0('#skF_1',k2_tarski(B_513,C_514)),k2_tarski(B_513,C_514)) = k3_xboole_0('#skF_1',k2_tarski(B_513,C_514)) ),
    inference(superposition,[status(thm),theory(equality)],[c_14458,c_18])).

tff(c_14478,plain,(
    ! [B_513,C_514] : k3_xboole_0('#skF_1',k2_tarski(B_513,C_514)) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_13570,c_13649,c_14464])).

tff(c_13671,plain,(
    ! [A_481] : k5_xboole_0('#skF_1',A_481) = A_481 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_198,c_13632])).

tff(c_13729,plain,(
    ! [B_4] : k4_xboole_0('#skF_1',B_4) = k3_xboole_0('#skF_1',B_4) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_13671])).

tff(c_12844,plain,(
    k4_xboole_0('#skF_1',k2_tarski('#skF_2','#skF_3')) != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_13559,plain,(
    k4_xboole_0('#skF_1',k2_tarski('#skF_2','#skF_3')) != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_13553,c_12844])).

tff(c_13878,plain,(
    k3_xboole_0('#skF_1',k2_tarski('#skF_2','#skF_3')) != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_13729,c_13559])).

tff(c_14494,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14478,c_13878])).

tff(c_14495,plain,
    ( k1_tarski('#skF_2') = '#skF_1'
    | k1_tarski('#skF_3') = '#skF_1'
    | k2_tarski('#skF_2','#skF_3') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_13552])).

tff(c_14846,plain,(
    k2_tarski('#skF_2','#skF_3') = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_14495])).

tff(c_14847,plain,(
    k4_xboole_0('#skF_1','#skF_1') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14846,c_12844])).

tff(c_14850,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_233,c_14847])).

tff(c_14851,plain,
    ( k1_tarski('#skF_3') = '#skF_1'
    | k1_tarski('#skF_2') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_14495])).

tff(c_14853,plain,(
    k1_tarski('#skF_2') = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_14851])).

tff(c_14936,plain,(
    ! [C_534] : r1_tarski('#skF_1',k2_tarski('#skF_2',C_534)) ),
    inference(superposition,[status(thm),theory(equality)],[c_14853,c_42])).

tff(c_15369,plain,(
    ! [C_559] : k2_xboole_0('#skF_1',k2_tarski('#skF_2',C_559)) = k2_tarski('#skF_2',C_559) ),
    inference(resolution,[status(thm)],[c_14936,c_65])).

tff(c_15375,plain,(
    ! [C_559] : k5_xboole_0(k5_xboole_0('#skF_1',k2_tarski('#skF_2',C_559)),k2_tarski('#skF_2',C_559)) = k3_xboole_0('#skF_1',k2_tarski('#skF_2',C_559)) ),
    inference(superposition,[status(thm),theory(equality)],[c_15369,c_18])).

tff(c_15396,plain,(
    ! [C_560] : k3_xboole_0('#skF_1',k2_tarski('#skF_2',C_560)) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_13510,c_15375])).

tff(c_15401,plain,(
    ! [C_560] : k4_xboole_0('#skF_1',k2_tarski('#skF_2',C_560)) = k5_xboole_0('#skF_1','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_15396,c_4])).

tff(c_15409,plain,(
    ! [C_560] : k4_xboole_0('#skF_1',k2_tarski('#skF_2',C_560)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_15401])).

tff(c_15414,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_15409,c_12844])).

tff(c_15415,plain,(
    k1_tarski('#skF_3') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_14851])).

tff(c_15490,plain,(
    ! [B_566] : r1_tarski('#skF_1',k2_tarski(B_566,'#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_15415,c_40])).

tff(c_16037,plain,(
    ! [B_591] : k2_xboole_0('#skF_1',k2_tarski(B_591,'#skF_3')) = k2_tarski(B_591,'#skF_3') ),
    inference(resolution,[status(thm)],[c_15490,c_65])).

tff(c_16047,plain,(
    ! [B_591] : k5_xboole_0(k5_xboole_0('#skF_1',k2_tarski(B_591,'#skF_3')),k2_tarski(B_591,'#skF_3')) = k3_xboole_0('#skF_1',k2_tarski(B_591,'#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_16037,c_18])).

tff(c_16082,plain,(
    ! [B_599] : k3_xboole_0('#skF_1',k2_tarski(B_599,'#skF_3')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_13510,c_16047])).

tff(c_16090,plain,(
    ! [B_599] : k4_xboole_0('#skF_1',k2_tarski(B_599,'#skF_3')) = k5_xboole_0('#skF_1','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_16082,c_4])).

tff(c_16102,plain,(
    ! [B_599] : k4_xboole_0('#skF_1',k2_tarski(B_599,'#skF_3')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_16090])).

tff(c_16108,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_16102,c_12844])).

tff(c_16110,plain,(
    k1_tarski('#skF_6') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_52,plain,
    ( k2_tarski('#skF_2','#skF_3') = '#skF_1'
    | k1_tarski('#skF_3') = '#skF_1'
    | k1_tarski('#skF_2') = '#skF_1'
    | k1_xboole_0 = '#skF_1'
    | k1_tarski('#skF_6') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_17029,plain,
    ( k2_tarski('#skF_2','#skF_3') = '#skF_1'
    | k1_tarski('#skF_3') = '#skF_1'
    | k1_tarski('#skF_2') = '#skF_1'
    | k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_16110,c_52])).

tff(c_17030,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_17029])).

tff(c_16685,plain,(
    ! [A_625,B_626] : k5_xboole_0(k5_xboole_0(A_625,B_626),k2_xboole_0(A_625,B_626)) = k3_xboole_0(A_625,B_626) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_16724,plain,(
    ! [B_47,C_48] : k5_xboole_0(k5_xboole_0(k1_xboole_0,k2_tarski(B_47,C_48)),k2_tarski(B_47,C_48)) = k3_xboole_0(k1_xboole_0,k2_tarski(B_47,C_48)) ),
    inference(superposition,[status(thm),theory(equality)],[c_159,c_16685])).

tff(c_16759,plain,(
    ! [B_47,C_48] : k3_xboole_0(k1_xboole_0,k2_tarski(B_47,C_48)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_16538,c_16724])).

tff(c_17033,plain,(
    ! [B_47,C_48] : k3_xboole_0('#skF_1',k2_tarski(B_47,C_48)) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_17030,c_17030,c_16759])).

tff(c_17092,plain,(
    ! [A_643] : k5_xboole_0(A_643,A_643) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_17030,c_16])).

tff(c_17104,plain,(
    ! [A_643] : k5_xboole_0('#skF_1',k2_xboole_0(A_643,A_643)) = k3_xboole_0(A_643,A_643) ),
    inference(superposition,[status(thm),theory(equality)],[c_17092,c_18])).

tff(c_17153,plain,(
    ! [A_647] : k5_xboole_0('#skF_1',A_647) = A_647 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_198,c_17104])).

tff(c_17211,plain,(
    ! [B_4] : k4_xboole_0('#skF_1',B_4) = k3_xboole_0('#skF_1',B_4) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_17153])).

tff(c_16109,plain,(
    k4_xboole_0('#skF_1',k2_tarski('#skF_2','#skF_3')) != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_17044,plain,(
    k4_xboole_0('#skF_1',k2_tarski('#skF_2','#skF_3')) != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_17030,c_16109])).

tff(c_17440,plain,(
    k3_xboole_0('#skF_1',k2_tarski('#skF_2','#skF_3')) != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_17211,c_17044])).

tff(c_17443,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_17033,c_17440])).

tff(c_17444,plain,
    ( k1_tarski('#skF_2') = '#skF_1'
    | k1_tarski('#skF_3') = '#skF_1'
    | k2_tarski('#skF_2','#skF_3') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_17029])).

tff(c_17837,plain,(
    k2_tarski('#skF_2','#skF_3') = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_17444])).

tff(c_17838,plain,(
    k4_xboole_0('#skF_1','#skF_1') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_17837,c_16109])).

tff(c_17841,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_16181,c_17838])).

tff(c_17842,plain,
    ( k1_tarski('#skF_3') = '#skF_1'
    | k1_tarski('#skF_2') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_17444])).

tff(c_17844,plain,(
    k1_tarski('#skF_2') = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_17842])).

tff(c_17935,plain,(
    ! [C_680] : r1_tarski('#skF_1',k2_tarski('#skF_2',C_680)) ),
    inference(superposition,[status(thm),theory(equality)],[c_17844,c_42])).

tff(c_18219,plain,(
    ! [C_700] : k2_xboole_0('#skF_1',k2_tarski('#skF_2',C_700)) = k2_tarski('#skF_2',C_700) ),
    inference(resolution,[status(thm)],[c_17935,c_65])).

tff(c_18229,plain,(
    ! [C_700] : k5_xboole_0(k5_xboole_0('#skF_1',k2_tarski('#skF_2',C_700)),k2_tarski('#skF_2',C_700)) = k3_xboole_0('#skF_1',k2_tarski('#skF_2',C_700)) ),
    inference(superposition,[status(thm),theory(equality)],[c_18219,c_18])).

tff(c_18255,plain,(
    ! [C_701] : k3_xboole_0('#skF_1',k2_tarski('#skF_2',C_701)) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_16919,c_18229])).

tff(c_18263,plain,(
    ! [C_701] : k4_xboole_0('#skF_1',k2_tarski('#skF_2',C_701)) = k5_xboole_0('#skF_1','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_18255,c_4])).

tff(c_18275,plain,(
    ! [C_701] : k4_xboole_0('#skF_1',k2_tarski('#skF_2',C_701)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_18263])).

tff(c_18281,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_18275,c_16109])).

tff(c_18282,plain,(
    k1_tarski('#skF_3') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_17842])).

tff(c_18382,plain,(
    ! [B_708] : r1_tarski('#skF_1',k2_tarski(B_708,'#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_18282,c_40])).

tff(c_18617,plain,(
    ! [B_731] : k2_xboole_0('#skF_1',k2_tarski(B_731,'#skF_3')) = k2_tarski(B_731,'#skF_3') ),
    inference(resolution,[status(thm)],[c_18382,c_65])).

tff(c_18627,plain,(
    ! [B_731] : k5_xboole_0(k5_xboole_0('#skF_1',k2_tarski(B_731,'#skF_3')),k2_tarski(B_731,'#skF_3')) = k3_xboole_0('#skF_1',k2_tarski(B_731,'#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_18617,c_18])).

tff(c_18653,plain,(
    ! [B_732] : k3_xboole_0('#skF_1',k2_tarski(B_732,'#skF_3')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_16919,c_18627])).

tff(c_18661,plain,(
    ! [B_732] : k4_xboole_0('#skF_1',k2_tarski(B_732,'#skF_3')) = k5_xboole_0('#skF_1','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_18653,c_4])).

tff(c_18673,plain,(
    ! [B_732] : k4_xboole_0('#skF_1',k2_tarski(B_732,'#skF_3')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_18661])).

tff(c_18679,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_18673,c_16109])).

tff(c_18681,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_18685,plain,(
    ! [A_15] : k5_xboole_0(A_15,A_15) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_18681,c_16])).

tff(c_18684,plain,(
    ! [A_9] : k5_xboole_0(A_9,'#skF_4') = A_9 ),
    inference(demodulation,[status(thm),theory(equality)],[c_18681,c_10])).

tff(c_18942,plain,(
    ! [A_762,B_763,C_764] : k5_xboole_0(k5_xboole_0(A_762,B_763),C_764) = k5_xboole_0(A_762,k5_xboole_0(B_763,C_764)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_19269,plain,(
    ! [A_771,C_772] : k5_xboole_0(A_771,k5_xboole_0(A_771,C_772)) = k5_xboole_0('#skF_4',C_772) ),
    inference(superposition,[status(thm),theory(equality)],[c_18685,c_18942])).

tff(c_19356,plain,(
    ! [A_15] : k5_xboole_0(A_15,'#skF_4') = k5_xboole_0('#skF_4',A_15) ),
    inference(superposition,[status(thm),theory(equality)],[c_18685,c_19269])).

tff(c_19382,plain,(
    ! [A_15] : k5_xboole_0('#skF_4',A_15) = A_15 ),
    inference(demodulation,[status(thm),theory(equality)],[c_18684,c_19356])).

tff(c_18976,plain,(
    ! [A_15,C_764] : k5_xboole_0(A_15,k5_xboole_0(A_15,C_764)) = k5_xboole_0('#skF_4',C_764) ),
    inference(superposition,[status(thm),theory(equality)],[c_18685,c_18942])).

tff(c_19384,plain,(
    ! [A_15,C_764] : k5_xboole_0(A_15,k5_xboole_0(A_15,C_764)) = C_764 ),
    inference(demodulation,[status(thm),theory(equality)],[c_19382,c_18976])).

tff(c_18956,plain,(
    ! [A_762,B_763] : k5_xboole_0(A_762,k5_xboole_0(B_763,k5_xboole_0(A_762,B_763))) = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_18942,c_18685])).

tff(c_19589,plain,(
    ! [A_780,C_781] : k5_xboole_0(A_780,k5_xboole_0(A_780,C_781)) = C_781 ),
    inference(demodulation,[status(thm),theory(equality)],[c_19382,c_18976])).

tff(c_19639,plain,(
    ! [B_763,A_762] : k5_xboole_0(B_763,k5_xboole_0(A_762,B_763)) = k5_xboole_0(A_762,'#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_18956,c_19589])).

tff(c_19766,plain,(
    ! [B_791,A_792] : k5_xboole_0(B_791,k5_xboole_0(A_792,B_791)) = A_792 ),
    inference(demodulation,[status(thm),theory(equality)],[c_18684,c_19639])).

tff(c_19802,plain,(
    ! [A_15,C_764] : k5_xboole_0(k5_xboole_0(A_15,C_764),C_764) = A_15 ),
    inference(superposition,[status(thm),theory(equality)],[c_19384,c_19766])).

tff(c_18823,plain,(
    ! [A_752,B_753] : k5_xboole_0(A_752,k3_xboole_0(A_752,B_753)) = k4_xboole_0(A_752,B_753) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_18832,plain,(
    ! [A_1] : k5_xboole_0(A_1,A_1) = k4_xboole_0(A_1,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_18823])).

tff(c_18835,plain,(
    ! [A_1] : k4_xboole_0(A_1,A_1) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_18685,c_18832])).

tff(c_18683,plain,(
    ! [B_47,C_48] : r1_tarski('#skF_4',k2_tarski(B_47,C_48)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18681,c_44])).

tff(c_18738,plain,(
    ! [A_743,B_744] :
      ( k2_xboole_0(A_743,B_744) = B_744
      | ~ r1_tarski(A_743,B_744) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_8])).

tff(c_18763,plain,(
    ! [B_47,C_48] : k2_xboole_0('#skF_4',k2_tarski(B_47,C_48)) = k2_tarski(B_47,C_48) ),
    inference(resolution,[status(thm)],[c_18683,c_18738])).

tff(c_19450,plain,(
    ! [A_774,B_775] : k5_xboole_0(k5_xboole_0(A_774,B_775),k2_xboole_0(A_774,B_775)) = k3_xboole_0(A_774,B_775) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_19487,plain,(
    ! [B_47,C_48] : k5_xboole_0(k5_xboole_0('#skF_4',k2_tarski(B_47,C_48)),k2_tarski(B_47,C_48)) = k3_xboole_0('#skF_4',k2_tarski(B_47,C_48)) ),
    inference(superposition,[status(thm),theory(equality)],[c_18763,c_19450])).

tff(c_19515,plain,(
    ! [B_47,C_48] : k3_xboole_0('#skF_4',k2_tarski(B_47,C_48)) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_18685,c_19382,c_19487])).

tff(c_19390,plain,(
    ! [A_773] : k5_xboole_0('#skF_4',A_773) = A_773 ),
    inference(demodulation,[status(thm),theory(equality)],[c_18684,c_19356])).

tff(c_19430,plain,(
    ! [B_4] : k4_xboole_0('#skF_4',B_4) = k3_xboole_0('#skF_4',B_4) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_19390])).

tff(c_60,plain,
    ( k2_tarski('#skF_2','#skF_3') = '#skF_1'
    | k1_tarski('#skF_3') = '#skF_1'
    | k1_tarski('#skF_2') = '#skF_1'
    | k1_xboole_0 = '#skF_1'
    | k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_19844,plain,
    ( k2_tarski('#skF_2','#skF_3') = '#skF_1'
    | k1_tarski('#skF_3') = '#skF_1'
    | k1_tarski('#skF_2') = '#skF_1'
    | '#skF_1' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_18681,c_18681,c_60])).

tff(c_19845,plain,(
    '#skF_1' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_19844])).

tff(c_18680,plain,(
    k4_xboole_0('#skF_1',k2_tarski('#skF_2','#skF_3')) != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_18727,plain,(
    k4_xboole_0('#skF_1',k2_tarski('#skF_2','#skF_3')) != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_18681,c_18680])).

tff(c_19846,plain,(
    k4_xboole_0('#skF_4',k2_tarski('#skF_2','#skF_3')) != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_19845,c_18727])).

tff(c_19849,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_19515,c_19430,c_19846])).

tff(c_19850,plain,
    ( k1_tarski('#skF_2') = '#skF_1'
    | k1_tarski('#skF_3') = '#skF_1'
    | k2_tarski('#skF_2','#skF_3') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_19844])).

tff(c_19969,plain,(
    k2_tarski('#skF_2','#skF_3') = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_19850])).

tff(c_19970,plain,(
    k4_xboole_0('#skF_1','#skF_1') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_19969,c_18727])).

tff(c_19973,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_18835,c_19970])).

tff(c_19974,plain,
    ( k1_tarski('#skF_3') = '#skF_1'
    | k1_tarski('#skF_2') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_19850])).

tff(c_19976,plain,(
    k1_tarski('#skF_2') = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_19974])).

tff(c_20068,plain,(
    ! [C_801] : r1_tarski('#skF_1',k2_tarski('#skF_2',C_801)) ),
    inference(superposition,[status(thm),theory(equality)],[c_19976,c_42])).

tff(c_20383,plain,(
    ! [C_820] : k2_xboole_0('#skF_1',k2_tarski('#skF_2',C_820)) = k2_tarski('#skF_2',C_820) ),
    inference(resolution,[status(thm)],[c_20068,c_65])).

tff(c_20389,plain,(
    ! [C_820] : k5_xboole_0(k5_xboole_0('#skF_1',k2_tarski('#skF_2',C_820)),k2_tarski('#skF_2',C_820)) = k3_xboole_0('#skF_1',k2_tarski('#skF_2',C_820)) ),
    inference(superposition,[status(thm),theory(equality)],[c_20383,c_18])).

tff(c_20409,plain,(
    ! [C_821] : k3_xboole_0('#skF_1',k2_tarski('#skF_2',C_821)) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_19802,c_20389])).

tff(c_20414,plain,(
    ! [C_821] : k4_xboole_0('#skF_1',k2_tarski('#skF_2',C_821)) = k5_xboole_0('#skF_1','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_20409,c_4])).

tff(c_20422,plain,(
    ! [C_821] : k4_xboole_0('#skF_1',k2_tarski('#skF_2',C_821)) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_18685,c_20414])).

tff(c_20427,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_20422,c_18727])).

tff(c_20428,plain,(
    k1_tarski('#skF_3') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_19974])).

tff(c_20531,plain,(
    ! [B_828] : r1_tarski('#skF_1',k2_tarski(B_828,'#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_20428,c_40])).

tff(c_20896,plain,(
    ! [B_849] : k2_xboole_0('#skF_1',k2_tarski(B_849,'#skF_3')) = k2_tarski(B_849,'#skF_3') ),
    inference(resolution,[status(thm)],[c_20531,c_65])).

tff(c_20906,plain,(
    ! [B_849] : k5_xboole_0(k5_xboole_0('#skF_1',k2_tarski(B_849,'#skF_3')),k2_tarski(B_849,'#skF_3')) = k3_xboole_0('#skF_1',k2_tarski(B_849,'#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_20896,c_18])).

tff(c_20932,plain,(
    ! [B_850] : k3_xboole_0('#skF_1',k2_tarski(B_850,'#skF_3')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_19802,c_20906])).

tff(c_20940,plain,(
    ! [B_850] : k4_xboole_0('#skF_1',k2_tarski(B_850,'#skF_3')) = k5_xboole_0('#skF_1','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_20932,c_4])).

tff(c_20952,plain,(
    ! [B_850] : k4_xboole_0('#skF_1',k2_tarski(B_850,'#skF_3')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_18685,c_20940])).

tff(c_20958,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_20952,c_18727])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n009.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 11:06:11 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.89/3.08  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.89/3.13  
% 8.89/3.13  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.89/3.13  %$ r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 8.89/3.13  
% 8.89/3.13  %Foreground sorts:
% 8.89/3.13  
% 8.89/3.13  
% 8.89/3.13  %Background operators:
% 8.89/3.13  
% 8.89/3.13  
% 8.89/3.13  %Foreground operators:
% 8.89/3.13  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.89/3.13  tff(k1_tarski, type, k1_tarski: $i > $i).
% 8.89/3.13  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 8.89/3.13  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 8.89/3.13  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 8.89/3.13  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 8.89/3.13  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.89/3.13  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 8.89/3.13  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 8.89/3.13  tff('#skF_5', type, '#skF_5': $i).
% 8.89/3.13  tff('#skF_6', type, '#skF_6': $i).
% 8.89/3.13  tff('#skF_2', type, '#skF_2': $i).
% 8.89/3.13  tff('#skF_3', type, '#skF_3': $i).
% 8.89/3.13  tff('#skF_1', type, '#skF_1': $i).
% 8.89/3.13  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 8.89/3.13  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 8.89/3.13  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.89/3.13  tff(k3_tarski, type, k3_tarski: $i > $i).
% 8.89/3.13  tff('#skF_4', type, '#skF_4': $i).
% 8.89/3.13  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.89/3.13  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 8.89/3.13  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 8.89/3.13  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 8.89/3.13  
% 9.26/3.17  tff(f_43, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 9.26/3.17  tff(f_37, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 9.26/3.17  tff(f_41, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_xboole_1)).
% 9.26/3.17  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 9.26/3.17  tff(f_29, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 9.26/3.17  tff(f_61, axiom, (![A]: (k3_tarski(k1_tarski(A)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_zfmisc_1)).
% 9.26/3.17  tff(f_47, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 9.26/3.17  tff(f_59, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 9.26/3.17  tff(f_45, axiom, (![A, B]: (k3_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k2_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t95_xboole_1)).
% 9.26/3.17  tff(f_92, negated_conjecture, ~(![A, B, C]: ((k4_xboole_0(A, k2_tarski(B, C)) = k1_xboole_0) <=> ~(((~(A = k1_xboole_0) & ~(A = k1_tarski(B))) & ~(A = k1_tarski(C))) & ~(A = k2_tarski(B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t75_zfmisc_1)).
% 9.26/3.17  tff(f_39, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 9.26/3.17  tff(f_76, axiom, (![A, B, C]: (r1_tarski(A, k2_tarski(B, C)) <=> ~(((~(A = k1_xboole_0) & ~(A = k1_tarski(B))) & ~(A = k1_tarski(C))) & ~(A = k2_tarski(B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t42_zfmisc_1)).
% 9.26/3.17  tff(f_31, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 9.26/3.17  tff(f_35, axiom, (![A, B]: (r1_tarski(A, B) => (B = k2_xboole_0(A, k4_xboole_0(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t45_xboole_1)).
% 9.26/3.17  tff(c_16, plain, (![A_15]: (k5_xboole_0(A_15, A_15)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_43])).
% 9.26/3.17  tff(c_10, plain, (![A_9]: (k5_xboole_0(A_9, k1_xboole_0)=A_9)), inference(cnfTransformation, [status(thm)], [f_37])).
% 9.26/3.17  tff(c_16238, plain, (![A_610, B_611, C_612]: (k5_xboole_0(k5_xboole_0(A_610, B_611), C_612)=k5_xboole_0(A_610, k5_xboole_0(B_611, C_612)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 9.26/3.17  tff(c_16454, plain, (![A_620, C_621]: (k5_xboole_0(A_620, k5_xboole_0(A_620, C_621))=k5_xboole_0(k1_xboole_0, C_621))), inference(superposition, [status(thm), theory('equality')], [c_16, c_16238])).
% 9.26/3.17  tff(c_16522, plain, (![A_15]: (k5_xboole_0(k1_xboole_0, A_15)=k5_xboole_0(A_15, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_16, c_16454])).
% 9.26/3.17  tff(c_16538, plain, (![A_15]: (k5_xboole_0(k1_xboole_0, A_15)=A_15)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_16522])).
% 9.26/3.17  tff(c_16279, plain, (![A_15, C_612]: (k5_xboole_0(A_15, k5_xboole_0(A_15, C_612))=k5_xboole_0(k1_xboole_0, C_612))), inference(superposition, [status(thm), theory('equality')], [c_16, c_16238])).
% 9.26/3.17  tff(c_16539, plain, (![A_15, C_612]: (k5_xboole_0(A_15, k5_xboole_0(A_15, C_612))=C_612)), inference(demodulation, [status(thm), theory('equality')], [c_16538, c_16279])).
% 9.26/3.17  tff(c_16256, plain, (![A_610, B_611]: (k5_xboole_0(A_610, k5_xboole_0(B_611, k5_xboole_0(A_610, B_611)))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_16238, c_16])).
% 9.26/3.17  tff(c_16602, plain, (![A_623, C_624]: (k5_xboole_0(A_623, k5_xboole_0(A_623, C_624))=C_624)), inference(demodulation, [status(thm), theory('equality')], [c_16538, c_16279])).
% 9.26/3.17  tff(c_16646, plain, (![B_611, A_610]: (k5_xboole_0(B_611, k5_xboole_0(A_610, B_611))=k5_xboole_0(A_610, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_16256, c_16602])).
% 9.26/3.17  tff(c_16880, plain, (![B_637, A_638]: (k5_xboole_0(B_637, k5_xboole_0(A_638, B_637))=A_638)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_16646])).
% 9.26/3.17  tff(c_16919, plain, (![A_15, C_612]: (k5_xboole_0(k5_xboole_0(A_15, C_612), C_612)=A_15)), inference(superposition, [status(thm), theory('equality')], [c_16539, c_16880])).
% 9.26/3.17  tff(c_2, plain, (![A_1]: (k3_xboole_0(A_1, A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 9.26/3.17  tff(c_16169, plain, (![A_602, B_603]: (k5_xboole_0(A_602, k3_xboole_0(A_602, B_603))=k4_xboole_0(A_602, B_603))), inference(cnfTransformation, [status(thm)], [f_29])).
% 9.26/3.17  tff(c_16178, plain, (![A_1]: (k5_xboole_0(A_1, A_1)=k4_xboole_0(A_1, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_16169])).
% 9.26/3.17  tff(c_16181, plain, (![A_1]: (k4_xboole_0(A_1, A_1)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_16178])).
% 9.26/3.17  tff(c_34, plain, (![A_45]: (k3_tarski(k1_tarski(A_45))=A_45)), inference(cnfTransformation, [status(thm)], [f_61])).
% 9.26/3.17  tff(c_20, plain, (![A_18]: (k2_tarski(A_18, A_18)=k1_tarski(A_18))), inference(cnfTransformation, [status(thm)], [f_47])).
% 9.26/3.17  tff(c_186, plain, (![A_69, B_70]: (k3_tarski(k2_tarski(A_69, B_70))=k2_xboole_0(A_69, B_70))), inference(cnfTransformation, [status(thm)], [f_59])).
% 9.26/3.17  tff(c_195, plain, (![A_18]: (k3_tarski(k1_tarski(A_18))=k2_xboole_0(A_18, A_18))), inference(superposition, [status(thm), theory('equality')], [c_20, c_186])).
% 9.26/3.17  tff(c_198, plain, (![A_18]: (k2_xboole_0(A_18, A_18)=A_18)), inference(demodulation, [status(thm), theory('equality')], [c_34, c_195])).
% 9.26/3.17  tff(c_13021, plain, (![A_456, B_457]: (k5_xboole_0(k5_xboole_0(A_456, B_457), k2_xboole_0(A_456, B_457))=k3_xboole_0(A_456, B_457))), inference(cnfTransformation, [status(thm)], [f_45])).
% 9.26/3.17  tff(c_13075, plain, (![A_15]: (k5_xboole_0(k1_xboole_0, k2_xboole_0(A_15, A_15))=k3_xboole_0(A_15, A_15))), inference(superposition, [status(thm), theory('equality')], [c_16, c_13021])).
% 9.26/3.17  tff(c_13081, plain, (![A_15]: (k5_xboole_0(k1_xboole_0, A_15)=A_15)), inference(demodulation, [status(thm), theory('equality')], [c_2, c_198, c_13075])).
% 9.26/3.17  tff(c_13082, plain, (![A_458, B_459, C_460]: (k5_xboole_0(k5_xboole_0(A_458, B_459), C_460)=k5_xboole_0(A_458, k5_xboole_0(B_459, C_460)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 9.26/3.17  tff(c_13136, plain, (![A_15, C_460]: (k5_xboole_0(A_15, k5_xboole_0(A_15, C_460))=k5_xboole_0(k1_xboole_0, C_460))), inference(superposition, [status(thm), theory('equality')], [c_16, c_13082])).
% 9.26/3.17  tff(c_13310, plain, (![A_15, C_460]: (k5_xboole_0(A_15, k5_xboole_0(A_15, C_460))=C_460)), inference(demodulation, [status(thm), theory('equality')], [c_13081, c_13136])).
% 9.26/3.17  tff(c_13376, plain, (![A_472, B_473]: (k5_xboole_0(A_472, k5_xboole_0(B_473, k5_xboole_0(A_472, B_473)))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_13082, c_16])).
% 9.26/3.17  tff(c_13384, plain, (![B_473, A_472]: (k5_xboole_0(B_473, k5_xboole_0(A_472, B_473))=k5_xboole_0(A_472, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_13376, c_13310])).
% 9.26/3.17  tff(c_13474, plain, (![B_474, A_475]: (k5_xboole_0(B_474, k5_xboole_0(A_475, B_474))=A_475)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_13384])).
% 9.26/3.17  tff(c_13510, plain, (![A_15, C_460]: (k5_xboole_0(k5_xboole_0(A_15, C_460), C_460)=A_15)), inference(superposition, [status(thm), theory('equality')], [c_13310, c_13474])).
% 9.26/3.17  tff(c_221, plain, (![A_73, B_74]: (k5_xboole_0(A_73, k3_xboole_0(A_73, B_74))=k4_xboole_0(A_73, B_74))), inference(cnfTransformation, [status(thm)], [f_29])).
% 9.26/3.17  tff(c_230, plain, (![A_1]: (k5_xboole_0(A_1, A_1)=k4_xboole_0(A_1, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_221])).
% 9.26/3.17  tff(c_233, plain, (![A_1]: (k4_xboole_0(A_1, A_1)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_230])).
% 9.26/3.17  tff(c_401, plain, (![A_89, B_90]: (k5_xboole_0(k5_xboole_0(A_89, B_90), k2_xboole_0(A_89, B_90))=k3_xboole_0(A_89, B_90))), inference(cnfTransformation, [status(thm)], [f_45])).
% 9.26/3.17  tff(c_446, plain, (![A_15]: (k5_xboole_0(k1_xboole_0, k2_xboole_0(A_15, A_15))=k3_xboole_0(A_15, A_15))), inference(superposition, [status(thm), theory('equality')], [c_16, c_401])).
% 9.26/3.17  tff(c_452, plain, (![A_15]: (k5_xboole_0(k1_xboole_0, A_15)=A_15)), inference(demodulation, [status(thm), theory('equality')], [c_198, c_2, c_446])).
% 9.26/3.17  tff(c_493, plain, (![A_92, B_93, C_94]: (k5_xboole_0(k5_xboole_0(A_92, B_93), C_94)=k5_xboole_0(A_92, k5_xboole_0(B_93, C_94)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 9.26/3.17  tff(c_550, plain, (![A_15, C_94]: (k5_xboole_0(A_15, k5_xboole_0(A_15, C_94))=k5_xboole_0(k1_xboole_0, C_94))), inference(superposition, [status(thm), theory('equality')], [c_16, c_493])).
% 9.26/3.17  tff(c_563, plain, (![A_15, C_94]: (k5_xboole_0(A_15, k5_xboole_0(A_15, C_94))=C_94)), inference(demodulation, [status(thm), theory('equality')], [c_452, c_550])).
% 9.26/3.17  tff(c_10442, plain, (![A_346, B_347]: (k5_xboole_0(A_346, k5_xboole_0(B_347, k5_xboole_0(A_346, B_347)))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_493, c_16])).
% 9.26/3.17  tff(c_10450, plain, (![B_347, A_346]: (k5_xboole_0(B_347, k5_xboole_0(A_346, B_347))=k5_xboole_0(A_346, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_10442, c_563])).
% 9.26/3.17  tff(c_10540, plain, (![B_348, A_349]: (k5_xboole_0(B_348, k5_xboole_0(A_349, B_348))=A_349)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_10450])).
% 9.26/3.17  tff(c_10576, plain, (![A_15, C_94]: (k5_xboole_0(k5_xboole_0(A_15, C_94), C_94)=A_15)), inference(superposition, [status(thm), theory('equality')], [c_563, c_10540])).
% 9.26/3.17  tff(c_58, plain, (k4_xboole_0('#skF_1', k2_tarski('#skF_2', '#skF_3'))!=k1_xboole_0 | k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_92])).
% 9.26/3.17  tff(c_128, plain, (k1_xboole_0!='#skF_4'), inference(splitLeft, [status(thm)], [c_58])).
% 9.26/3.17  tff(c_54, plain, (k4_xboole_0('#skF_1', k2_tarski('#skF_2', '#skF_3'))!=k1_xboole_0 | k1_tarski('#skF_5')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_92])).
% 9.26/3.17  tff(c_348, plain, (k1_tarski('#skF_5')!='#skF_4'), inference(splitLeft, [status(thm)], [c_54])).
% 9.26/3.17  tff(c_50, plain, (k4_xboole_0('#skF_1', k2_tarski('#skF_2', '#skF_3'))!=k1_xboole_0 | k1_tarski('#skF_6')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_92])).
% 9.26/3.17  tff(c_219, plain, (k1_tarski('#skF_6')!='#skF_4'), inference(splitLeft, [status(thm)], [c_50])).
% 9.26/3.17  tff(c_46, plain, (k4_xboole_0('#skF_1', k2_tarski('#skF_2', '#skF_3'))!=k1_xboole_0 | k2_tarski('#skF_5', '#skF_6')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_92])).
% 9.26/3.17  tff(c_587, plain, (k2_tarski('#skF_5', '#skF_6')!='#skF_4'), inference(splitLeft, [status(thm)], [c_46])).
% 9.26/3.17  tff(c_749, plain, (![A_105, B_106]: (k5_xboole_0(A_105, k5_xboole_0(B_106, k5_xboole_0(A_105, B_106)))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_493, c_16])).
% 9.26/3.17  tff(c_757, plain, (![B_106, A_105]: (k5_xboole_0(B_106, k5_xboole_0(A_105, B_106))=k5_xboole_0(A_105, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_749, c_563])).
% 9.26/3.17  tff(c_847, plain, (![B_107, A_108]: (k5_xboole_0(B_107, k5_xboole_0(A_108, B_107))=A_108)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_757])).
% 9.26/3.17  tff(c_883, plain, (![A_15, C_94]: (k5_xboole_0(k5_xboole_0(A_15, C_94), C_94)=A_15)), inference(superposition, [status(thm), theory('equality')], [c_563, c_847])).
% 9.26/3.17  tff(c_64, plain, (k2_tarski('#skF_2', '#skF_3')='#skF_1' | k1_tarski('#skF_3')='#skF_1' | k1_tarski('#skF_2')='#skF_1' | k1_xboole_0='#skF_1' | k4_xboole_0('#skF_4', k2_tarski('#skF_5', '#skF_6'))=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_92])).
% 9.26/3.17  tff(c_2471, plain, (k4_xboole_0('#skF_4', k2_tarski('#skF_5', '#skF_6'))=k1_xboole_0), inference(splitLeft, [status(thm)], [c_64])).
% 9.26/3.17  tff(c_4, plain, (![A_3, B_4]: (k5_xboole_0(A_3, k3_xboole_0(A_3, B_4))=k4_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 9.26/3.17  tff(c_18, plain, (![A_16, B_17]: (k5_xboole_0(k5_xboole_0(A_16, B_17), k2_xboole_0(A_16, B_17))=k3_xboole_0(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_45])).
% 9.26/3.17  tff(c_2676, plain, (![A_162, B_163]: (k5_xboole_0(A_162, k5_xboole_0(B_163, k2_xboole_0(A_162, B_163)))=k3_xboole_0(A_162, B_163))), inference(superposition, [status(thm), theory('equality')], [c_493, c_18])).
% 9.26/3.17  tff(c_2691, plain, (![B_163, A_162]: (k5_xboole_0(B_163, k2_xboole_0(A_162, B_163))=k5_xboole_0(A_162, k3_xboole_0(A_162, B_163)))), inference(superposition, [status(thm), theory('equality')], [c_2676, c_563])).
% 9.26/3.17  tff(c_3068, plain, (![B_172, A_173]: (k5_xboole_0(B_172, k2_xboole_0(A_173, B_172))=k4_xboole_0(A_173, B_172))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_2691])).
% 9.26/3.17  tff(c_3498, plain, (![B_183, A_184]: (k5_xboole_0(B_183, k4_xboole_0(A_184, B_183))=k2_xboole_0(A_184, B_183))), inference(superposition, [status(thm), theory('equality')], [c_3068, c_563])).
% 9.26/3.17  tff(c_3559, plain, (k5_xboole_0(k2_tarski('#skF_5', '#skF_6'), k1_xboole_0)=k2_xboole_0('#skF_4', k2_tarski('#skF_5', '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_2471, c_3498])).
% 9.26/3.17  tff(c_3600, plain, (k2_xboole_0('#skF_4', k2_tarski('#skF_5', '#skF_6'))=k2_tarski('#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_10, c_3559])).
% 9.26/3.17  tff(c_12, plain, (![A_10, B_11]: (r1_tarski(A_10, k2_xboole_0(A_10, B_11)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 9.26/3.17  tff(c_4490, plain, (r1_tarski('#skF_4', k2_tarski('#skF_5', '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_3600, c_12])).
% 9.26/3.17  tff(c_36, plain, (![B_47, C_48, A_46]: (k2_tarski(B_47, C_48)=A_46 | k1_tarski(C_48)=A_46 | k1_tarski(B_47)=A_46 | k1_xboole_0=A_46 | ~r1_tarski(A_46, k2_tarski(B_47, C_48)))), inference(cnfTransformation, [status(thm)], [f_76])).
% 9.26/3.17  tff(c_4652, plain, (k2_tarski('#skF_5', '#skF_6')='#skF_4' | k1_tarski('#skF_6')='#skF_4' | k1_tarski('#skF_5')='#skF_4' | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_4490, c_36])).
% 9.26/3.17  tff(c_4659, plain, $false, inference(negUnitSimplification, [status(thm)], [c_128, c_348, c_219, c_587, c_4652])).
% 9.26/3.17  tff(c_4660, plain, (k1_xboole_0='#skF_1' | k1_tarski('#skF_2')='#skF_1' | k1_tarski('#skF_3')='#skF_1' | k2_tarski('#skF_2', '#skF_3')='#skF_1'), inference(splitRight, [status(thm)], [c_64])).
% 9.26/3.17  tff(c_4663, plain, (k2_tarski('#skF_2', '#skF_3')='#skF_1'), inference(splitLeft, [status(thm)], [c_4660])).
% 9.26/3.17  tff(c_62, plain, (k4_xboole_0('#skF_1', k2_tarski('#skF_2', '#skF_3'))!=k1_xboole_0 | k4_xboole_0('#skF_4', k2_tarski('#skF_5', '#skF_6'))=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_92])).
% 9.26/3.17  tff(c_924, plain, (k4_xboole_0('#skF_1', k2_tarski('#skF_2', '#skF_3'))!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_62])).
% 9.26/3.17  tff(c_4664, plain, (k4_xboole_0('#skF_1', '#skF_1')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_4663, c_924])).
% 9.26/3.17  tff(c_4667, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_233, c_4664])).
% 9.26/3.17  tff(c_4668, plain, (k1_tarski('#skF_3')='#skF_1' | k1_tarski('#skF_2')='#skF_1' | k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_4660])).
% 9.26/3.17  tff(c_4670, plain, (k1_xboole_0='#skF_1'), inference(splitLeft, [status(thm)], [c_4668])).
% 9.26/3.17  tff(c_44, plain, (![B_47, C_48]: (r1_tarski(k1_xboole_0, k2_tarski(B_47, C_48)))), inference(cnfTransformation, [status(thm)], [f_76])).
% 9.26/3.17  tff(c_6, plain, (![A_5, B_6]: (k2_xboole_0(A_5, k4_xboole_0(B_6, A_5))=k2_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_31])).
% 9.26/3.17  tff(c_8, plain, (![A_7, B_8]: (k2_xboole_0(A_7, k4_xboole_0(B_8, A_7))=B_8 | ~r1_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_35])).
% 9.26/3.17  tff(c_135, plain, (![A_64, B_65]: (k2_xboole_0(A_64, B_65)=B_65 | ~r1_tarski(A_64, B_65))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_8])).
% 9.26/3.17  tff(c_159, plain, (![B_47, C_48]: (k2_xboole_0(k1_xboole_0, k2_tarski(B_47, C_48))=k2_tarski(B_47, C_48))), inference(resolution, [status(thm)], [c_44, c_135])).
% 9.26/3.17  tff(c_5180, plain, (![B_214, C_215]: (k2_xboole_0('#skF_1', k2_tarski(B_214, C_215))=k2_tarski(B_214, C_215))), inference(demodulation, [status(thm), theory('equality')], [c_4670, c_159])).
% 9.26/3.17  tff(c_5186, plain, (![B_214, C_215]: (k5_xboole_0(k5_xboole_0('#skF_1', k2_tarski(B_214, C_215)), k2_tarski(B_214, C_215))=k3_xboole_0('#skF_1', k2_tarski(B_214, C_215)))), inference(superposition, [status(thm), theory('equality')], [c_5180, c_18])).
% 9.26/3.17  tff(c_5200, plain, (![B_214, C_215]: (k3_xboole_0('#skF_1', k2_tarski(B_214, C_215))='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_883, c_5186])).
% 9.26/3.17  tff(c_4704, plain, (![A_200]: (k5_xboole_0(A_200, A_200)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_4670, c_16])).
% 9.26/3.17  tff(c_14, plain, (![A_12, B_13, C_14]: (k5_xboole_0(k5_xboole_0(A_12, B_13), C_14)=k5_xboole_0(A_12, k5_xboole_0(B_13, C_14)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 9.26/3.17  tff(c_4721, plain, (![A_200, C_14]: (k5_xboole_0(A_200, k5_xboole_0(A_200, C_14))=k5_xboole_0('#skF_1', C_14))), inference(superposition, [status(thm), theory('equality')], [c_4704, c_14])).
% 9.26/3.17  tff(c_4839, plain, (![C_202]: (k5_xboole_0('#skF_1', C_202)=C_202)), inference(demodulation, [status(thm), theory('equality')], [c_563, c_4721])).
% 9.26/3.17  tff(c_4890, plain, (![B_4]: (k4_xboole_0('#skF_1', B_4)=k3_xboole_0('#skF_1', B_4))), inference(superposition, [status(thm), theory('equality')], [c_4839, c_4])).
% 9.26/3.17  tff(c_4685, plain, (k4_xboole_0('#skF_1', k2_tarski('#skF_2', '#skF_3'))!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_4670, c_924])).
% 9.26/3.17  tff(c_5125, plain, (k3_xboole_0('#skF_1', k2_tarski('#skF_2', '#skF_3'))!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_4890, c_4685])).
% 9.26/3.17  tff(c_5341, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_5200, c_5125])).
% 9.26/3.17  tff(c_5342, plain, (k1_tarski('#skF_2')='#skF_1' | k1_tarski('#skF_3')='#skF_1'), inference(splitRight, [status(thm)], [c_4668])).
% 9.26/3.17  tff(c_5344, plain, (k1_tarski('#skF_3')='#skF_1'), inference(splitLeft, [status(thm)], [c_5342])).
% 9.26/3.17  tff(c_40, plain, (![C_48, B_47]: (r1_tarski(k1_tarski(C_48), k2_tarski(B_47, C_48)))), inference(cnfTransformation, [status(thm)], [f_76])).
% 9.26/3.17  tff(c_5524, plain, (![B_223]: (r1_tarski('#skF_1', k2_tarski(B_223, '#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_5344, c_40])).
% 9.26/3.17  tff(c_65, plain, (![A_7, B_8]: (k2_xboole_0(A_7, B_8)=B_8 | ~r1_tarski(A_7, B_8))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_8])).
% 9.26/3.17  tff(c_5558, plain, (![B_225]: (k2_xboole_0('#skF_1', k2_tarski(B_225, '#skF_3'))=k2_tarski(B_225, '#skF_3'))), inference(resolution, [status(thm)], [c_5524, c_65])).
% 9.26/3.17  tff(c_5564, plain, (![B_225]: (k5_xboole_0(k5_xboole_0('#skF_1', k2_tarski(B_225, '#skF_3')), k2_tarski(B_225, '#skF_3'))=k3_xboole_0('#skF_1', k2_tarski(B_225, '#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_5558, c_18])).
% 9.26/3.17  tff(c_5585, plain, (![B_226]: (k3_xboole_0('#skF_1', k2_tarski(B_226, '#skF_3'))='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_883, c_5564])).
% 9.26/3.17  tff(c_5599, plain, (![B_226]: (k4_xboole_0('#skF_1', k2_tarski(B_226, '#skF_3'))=k5_xboole_0('#skF_1', '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_5585, c_4])).
% 9.26/3.17  tff(c_5608, plain, (![B_226]: (k4_xboole_0('#skF_1', k2_tarski(B_226, '#skF_3'))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_5599])).
% 9.26/3.17  tff(c_5613, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_5608, c_924])).
% 9.26/3.17  tff(c_5614, plain, (k1_tarski('#skF_2')='#skF_1'), inference(splitRight, [status(thm)], [c_5342])).
% 9.26/3.17  tff(c_42, plain, (![B_47, C_48]: (r1_tarski(k1_tarski(B_47), k2_tarski(B_47, C_48)))), inference(cnfTransformation, [status(thm)], [f_76])).
% 9.26/3.17  tff(c_5811, plain, (![C_231]: (r1_tarski('#skF_1', k2_tarski('#skF_2', C_231)))), inference(superposition, [status(thm), theory('equality')], [c_5614, c_42])).
% 9.26/3.17  tff(c_5914, plain, (![C_235]: (k2_xboole_0('#skF_1', k2_tarski('#skF_2', C_235))=k2_tarski('#skF_2', C_235))), inference(resolution, [status(thm)], [c_5811, c_65])).
% 9.26/3.17  tff(c_5924, plain, (![C_235]: (k5_xboole_0(k5_xboole_0('#skF_1', k2_tarski('#skF_2', C_235)), k2_tarski('#skF_2', C_235))=k3_xboole_0('#skF_1', k2_tarski('#skF_2', C_235)))), inference(superposition, [status(thm), theory('equality')], [c_5914, c_18])).
% 9.26/3.17  tff(c_6251, plain, (![C_242]: (k3_xboole_0('#skF_1', k2_tarski('#skF_2', C_242))='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_883, c_5924])).
% 9.26/3.17  tff(c_6268, plain, (![C_242]: (k4_xboole_0('#skF_1', k2_tarski('#skF_2', C_242))=k5_xboole_0('#skF_1', '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_6251, c_4])).
% 9.26/3.17  tff(c_6281, plain, (![C_242]: (k4_xboole_0('#skF_1', k2_tarski('#skF_2', C_242))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_6268])).
% 9.26/3.17  tff(c_6290, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6281, c_924])).
% 9.26/3.17  tff(c_6291, plain, (k4_xboole_0('#skF_4', k2_tarski('#skF_5', '#skF_6'))=k1_xboole_0), inference(splitRight, [status(thm)], [c_62])).
% 9.26/3.17  tff(c_8086, plain, (![A_295, B_296]: (k5_xboole_0(A_295, k5_xboole_0(B_296, k2_xboole_0(A_295, B_296)))=k3_xboole_0(A_295, B_296))), inference(superposition, [status(thm), theory('equality')], [c_493, c_18])).
% 9.26/3.17  tff(c_8101, plain, (![B_296, A_295]: (k5_xboole_0(B_296, k2_xboole_0(A_295, B_296))=k5_xboole_0(A_295, k3_xboole_0(A_295, B_296)))), inference(superposition, [status(thm), theory('equality')], [c_8086, c_563])).
% 9.26/3.17  tff(c_8548, plain, (![B_309, A_310]: (k5_xboole_0(B_309, k2_xboole_0(A_310, B_309))=k4_xboole_0(A_310, B_309))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_8101])).
% 9.26/3.17  tff(c_8646, plain, (![B_311, A_312]: (k5_xboole_0(B_311, k4_xboole_0(A_312, B_311))=k2_xboole_0(A_312, B_311))), inference(superposition, [status(thm), theory('equality')], [c_8548, c_563])).
% 9.26/3.17  tff(c_8713, plain, (k5_xboole_0(k2_tarski('#skF_5', '#skF_6'), k1_xboole_0)=k2_xboole_0('#skF_4', k2_tarski('#skF_5', '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_6291, c_8646])).
% 9.26/3.17  tff(c_8746, plain, (k2_xboole_0('#skF_4', k2_tarski('#skF_5', '#skF_6'))=k2_tarski('#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_10, c_8713])).
% 9.26/3.17  tff(c_10093, plain, (r1_tarski('#skF_4', k2_tarski('#skF_5', '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_8746, c_12])).
% 9.26/3.17  tff(c_10111, plain, (k2_tarski('#skF_5', '#skF_6')='#skF_4' | k1_tarski('#skF_6')='#skF_4' | k1_tarski('#skF_5')='#skF_4' | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_10093, c_36])).
% 9.26/3.17  tff(c_10118, plain, $false, inference(negUnitSimplification, [status(thm)], [c_128, c_348, c_219, c_587, c_10111])).
% 9.26/3.17  tff(c_10120, plain, (k2_tarski('#skF_5', '#skF_6')='#skF_4'), inference(splitRight, [status(thm)], [c_46])).
% 9.26/3.17  tff(c_48, plain, (k2_tarski('#skF_2', '#skF_3')='#skF_1' | k1_tarski('#skF_3')='#skF_1' | k1_tarski('#skF_2')='#skF_1' | k1_xboole_0='#skF_1' | k2_tarski('#skF_5', '#skF_6')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_92])).
% 9.26/3.17  tff(c_10968, plain, (k2_tarski('#skF_2', '#skF_3')='#skF_1' | k1_tarski('#skF_3')='#skF_1' | k1_tarski('#skF_2')='#skF_1' | k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_10120, c_48])).
% 9.26/3.17  tff(c_10969, plain, (k1_xboole_0='#skF_1'), inference(splitLeft, [status(thm)], [c_10968])).
% 9.26/3.17  tff(c_11649, plain, (![B_388, C_389]: (k2_xboole_0('#skF_1', k2_tarski(B_388, C_389))=k2_tarski(B_388, C_389))), inference(demodulation, [status(thm), theory('equality')], [c_10969, c_159])).
% 9.26/3.17  tff(c_11655, plain, (![B_388, C_389]: (k5_xboole_0(k5_xboole_0('#skF_1', k2_tarski(B_388, C_389)), k2_tarski(B_388, C_389))=k3_xboole_0('#skF_1', k2_tarski(B_388, C_389)))), inference(superposition, [status(thm), theory('equality')], [c_11649, c_18])).
% 9.26/3.17  tff(c_11672, plain, (![B_388, C_389]: (k3_xboole_0('#skF_1', k2_tarski(B_388, C_389))='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_10576, c_11655])).
% 9.26/3.17  tff(c_11067, plain, (![A_357]: (k5_xboole_0(A_357, A_357)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_10969, c_16])).
% 9.26/3.17  tff(c_11095, plain, (![A_357]: (k5_xboole_0('#skF_1', k2_xboole_0(A_357, A_357))=k3_xboole_0(A_357, A_357))), inference(superposition, [status(thm), theory('equality')], [c_11067, c_18])).
% 9.26/3.17  tff(c_11137, plain, (![A_361]: (k5_xboole_0('#skF_1', A_361)=A_361)), inference(demodulation, [status(thm), theory('equality')], [c_2, c_198, c_11095])).
% 9.26/3.17  tff(c_11184, plain, (![B_4]: (k4_xboole_0('#skF_1', B_4)=k3_xboole_0('#skF_1', B_4))), inference(superposition, [status(thm), theory('equality')], [c_11137, c_4])).
% 9.26/3.17  tff(c_10119, plain, (k4_xboole_0('#skF_1', k2_tarski('#skF_2', '#skF_3'))!=k1_xboole_0), inference(splitRight, [status(thm)], [c_46])).
% 9.26/3.17  tff(c_10976, plain, (k4_xboole_0('#skF_1', k2_tarski('#skF_2', '#skF_3'))!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_10969, c_10119])).
% 9.26/3.17  tff(c_11496, plain, (k3_xboole_0('#skF_1', k2_tarski('#skF_2', '#skF_3'))!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_11184, c_10976])).
% 9.26/3.17  tff(c_11680, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_11672, c_11496])).
% 9.26/3.17  tff(c_11681, plain, (k1_tarski('#skF_2')='#skF_1' | k1_tarski('#skF_3')='#skF_1' | k2_tarski('#skF_2', '#skF_3')='#skF_1'), inference(splitRight, [status(thm)], [c_10968])).
% 9.26/3.17  tff(c_11866, plain, (k2_tarski('#skF_2', '#skF_3')='#skF_1'), inference(splitLeft, [status(thm)], [c_11681])).
% 9.26/3.17  tff(c_11867, plain, (k4_xboole_0('#skF_1', '#skF_1')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_11866, c_10119])).
% 9.26/3.17  tff(c_11870, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_233, c_11867])).
% 9.26/3.17  tff(c_11871, plain, (k1_tarski('#skF_3')='#skF_1' | k1_tarski('#skF_2')='#skF_1'), inference(splitRight, [status(thm)], [c_11681])).
% 9.26/3.17  tff(c_11873, plain, (k1_tarski('#skF_2')='#skF_1'), inference(splitLeft, [status(thm)], [c_11871])).
% 9.26/3.17  tff(c_12008, plain, (![C_401]: (r1_tarski('#skF_1', k2_tarski('#skF_2', C_401)))), inference(superposition, [status(thm), theory('equality')], [c_11873, c_42])).
% 9.26/3.17  tff(c_12320, plain, (![C_419]: (k2_xboole_0('#skF_1', k2_tarski('#skF_2', C_419))=k2_tarski('#skF_2', C_419))), inference(resolution, [status(thm)], [c_12008, c_65])).
% 9.26/3.17  tff(c_12326, plain, (![C_419]: (k5_xboole_0(k5_xboole_0('#skF_1', k2_tarski('#skF_2', C_419)), k2_tarski('#skF_2', C_419))=k3_xboole_0('#skF_1', k2_tarski('#skF_2', C_419)))), inference(superposition, [status(thm), theory('equality')], [c_12320, c_18])).
% 9.26/3.17  tff(c_12346, plain, (![C_420]: (k3_xboole_0('#skF_1', k2_tarski('#skF_2', C_420))='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_10576, c_12326])).
% 9.26/3.17  tff(c_12351, plain, (![C_420]: (k4_xboole_0('#skF_1', k2_tarski('#skF_2', C_420))=k5_xboole_0('#skF_1', '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_12346, c_4])).
% 9.26/3.17  tff(c_12359, plain, (![C_420]: (k4_xboole_0('#skF_1', k2_tarski('#skF_2', C_420))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_12351])).
% 9.26/3.17  tff(c_12364, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12359, c_10119])).
% 9.26/3.17  tff(c_12365, plain, (k1_tarski('#skF_3')='#skF_1'), inference(splitRight, [status(thm)], [c_11871])).
% 9.26/3.17  tff(c_12511, plain, (![B_428]: (r1_tarski('#skF_1', k2_tarski(B_428, '#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_12365, c_40])).
% 9.26/3.17  tff(c_12799, plain, (![B_446]: (k2_xboole_0('#skF_1', k2_tarski(B_446, '#skF_3'))=k2_tarski(B_446, '#skF_3'))), inference(resolution, [status(thm)], [c_12511, c_65])).
% 9.26/3.17  tff(c_12805, plain, (![B_446]: (k5_xboole_0(k5_xboole_0('#skF_1', k2_tarski(B_446, '#skF_3')), k2_tarski(B_446, '#skF_3'))=k3_xboole_0('#skF_1', k2_tarski(B_446, '#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_12799, c_18])).
% 9.26/3.17  tff(c_12825, plain, (![B_447]: (k3_xboole_0('#skF_1', k2_tarski(B_447, '#skF_3'))='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_10576, c_12805])).
% 9.26/3.17  tff(c_12830, plain, (![B_447]: (k4_xboole_0('#skF_1', k2_tarski(B_447, '#skF_3'))=k5_xboole_0('#skF_1', '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_12825, c_4])).
% 9.26/3.17  tff(c_12838, plain, (![B_447]: (k4_xboole_0('#skF_1', k2_tarski(B_447, '#skF_3'))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_12830])).
% 9.26/3.17  tff(c_12843, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12838, c_10119])).
% 9.26/3.17  tff(c_12845, plain, (k1_tarski('#skF_5')='#skF_4'), inference(splitRight, [status(thm)], [c_54])).
% 9.26/3.17  tff(c_56, plain, (k2_tarski('#skF_2', '#skF_3')='#skF_1' | k1_tarski('#skF_3')='#skF_1' | k1_tarski('#skF_2')='#skF_1' | k1_xboole_0='#skF_1' | k1_tarski('#skF_5')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_92])).
% 9.26/3.17  tff(c_13552, plain, (k2_tarski('#skF_2', '#skF_3')='#skF_1' | k1_tarski('#skF_3')='#skF_1' | k1_tarski('#skF_2')='#skF_1' | k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_12845, c_56])).
% 9.26/3.17  tff(c_13553, plain, (k1_xboole_0='#skF_1'), inference(splitLeft, [status(thm)], [c_13552])).
% 9.26/3.17  tff(c_13570, plain, (![A_15]: (k5_xboole_0(A_15, A_15)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_13553, c_16])).
% 9.26/3.17  tff(c_13610, plain, (![A_477]: (k5_xboole_0(A_477, A_477)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_13553, c_16])).
% 9.26/3.17  tff(c_13632, plain, (![A_477]: (k5_xboole_0('#skF_1', k2_xboole_0(A_477, A_477))=k3_xboole_0(A_477, A_477))), inference(superposition, [status(thm), theory('equality')], [c_13610, c_18])).
% 9.26/3.17  tff(c_13649, plain, (![A_477]: (k5_xboole_0('#skF_1', A_477)=A_477)), inference(demodulation, [status(thm), theory('equality')], [c_2, c_198, c_13632])).
% 9.26/3.17  tff(c_14458, plain, (![B_513, C_514]: (k2_xboole_0('#skF_1', k2_tarski(B_513, C_514))=k2_tarski(B_513, C_514))), inference(demodulation, [status(thm), theory('equality')], [c_13553, c_159])).
% 9.26/3.17  tff(c_14464, plain, (![B_513, C_514]: (k5_xboole_0(k5_xboole_0('#skF_1', k2_tarski(B_513, C_514)), k2_tarski(B_513, C_514))=k3_xboole_0('#skF_1', k2_tarski(B_513, C_514)))), inference(superposition, [status(thm), theory('equality')], [c_14458, c_18])).
% 9.26/3.17  tff(c_14478, plain, (![B_513, C_514]: (k3_xboole_0('#skF_1', k2_tarski(B_513, C_514))='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_13570, c_13649, c_14464])).
% 9.26/3.17  tff(c_13671, plain, (![A_481]: (k5_xboole_0('#skF_1', A_481)=A_481)), inference(demodulation, [status(thm), theory('equality')], [c_2, c_198, c_13632])).
% 9.26/3.17  tff(c_13729, plain, (![B_4]: (k4_xboole_0('#skF_1', B_4)=k3_xboole_0('#skF_1', B_4))), inference(superposition, [status(thm), theory('equality')], [c_4, c_13671])).
% 9.26/3.17  tff(c_12844, plain, (k4_xboole_0('#skF_1', k2_tarski('#skF_2', '#skF_3'))!=k1_xboole_0), inference(splitRight, [status(thm)], [c_54])).
% 9.26/3.17  tff(c_13559, plain, (k4_xboole_0('#skF_1', k2_tarski('#skF_2', '#skF_3'))!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_13553, c_12844])).
% 9.26/3.17  tff(c_13878, plain, (k3_xboole_0('#skF_1', k2_tarski('#skF_2', '#skF_3'))!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_13729, c_13559])).
% 9.26/3.17  tff(c_14494, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_14478, c_13878])).
% 9.26/3.17  tff(c_14495, plain, (k1_tarski('#skF_2')='#skF_1' | k1_tarski('#skF_3')='#skF_1' | k2_tarski('#skF_2', '#skF_3')='#skF_1'), inference(splitRight, [status(thm)], [c_13552])).
% 9.26/3.17  tff(c_14846, plain, (k2_tarski('#skF_2', '#skF_3')='#skF_1'), inference(splitLeft, [status(thm)], [c_14495])).
% 9.26/3.17  tff(c_14847, plain, (k4_xboole_0('#skF_1', '#skF_1')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_14846, c_12844])).
% 9.26/3.17  tff(c_14850, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_233, c_14847])).
% 9.26/3.17  tff(c_14851, plain, (k1_tarski('#skF_3')='#skF_1' | k1_tarski('#skF_2')='#skF_1'), inference(splitRight, [status(thm)], [c_14495])).
% 9.26/3.17  tff(c_14853, plain, (k1_tarski('#skF_2')='#skF_1'), inference(splitLeft, [status(thm)], [c_14851])).
% 9.26/3.17  tff(c_14936, plain, (![C_534]: (r1_tarski('#skF_1', k2_tarski('#skF_2', C_534)))), inference(superposition, [status(thm), theory('equality')], [c_14853, c_42])).
% 9.26/3.17  tff(c_15369, plain, (![C_559]: (k2_xboole_0('#skF_1', k2_tarski('#skF_2', C_559))=k2_tarski('#skF_2', C_559))), inference(resolution, [status(thm)], [c_14936, c_65])).
% 9.26/3.17  tff(c_15375, plain, (![C_559]: (k5_xboole_0(k5_xboole_0('#skF_1', k2_tarski('#skF_2', C_559)), k2_tarski('#skF_2', C_559))=k3_xboole_0('#skF_1', k2_tarski('#skF_2', C_559)))), inference(superposition, [status(thm), theory('equality')], [c_15369, c_18])).
% 9.26/3.17  tff(c_15396, plain, (![C_560]: (k3_xboole_0('#skF_1', k2_tarski('#skF_2', C_560))='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_13510, c_15375])).
% 9.26/3.17  tff(c_15401, plain, (![C_560]: (k4_xboole_0('#skF_1', k2_tarski('#skF_2', C_560))=k5_xboole_0('#skF_1', '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_15396, c_4])).
% 9.26/3.17  tff(c_15409, plain, (![C_560]: (k4_xboole_0('#skF_1', k2_tarski('#skF_2', C_560))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_15401])).
% 9.26/3.17  tff(c_15414, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_15409, c_12844])).
% 9.26/3.17  tff(c_15415, plain, (k1_tarski('#skF_3')='#skF_1'), inference(splitRight, [status(thm)], [c_14851])).
% 9.26/3.17  tff(c_15490, plain, (![B_566]: (r1_tarski('#skF_1', k2_tarski(B_566, '#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_15415, c_40])).
% 9.26/3.17  tff(c_16037, plain, (![B_591]: (k2_xboole_0('#skF_1', k2_tarski(B_591, '#skF_3'))=k2_tarski(B_591, '#skF_3'))), inference(resolution, [status(thm)], [c_15490, c_65])).
% 9.26/3.17  tff(c_16047, plain, (![B_591]: (k5_xboole_0(k5_xboole_0('#skF_1', k2_tarski(B_591, '#skF_3')), k2_tarski(B_591, '#skF_3'))=k3_xboole_0('#skF_1', k2_tarski(B_591, '#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_16037, c_18])).
% 9.26/3.17  tff(c_16082, plain, (![B_599]: (k3_xboole_0('#skF_1', k2_tarski(B_599, '#skF_3'))='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_13510, c_16047])).
% 9.26/3.17  tff(c_16090, plain, (![B_599]: (k4_xboole_0('#skF_1', k2_tarski(B_599, '#skF_3'))=k5_xboole_0('#skF_1', '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_16082, c_4])).
% 9.26/3.17  tff(c_16102, plain, (![B_599]: (k4_xboole_0('#skF_1', k2_tarski(B_599, '#skF_3'))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_16090])).
% 9.26/3.17  tff(c_16108, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_16102, c_12844])).
% 9.26/3.17  tff(c_16110, plain, (k1_tarski('#skF_6')='#skF_4'), inference(splitRight, [status(thm)], [c_50])).
% 9.26/3.17  tff(c_52, plain, (k2_tarski('#skF_2', '#skF_3')='#skF_1' | k1_tarski('#skF_3')='#skF_1' | k1_tarski('#skF_2')='#skF_1' | k1_xboole_0='#skF_1' | k1_tarski('#skF_6')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_92])).
% 9.26/3.17  tff(c_17029, plain, (k2_tarski('#skF_2', '#skF_3')='#skF_1' | k1_tarski('#skF_3')='#skF_1' | k1_tarski('#skF_2')='#skF_1' | k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_16110, c_52])).
% 9.26/3.17  tff(c_17030, plain, (k1_xboole_0='#skF_1'), inference(splitLeft, [status(thm)], [c_17029])).
% 9.26/3.17  tff(c_16685, plain, (![A_625, B_626]: (k5_xboole_0(k5_xboole_0(A_625, B_626), k2_xboole_0(A_625, B_626))=k3_xboole_0(A_625, B_626))), inference(cnfTransformation, [status(thm)], [f_45])).
% 9.26/3.17  tff(c_16724, plain, (![B_47, C_48]: (k5_xboole_0(k5_xboole_0(k1_xboole_0, k2_tarski(B_47, C_48)), k2_tarski(B_47, C_48))=k3_xboole_0(k1_xboole_0, k2_tarski(B_47, C_48)))), inference(superposition, [status(thm), theory('equality')], [c_159, c_16685])).
% 9.26/3.17  tff(c_16759, plain, (![B_47, C_48]: (k3_xboole_0(k1_xboole_0, k2_tarski(B_47, C_48))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_16538, c_16724])).
% 9.26/3.17  tff(c_17033, plain, (![B_47, C_48]: (k3_xboole_0('#skF_1', k2_tarski(B_47, C_48))='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_17030, c_17030, c_16759])).
% 9.26/3.17  tff(c_17092, plain, (![A_643]: (k5_xboole_0(A_643, A_643)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_17030, c_16])).
% 9.26/3.17  tff(c_17104, plain, (![A_643]: (k5_xboole_0('#skF_1', k2_xboole_0(A_643, A_643))=k3_xboole_0(A_643, A_643))), inference(superposition, [status(thm), theory('equality')], [c_17092, c_18])).
% 9.26/3.17  tff(c_17153, plain, (![A_647]: (k5_xboole_0('#skF_1', A_647)=A_647)), inference(demodulation, [status(thm), theory('equality')], [c_2, c_198, c_17104])).
% 9.26/3.17  tff(c_17211, plain, (![B_4]: (k4_xboole_0('#skF_1', B_4)=k3_xboole_0('#skF_1', B_4))), inference(superposition, [status(thm), theory('equality')], [c_4, c_17153])).
% 9.26/3.17  tff(c_16109, plain, (k4_xboole_0('#skF_1', k2_tarski('#skF_2', '#skF_3'))!=k1_xboole_0), inference(splitRight, [status(thm)], [c_50])).
% 9.26/3.17  tff(c_17044, plain, (k4_xboole_0('#skF_1', k2_tarski('#skF_2', '#skF_3'))!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_17030, c_16109])).
% 9.26/3.17  tff(c_17440, plain, (k3_xboole_0('#skF_1', k2_tarski('#skF_2', '#skF_3'))!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_17211, c_17044])).
% 9.26/3.17  tff(c_17443, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_17033, c_17440])).
% 9.26/3.17  tff(c_17444, plain, (k1_tarski('#skF_2')='#skF_1' | k1_tarski('#skF_3')='#skF_1' | k2_tarski('#skF_2', '#skF_3')='#skF_1'), inference(splitRight, [status(thm)], [c_17029])).
% 9.26/3.17  tff(c_17837, plain, (k2_tarski('#skF_2', '#skF_3')='#skF_1'), inference(splitLeft, [status(thm)], [c_17444])).
% 9.26/3.17  tff(c_17838, plain, (k4_xboole_0('#skF_1', '#skF_1')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_17837, c_16109])).
% 9.26/3.17  tff(c_17841, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_16181, c_17838])).
% 9.26/3.17  tff(c_17842, plain, (k1_tarski('#skF_3')='#skF_1' | k1_tarski('#skF_2')='#skF_1'), inference(splitRight, [status(thm)], [c_17444])).
% 9.26/3.17  tff(c_17844, plain, (k1_tarski('#skF_2')='#skF_1'), inference(splitLeft, [status(thm)], [c_17842])).
% 9.26/3.17  tff(c_17935, plain, (![C_680]: (r1_tarski('#skF_1', k2_tarski('#skF_2', C_680)))), inference(superposition, [status(thm), theory('equality')], [c_17844, c_42])).
% 9.26/3.17  tff(c_18219, plain, (![C_700]: (k2_xboole_0('#skF_1', k2_tarski('#skF_2', C_700))=k2_tarski('#skF_2', C_700))), inference(resolution, [status(thm)], [c_17935, c_65])).
% 9.26/3.17  tff(c_18229, plain, (![C_700]: (k5_xboole_0(k5_xboole_0('#skF_1', k2_tarski('#skF_2', C_700)), k2_tarski('#skF_2', C_700))=k3_xboole_0('#skF_1', k2_tarski('#skF_2', C_700)))), inference(superposition, [status(thm), theory('equality')], [c_18219, c_18])).
% 9.26/3.17  tff(c_18255, plain, (![C_701]: (k3_xboole_0('#skF_1', k2_tarski('#skF_2', C_701))='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_16919, c_18229])).
% 9.26/3.17  tff(c_18263, plain, (![C_701]: (k4_xboole_0('#skF_1', k2_tarski('#skF_2', C_701))=k5_xboole_0('#skF_1', '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_18255, c_4])).
% 9.26/3.17  tff(c_18275, plain, (![C_701]: (k4_xboole_0('#skF_1', k2_tarski('#skF_2', C_701))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_18263])).
% 9.26/3.17  tff(c_18281, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_18275, c_16109])).
% 9.26/3.17  tff(c_18282, plain, (k1_tarski('#skF_3')='#skF_1'), inference(splitRight, [status(thm)], [c_17842])).
% 9.26/3.17  tff(c_18382, plain, (![B_708]: (r1_tarski('#skF_1', k2_tarski(B_708, '#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_18282, c_40])).
% 9.26/3.17  tff(c_18617, plain, (![B_731]: (k2_xboole_0('#skF_1', k2_tarski(B_731, '#skF_3'))=k2_tarski(B_731, '#skF_3'))), inference(resolution, [status(thm)], [c_18382, c_65])).
% 9.26/3.17  tff(c_18627, plain, (![B_731]: (k5_xboole_0(k5_xboole_0('#skF_1', k2_tarski(B_731, '#skF_3')), k2_tarski(B_731, '#skF_3'))=k3_xboole_0('#skF_1', k2_tarski(B_731, '#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_18617, c_18])).
% 9.26/3.17  tff(c_18653, plain, (![B_732]: (k3_xboole_0('#skF_1', k2_tarski(B_732, '#skF_3'))='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_16919, c_18627])).
% 9.26/3.17  tff(c_18661, plain, (![B_732]: (k4_xboole_0('#skF_1', k2_tarski(B_732, '#skF_3'))=k5_xboole_0('#skF_1', '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_18653, c_4])).
% 9.26/3.17  tff(c_18673, plain, (![B_732]: (k4_xboole_0('#skF_1', k2_tarski(B_732, '#skF_3'))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_18661])).
% 9.26/3.17  tff(c_18679, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_18673, c_16109])).
% 9.26/3.17  tff(c_18681, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_58])).
% 9.26/3.17  tff(c_18685, plain, (![A_15]: (k5_xboole_0(A_15, A_15)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_18681, c_16])).
% 9.26/3.17  tff(c_18684, plain, (![A_9]: (k5_xboole_0(A_9, '#skF_4')=A_9)), inference(demodulation, [status(thm), theory('equality')], [c_18681, c_10])).
% 9.26/3.17  tff(c_18942, plain, (![A_762, B_763, C_764]: (k5_xboole_0(k5_xboole_0(A_762, B_763), C_764)=k5_xboole_0(A_762, k5_xboole_0(B_763, C_764)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 9.26/3.17  tff(c_19269, plain, (![A_771, C_772]: (k5_xboole_0(A_771, k5_xboole_0(A_771, C_772))=k5_xboole_0('#skF_4', C_772))), inference(superposition, [status(thm), theory('equality')], [c_18685, c_18942])).
% 9.26/3.17  tff(c_19356, plain, (![A_15]: (k5_xboole_0(A_15, '#skF_4')=k5_xboole_0('#skF_4', A_15))), inference(superposition, [status(thm), theory('equality')], [c_18685, c_19269])).
% 9.26/3.17  tff(c_19382, plain, (![A_15]: (k5_xboole_0('#skF_4', A_15)=A_15)), inference(demodulation, [status(thm), theory('equality')], [c_18684, c_19356])).
% 9.26/3.17  tff(c_18976, plain, (![A_15, C_764]: (k5_xboole_0(A_15, k5_xboole_0(A_15, C_764))=k5_xboole_0('#skF_4', C_764))), inference(superposition, [status(thm), theory('equality')], [c_18685, c_18942])).
% 9.26/3.17  tff(c_19384, plain, (![A_15, C_764]: (k5_xboole_0(A_15, k5_xboole_0(A_15, C_764))=C_764)), inference(demodulation, [status(thm), theory('equality')], [c_19382, c_18976])).
% 9.26/3.17  tff(c_18956, plain, (![A_762, B_763]: (k5_xboole_0(A_762, k5_xboole_0(B_763, k5_xboole_0(A_762, B_763)))='#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_18942, c_18685])).
% 9.26/3.17  tff(c_19589, plain, (![A_780, C_781]: (k5_xboole_0(A_780, k5_xboole_0(A_780, C_781))=C_781)), inference(demodulation, [status(thm), theory('equality')], [c_19382, c_18976])).
% 9.26/3.17  tff(c_19639, plain, (![B_763, A_762]: (k5_xboole_0(B_763, k5_xboole_0(A_762, B_763))=k5_xboole_0(A_762, '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_18956, c_19589])).
% 9.26/3.17  tff(c_19766, plain, (![B_791, A_792]: (k5_xboole_0(B_791, k5_xboole_0(A_792, B_791))=A_792)), inference(demodulation, [status(thm), theory('equality')], [c_18684, c_19639])).
% 9.26/3.17  tff(c_19802, plain, (![A_15, C_764]: (k5_xboole_0(k5_xboole_0(A_15, C_764), C_764)=A_15)), inference(superposition, [status(thm), theory('equality')], [c_19384, c_19766])).
% 9.26/3.17  tff(c_18823, plain, (![A_752, B_753]: (k5_xboole_0(A_752, k3_xboole_0(A_752, B_753))=k4_xboole_0(A_752, B_753))), inference(cnfTransformation, [status(thm)], [f_29])).
% 9.26/3.17  tff(c_18832, plain, (![A_1]: (k5_xboole_0(A_1, A_1)=k4_xboole_0(A_1, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_18823])).
% 9.26/3.17  tff(c_18835, plain, (![A_1]: (k4_xboole_0(A_1, A_1)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_18685, c_18832])).
% 9.26/3.17  tff(c_18683, plain, (![B_47, C_48]: (r1_tarski('#skF_4', k2_tarski(B_47, C_48)))), inference(demodulation, [status(thm), theory('equality')], [c_18681, c_44])).
% 9.26/3.17  tff(c_18738, plain, (![A_743, B_744]: (k2_xboole_0(A_743, B_744)=B_744 | ~r1_tarski(A_743, B_744))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_8])).
% 9.26/3.17  tff(c_18763, plain, (![B_47, C_48]: (k2_xboole_0('#skF_4', k2_tarski(B_47, C_48))=k2_tarski(B_47, C_48))), inference(resolution, [status(thm)], [c_18683, c_18738])).
% 9.26/3.17  tff(c_19450, plain, (![A_774, B_775]: (k5_xboole_0(k5_xboole_0(A_774, B_775), k2_xboole_0(A_774, B_775))=k3_xboole_0(A_774, B_775))), inference(cnfTransformation, [status(thm)], [f_45])).
% 9.26/3.17  tff(c_19487, plain, (![B_47, C_48]: (k5_xboole_0(k5_xboole_0('#skF_4', k2_tarski(B_47, C_48)), k2_tarski(B_47, C_48))=k3_xboole_0('#skF_4', k2_tarski(B_47, C_48)))), inference(superposition, [status(thm), theory('equality')], [c_18763, c_19450])).
% 9.26/3.17  tff(c_19515, plain, (![B_47, C_48]: (k3_xboole_0('#skF_4', k2_tarski(B_47, C_48))='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_18685, c_19382, c_19487])).
% 9.26/3.17  tff(c_19390, plain, (![A_773]: (k5_xboole_0('#skF_4', A_773)=A_773)), inference(demodulation, [status(thm), theory('equality')], [c_18684, c_19356])).
% 9.26/3.17  tff(c_19430, plain, (![B_4]: (k4_xboole_0('#skF_4', B_4)=k3_xboole_0('#skF_4', B_4))), inference(superposition, [status(thm), theory('equality')], [c_4, c_19390])).
% 9.26/3.17  tff(c_60, plain, (k2_tarski('#skF_2', '#skF_3')='#skF_1' | k1_tarski('#skF_3')='#skF_1' | k1_tarski('#skF_2')='#skF_1' | k1_xboole_0='#skF_1' | k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_92])).
% 9.26/3.17  tff(c_19844, plain, (k2_tarski('#skF_2', '#skF_3')='#skF_1' | k1_tarski('#skF_3')='#skF_1' | k1_tarski('#skF_2')='#skF_1' | '#skF_1'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_18681, c_18681, c_60])).
% 9.26/3.17  tff(c_19845, plain, ('#skF_1'='#skF_4'), inference(splitLeft, [status(thm)], [c_19844])).
% 9.26/3.17  tff(c_18680, plain, (k4_xboole_0('#skF_1', k2_tarski('#skF_2', '#skF_3'))!=k1_xboole_0), inference(splitRight, [status(thm)], [c_58])).
% 9.26/3.17  tff(c_18727, plain, (k4_xboole_0('#skF_1', k2_tarski('#skF_2', '#skF_3'))!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_18681, c_18680])).
% 9.26/3.17  tff(c_19846, plain, (k4_xboole_0('#skF_4', k2_tarski('#skF_2', '#skF_3'))!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_19845, c_18727])).
% 9.26/3.17  tff(c_19849, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_19515, c_19430, c_19846])).
% 9.26/3.17  tff(c_19850, plain, (k1_tarski('#skF_2')='#skF_1' | k1_tarski('#skF_3')='#skF_1' | k2_tarski('#skF_2', '#skF_3')='#skF_1'), inference(splitRight, [status(thm)], [c_19844])).
% 9.26/3.17  tff(c_19969, plain, (k2_tarski('#skF_2', '#skF_3')='#skF_1'), inference(splitLeft, [status(thm)], [c_19850])).
% 9.26/3.17  tff(c_19970, plain, (k4_xboole_0('#skF_1', '#skF_1')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_19969, c_18727])).
% 9.26/3.17  tff(c_19973, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_18835, c_19970])).
% 9.26/3.17  tff(c_19974, plain, (k1_tarski('#skF_3')='#skF_1' | k1_tarski('#skF_2')='#skF_1'), inference(splitRight, [status(thm)], [c_19850])).
% 9.26/3.17  tff(c_19976, plain, (k1_tarski('#skF_2')='#skF_1'), inference(splitLeft, [status(thm)], [c_19974])).
% 9.26/3.17  tff(c_20068, plain, (![C_801]: (r1_tarski('#skF_1', k2_tarski('#skF_2', C_801)))), inference(superposition, [status(thm), theory('equality')], [c_19976, c_42])).
% 9.26/3.17  tff(c_20383, plain, (![C_820]: (k2_xboole_0('#skF_1', k2_tarski('#skF_2', C_820))=k2_tarski('#skF_2', C_820))), inference(resolution, [status(thm)], [c_20068, c_65])).
% 9.26/3.17  tff(c_20389, plain, (![C_820]: (k5_xboole_0(k5_xboole_0('#skF_1', k2_tarski('#skF_2', C_820)), k2_tarski('#skF_2', C_820))=k3_xboole_0('#skF_1', k2_tarski('#skF_2', C_820)))), inference(superposition, [status(thm), theory('equality')], [c_20383, c_18])).
% 9.26/3.17  tff(c_20409, plain, (![C_821]: (k3_xboole_0('#skF_1', k2_tarski('#skF_2', C_821))='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_19802, c_20389])).
% 9.26/3.17  tff(c_20414, plain, (![C_821]: (k4_xboole_0('#skF_1', k2_tarski('#skF_2', C_821))=k5_xboole_0('#skF_1', '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_20409, c_4])).
% 9.26/3.17  tff(c_20422, plain, (![C_821]: (k4_xboole_0('#skF_1', k2_tarski('#skF_2', C_821))='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_18685, c_20414])).
% 9.26/3.17  tff(c_20427, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_20422, c_18727])).
% 9.26/3.17  tff(c_20428, plain, (k1_tarski('#skF_3')='#skF_1'), inference(splitRight, [status(thm)], [c_19974])).
% 9.26/3.17  tff(c_20531, plain, (![B_828]: (r1_tarski('#skF_1', k2_tarski(B_828, '#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_20428, c_40])).
% 9.26/3.17  tff(c_20896, plain, (![B_849]: (k2_xboole_0('#skF_1', k2_tarski(B_849, '#skF_3'))=k2_tarski(B_849, '#skF_3'))), inference(resolution, [status(thm)], [c_20531, c_65])).
% 9.26/3.17  tff(c_20906, plain, (![B_849]: (k5_xboole_0(k5_xboole_0('#skF_1', k2_tarski(B_849, '#skF_3')), k2_tarski(B_849, '#skF_3'))=k3_xboole_0('#skF_1', k2_tarski(B_849, '#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_20896, c_18])).
% 9.26/3.17  tff(c_20932, plain, (![B_850]: (k3_xboole_0('#skF_1', k2_tarski(B_850, '#skF_3'))='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_19802, c_20906])).
% 9.26/3.17  tff(c_20940, plain, (![B_850]: (k4_xboole_0('#skF_1', k2_tarski(B_850, '#skF_3'))=k5_xboole_0('#skF_1', '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_20932, c_4])).
% 9.26/3.17  tff(c_20952, plain, (![B_850]: (k4_xboole_0('#skF_1', k2_tarski(B_850, '#skF_3'))='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_18685, c_20940])).
% 9.26/3.17  tff(c_20958, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_20952, c_18727])).
% 9.26/3.17  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.26/3.17  
% 9.26/3.17  Inference rules
% 9.26/3.17  ----------------------
% 9.26/3.17  #Ref     : 0
% 9.26/3.17  #Sup     : 5157
% 9.26/3.17  #Fact    : 0
% 9.26/3.17  #Define  : 0
% 9.26/3.17  #Split   : 26
% 9.26/3.17  #Chain   : 0
% 9.26/3.17  #Close   : 0
% 9.26/3.17  
% 9.26/3.17  Ordering : KBO
% 9.26/3.17  
% 9.26/3.17  Simplification rules
% 9.26/3.17  ----------------------
% 9.26/3.17  #Subsume      : 55
% 9.26/3.17  #Demod        : 4792
% 9.26/3.17  #Tautology    : 3865
% 9.26/3.17  #SimpNegUnit  : 45
% 9.26/3.17  #BackRed      : 129
% 9.26/3.17  
% 9.26/3.17  #Partial instantiations: 0
% 9.26/3.17  #Strategies tried      : 1
% 9.26/3.17  
% 9.26/3.17  Timing (in seconds)
% 9.26/3.17  ----------------------
% 9.26/3.17  Preprocessing        : 0.32
% 9.26/3.17  Parsing              : 0.16
% 9.26/3.17  CNF conversion       : 0.02
% 9.26/3.17  Main loop            : 2.04
% 9.26/3.17  Inferencing          : 0.61
% 9.26/3.17  Reduction            : 0.94
% 9.26/3.18  Demodulation         : 0.76
% 9.26/3.18  BG Simplification    : 0.07
% 9.26/3.18  Subsumption          : 0.28
% 9.26/3.18  Abstraction          : 0.11
% 9.26/3.18  MUC search           : 0.00
% 9.26/3.18  Cooper               : 0.00
% 9.26/3.18  Total                : 2.45
% 9.26/3.18  Index Insertion      : 0.00
% 9.26/3.18  Index Deletion       : 0.00
% 9.26/3.18  Index Matching       : 0.00
% 9.26/3.18  BG Taut test         : 0.00
%------------------------------------------------------------------------------

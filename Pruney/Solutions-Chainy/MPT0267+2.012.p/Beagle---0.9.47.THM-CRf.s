%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:52:33 EST 2020

% Result     : Theorem 7.38s
% Output     : CNFRefutation 7.70s
% Verified   : 
% Statistics : Number of formulae       :  137 ( 287 expanded)
%              Number of leaves         :   34 ( 103 expanded)
%              Depth                    :   13
%              Number of atoms          :  193 ( 543 expanded)
%              Number of equality atoms :   33 ( 153 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_9 > #skF_8 > #skF_4 > #skF_2 > #skF_1

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

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_67,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(f_89,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r2_hidden(A,k4_xboole_0(B,k1_tarski(C)))
      <=> ( r2_hidden(A,B)
          & A != C ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_58,axiom,(
    ! [A,B,C] : k3_xboole_0(k3_xboole_0(A,B),C) = k3_xboole_0(A,k3_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_xboole_1)).

tff(f_56,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_54,axiom,(
    ! [A,B] : r1_xboole_0(k3_xboole_0(A,B),k5_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l97_xboole_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k5_xboole_0(B,C))
    <=> ~ ( r2_hidden(A,B)
        <=> r2_hidden(A,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_0)).

tff(f_60,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

tff(c_32,plain,(
    ! [C_24] : r2_hidden(C_24,k1_tarski(C_24)) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_64,plain,
    ( '#skF_6' != '#skF_4'
    | r2_hidden('#skF_7',k4_xboole_0('#skF_8',k1_tarski('#skF_9'))) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_120,plain,(
    '#skF_6' != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_64])).

tff(c_66,plain,
    ( r2_hidden('#skF_4','#skF_5')
    | r2_hidden('#skF_7',k4_xboole_0('#skF_8',k1_tarski('#skF_9'))) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_152,plain,(
    r2_hidden('#skF_7',k4_xboole_0('#skF_8',k1_tarski('#skF_9'))) ),
    inference(splitLeft,[status(thm)],[c_66])).

tff(c_2,plain,(
    ! [A_1] : k3_xboole_0(A_1,A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_187,plain,(
    ! [A_82,B_83,C_84] : k3_xboole_0(k3_xboole_0(A_82,B_83),C_84) = k3_xboole_0(A_82,k3_xboole_0(B_83,C_84)) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_212,plain,(
    ! [A_1,C_84] : k3_xboole_0(A_1,k3_xboole_0(A_1,C_84)) = k3_xboole_0(A_1,C_84) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_187])).

tff(c_24,plain,(
    ! [A_13,B_14] : k5_xboole_0(A_13,k3_xboole_0(A_13,B_14)) = k4_xboole_0(A_13,B_14) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_22,plain,(
    ! [A_11,B_12] : r1_xboole_0(k3_xboole_0(A_11,B_12),k5_xboole_0(A_11,B_12)) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_162,plain,(
    ! [A_76,B_77,C_78] :
      ( ~ r1_xboole_0(A_76,B_77)
      | ~ r2_hidden(C_78,B_77)
      | ~ r2_hidden(C_78,A_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_442,plain,(
    ! [C_104,A_105,B_106] :
      ( ~ r2_hidden(C_104,k5_xboole_0(A_105,B_106))
      | ~ r2_hidden(C_104,k3_xboole_0(A_105,B_106)) ) ),
    inference(resolution,[status(thm)],[c_22,c_162])).

tff(c_451,plain,(
    ! [C_104,A_13,B_14] :
      ( ~ r2_hidden(C_104,k4_xboole_0(A_13,B_14))
      | ~ r2_hidden(C_104,k3_xboole_0(A_13,k3_xboole_0(A_13,B_14))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_442])).

tff(c_467,plain,(
    ! [C_107,A_108,B_109] :
      ( ~ r2_hidden(C_107,k4_xboole_0(A_108,B_109))
      | ~ r2_hidden(C_107,k3_xboole_0(A_108,B_109)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_212,c_451])).

tff(c_483,plain,(
    ~ r2_hidden('#skF_7',k3_xboole_0('#skF_8',k1_tarski('#skF_9'))) ),
    inference(resolution,[status(thm)],[c_152,c_467])).

tff(c_58,plain,
    ( '#skF_6' != '#skF_4'
    | '#skF_7' = '#skF_9'
    | ~ r2_hidden('#skF_7','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_98,plain,(
    ~ r2_hidden('#skF_7','#skF_8') ),
    inference(splitLeft,[status(thm)],[c_58])).

tff(c_583,plain,(
    ! [A_114,B_115,C_116] :
      ( r2_hidden(A_114,B_115)
      | r2_hidden(A_114,C_116)
      | ~ r2_hidden(A_114,k5_xboole_0(B_115,C_116)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_2143,plain,(
    ! [A_253,A_254,B_255] :
      ( r2_hidden(A_253,A_254)
      | r2_hidden(A_253,k3_xboole_0(A_254,B_255))
      | ~ r2_hidden(A_253,k4_xboole_0(A_254,B_255)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_583])).

tff(c_2163,plain,
    ( r2_hidden('#skF_7','#skF_8')
    | r2_hidden('#skF_7',k3_xboole_0('#skF_8',k1_tarski('#skF_9'))) ),
    inference(resolution,[status(thm)],[c_152,c_2143])).

tff(c_2180,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_483,c_98,c_2163])).

tff(c_2181,plain,(
    r2_hidden('#skF_4','#skF_5') ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_2658,plain,(
    ! [A_309,C_310,B_311] :
      ( r2_hidden(A_309,C_310)
      | ~ r2_hidden(A_309,B_311)
      | r2_hidden(A_309,k5_xboole_0(B_311,C_310)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_4388,plain,(
    ! [A_445,A_446,B_447] :
      ( r2_hidden(A_445,k3_xboole_0(A_446,B_447))
      | ~ r2_hidden(A_445,A_446)
      | r2_hidden(A_445,k4_xboole_0(A_446,B_447)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_2658])).

tff(c_2182,plain,(
    ~ r2_hidden('#skF_7',k4_xboole_0('#skF_8',k1_tarski('#skF_9'))) ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_62,plain,
    ( ~ r2_hidden('#skF_4',k4_xboole_0('#skF_5',k1_tarski('#skF_6')))
    | r2_hidden('#skF_7',k4_xboole_0('#skF_8',k1_tarski('#skF_9'))) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_2357,plain,(
    ~ r2_hidden('#skF_4',k4_xboole_0('#skF_5',k1_tarski('#skF_6'))) ),
    inference(negUnitSimplification,[status(thm)],[c_2182,c_62])).

tff(c_4423,plain,
    ( r2_hidden('#skF_4',k3_xboole_0('#skF_5',k1_tarski('#skF_6')))
    | ~ r2_hidden('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_4388,c_2357])).

tff(c_4447,plain,(
    r2_hidden('#skF_4',k3_xboole_0('#skF_5',k1_tarski('#skF_6'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2181,c_4423])).

tff(c_14,plain,(
    ! [A_3,C_5,B_4] :
      ( r2_hidden(A_3,C_5)
      | ~ r2_hidden(A_3,B_4)
      | r2_hidden(A_3,k5_xboole_0(B_4,C_5)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_2232,plain,(
    ! [A_271,B_272,C_273] : k3_xboole_0(k3_xboole_0(A_271,B_272),C_273) = k3_xboole_0(A_271,k3_xboole_0(B_272,C_273)) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_2688,plain,(
    ! [A_314,B_315,C_316] : r1_xboole_0(k3_xboole_0(A_314,k3_xboole_0(B_315,C_316)),k5_xboole_0(k3_xboole_0(A_314,B_315),C_316)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2232,c_22])).

tff(c_2748,plain,(
    ! [A_317,A_318] : r1_xboole_0(k3_xboole_0(A_317,A_318),k5_xboole_0(k3_xboole_0(A_317,A_318),A_318)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_2688])).

tff(c_16,plain,(
    ! [A_6,B_7,C_10] :
      ( ~ r1_xboole_0(A_6,B_7)
      | ~ r2_hidden(C_10,B_7)
      | ~ r2_hidden(C_10,A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_3749,plain,(
    ! [C_404,A_405,A_406] :
      ( ~ r2_hidden(C_404,k5_xboole_0(k3_xboole_0(A_405,A_406),A_406))
      | ~ r2_hidden(C_404,k3_xboole_0(A_405,A_406)) ) ),
    inference(resolution,[status(thm)],[c_2748,c_16])).

tff(c_3788,plain,(
    ! [A_3,C_5,A_405] :
      ( r2_hidden(A_3,C_5)
      | ~ r2_hidden(A_3,k3_xboole_0(A_405,C_5)) ) ),
    inference(resolution,[status(thm)],[c_14,c_3749])).

tff(c_4462,plain,(
    r2_hidden('#skF_4',k1_tarski('#skF_6')) ),
    inference(resolution,[status(thm)],[c_4447,c_3788])).

tff(c_30,plain,(
    ! [C_24,A_20] :
      ( C_24 = A_20
      | ~ r2_hidden(C_24,k1_tarski(A_20)) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_4473,plain,(
    '#skF_6' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_4462,c_30])).

tff(c_4480,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_120,c_4473])).

tff(c_4481,plain,(
    r2_hidden('#skF_7',k4_xboole_0('#skF_8',k1_tarski('#skF_9'))) ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_4582,plain,(
    ! [A_469,B_470,C_471] : k3_xboole_0(k3_xboole_0(A_469,B_470),C_471) = k3_xboole_0(A_469,k3_xboole_0(B_470,C_471)) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_4614,plain,(
    ! [A_1,C_471] : k3_xboole_0(A_1,k3_xboole_0(A_1,C_471)) = k3_xboole_0(A_1,C_471) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_4582])).

tff(c_4489,plain,(
    ! [A_448,B_449] : k5_xboole_0(A_448,k3_xboole_0(A_448,B_449)) = k4_xboole_0(A_448,B_449) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_4495,plain,(
    ! [A_448,B_449] : r1_xboole_0(k3_xboole_0(A_448,k3_xboole_0(A_448,B_449)),k4_xboole_0(A_448,B_449)) ),
    inference(superposition,[status(thm),theory(equality)],[c_4489,c_22])).

tff(c_4673,plain,(
    ! [A_474,B_475] : r1_xboole_0(k3_xboole_0(A_474,B_475),k4_xboole_0(A_474,B_475)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4614,c_4495])).

tff(c_4859,plain,(
    ! [C_488,A_489,B_490] :
      ( ~ r2_hidden(C_488,k4_xboole_0(A_489,B_490))
      | ~ r2_hidden(C_488,k3_xboole_0(A_489,B_490)) ) ),
    inference(resolution,[status(thm)],[c_4673,c_16])).

tff(c_4875,plain,(
    ~ r2_hidden('#skF_7',k3_xboole_0('#skF_8',k1_tarski('#skF_9'))) ),
    inference(resolution,[status(thm)],[c_4481,c_4859])).

tff(c_4823,plain,(
    ! [A_482,B_483,C_484] :
      ( r2_hidden(A_482,B_483)
      | r2_hidden(A_482,C_484)
      | ~ r2_hidden(A_482,k5_xboole_0(B_483,C_484)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_6366,plain,(
    ! [A_623,A_624,B_625] :
      ( r2_hidden(A_623,A_624)
      | r2_hidden(A_623,k3_xboole_0(A_624,B_625))
      | ~ r2_hidden(A_623,k4_xboole_0(A_624,B_625)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_4823])).

tff(c_6386,plain,
    ( r2_hidden('#skF_7','#skF_8')
    | r2_hidden('#skF_7',k3_xboole_0('#skF_8',k1_tarski('#skF_9'))) ),
    inference(resolution,[status(thm)],[c_4481,c_6366])).

tff(c_6403,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4875,c_98,c_6386])).

tff(c_6404,plain,
    ( '#skF_6' != '#skF_4'
    | '#skF_7' = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_6406,plain,(
    '#skF_6' != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_6404])).

tff(c_6405,plain,(
    r2_hidden('#skF_7','#skF_8') ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_60,plain,
    ( r2_hidden('#skF_4','#skF_5')
    | '#skF_7' = '#skF_9'
    | ~ r2_hidden('#skF_7','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_6408,plain,
    ( r2_hidden('#skF_4','#skF_5')
    | '#skF_7' = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6405,c_60])).

tff(c_6409,plain,(
    '#skF_7' = '#skF_9' ),
    inference(splitLeft,[status(thm)],[c_6408])).

tff(c_6467,plain,
    ( r2_hidden('#skF_4','#skF_5')
    | r2_hidden('#skF_9',k4_xboole_0('#skF_8',k1_tarski('#skF_9'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6409,c_66])).

tff(c_6468,plain,(
    r2_hidden('#skF_9',k4_xboole_0('#skF_8',k1_tarski('#skF_9'))) ),
    inference(splitLeft,[status(thm)],[c_6467])).

tff(c_28,plain,(
    ! [A_18,B_19] : r1_xboole_0(k4_xboole_0(A_18,B_19),B_19) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_6479,plain,(
    ! [A_639,B_640,C_641] :
      ( ~ r1_xboole_0(A_639,B_640)
      | ~ r2_hidden(C_641,B_640)
      | ~ r2_hidden(C_641,A_639) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_6489,plain,(
    ! [C_642,B_643,A_644] :
      ( ~ r2_hidden(C_642,B_643)
      | ~ r2_hidden(C_642,k4_xboole_0(A_644,B_643)) ) ),
    inference(resolution,[status(thm)],[c_28,c_6479])).

tff(c_6492,plain,(
    ~ r2_hidden('#skF_9',k1_tarski('#skF_9')) ),
    inference(resolution,[status(thm)],[c_6468,c_6489])).

tff(c_6504,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_6492])).

tff(c_6505,plain,(
    r2_hidden('#skF_4','#skF_5') ),
    inference(splitRight,[status(thm)],[c_6467])).

tff(c_6955,plain,(
    ! [A_689,C_690,B_691] :
      ( r2_hidden(A_689,C_690)
      | ~ r2_hidden(A_689,B_691)
      | r2_hidden(A_689,k5_xboole_0(B_691,C_690)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_8044,plain,(
    ! [A_786,A_787,B_788] :
      ( r2_hidden(A_786,k3_xboole_0(A_787,B_788))
      | ~ r2_hidden(A_786,A_787)
      | r2_hidden(A_786,k4_xboole_0(A_787,B_788)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_6955])).

tff(c_6506,plain,(
    ~ r2_hidden('#skF_9',k4_xboole_0('#skF_8',k1_tarski('#skF_9'))) ),
    inference(splitRight,[status(thm)],[c_6467])).

tff(c_6684,plain,
    ( ~ r2_hidden('#skF_4',k4_xboole_0('#skF_5',k1_tarski('#skF_6')))
    | r2_hidden('#skF_9',k4_xboole_0('#skF_8',k1_tarski('#skF_9'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6409,c_62])).

tff(c_6685,plain,(
    ~ r2_hidden('#skF_4',k4_xboole_0('#skF_5',k1_tarski('#skF_6'))) ),
    inference(negUnitSimplification,[status(thm)],[c_6506,c_6684])).

tff(c_8071,plain,
    ( r2_hidden('#skF_4',k3_xboole_0('#skF_5',k1_tarski('#skF_6')))
    | ~ r2_hidden('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_8044,c_6685])).

tff(c_8091,plain,(
    r2_hidden('#skF_4',k3_xboole_0('#skF_5',k1_tarski('#skF_6'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6505,c_8071])).

tff(c_6519,plain,(
    ! [A_648,B_649,C_650] :
      ( ~ r1_xboole_0(A_648,B_649)
      | ~ r2_hidden(C_650,B_649)
      | ~ r2_hidden(C_650,A_648) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_6527,plain,(
    ! [C_650,A_11,B_12] :
      ( ~ r2_hidden(C_650,k5_xboole_0(A_11,B_12))
      | ~ r2_hidden(C_650,k3_xboole_0(A_11,B_12)) ) ),
    inference(resolution,[status(thm)],[c_22,c_6519])).

tff(c_6968,plain,(
    ! [A_689,B_691,C_690] :
      ( ~ r2_hidden(A_689,k3_xboole_0(B_691,C_690))
      | r2_hidden(A_689,C_690)
      | ~ r2_hidden(A_689,B_691) ) ),
    inference(resolution,[status(thm)],[c_6955,c_6527])).

tff(c_8106,plain,
    ( r2_hidden('#skF_4',k1_tarski('#skF_6'))
    | ~ r2_hidden('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_8091,c_6968])).

tff(c_8113,plain,(
    r2_hidden('#skF_4',k1_tarski('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6505,c_8106])).

tff(c_8125,plain,(
    '#skF_6' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_8113,c_30])).

tff(c_8132,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_6406,c_8125])).

tff(c_8133,plain,(
    r2_hidden('#skF_4','#skF_5') ),
    inference(splitRight,[status(thm)],[c_6408])).

tff(c_8683,plain,(
    ! [A_856,C_857,B_858] :
      ( r2_hidden(A_856,C_857)
      | ~ r2_hidden(A_856,B_858)
      | r2_hidden(A_856,k5_xboole_0(B_858,C_857)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_9783,plain,(
    ! [A_952,A_953,B_954] :
      ( r2_hidden(A_952,k3_xboole_0(A_953,B_954))
      | ~ r2_hidden(A_952,A_953)
      | r2_hidden(A_952,k4_xboole_0(A_953,B_954)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_8683])).

tff(c_8134,plain,(
    '#skF_7' != '#skF_9' ),
    inference(splitRight,[status(thm)],[c_6408])).

tff(c_56,plain,
    ( ~ r2_hidden('#skF_4',k4_xboole_0('#skF_5',k1_tarski('#skF_6')))
    | '#skF_7' = '#skF_9'
    | ~ r2_hidden('#skF_7','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_8344,plain,
    ( ~ r2_hidden('#skF_4',k4_xboole_0('#skF_5',k1_tarski('#skF_6')))
    | '#skF_7' = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6405,c_56])).

tff(c_8345,plain,(
    ~ r2_hidden('#skF_4',k4_xboole_0('#skF_5',k1_tarski('#skF_6'))) ),
    inference(negUnitSimplification,[status(thm)],[c_8134,c_8344])).

tff(c_9813,plain,
    ( r2_hidden('#skF_4',k3_xboole_0('#skF_5',k1_tarski('#skF_6')))
    | ~ r2_hidden('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_9783,c_8345])).

tff(c_9831,plain,(
    r2_hidden('#skF_4',k3_xboole_0('#skF_5',k1_tarski('#skF_6'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8133,c_9813])).

tff(c_8197,plain,(
    ! [A_804,B_805,C_806] :
      ( ~ r1_xboole_0(A_804,B_805)
      | ~ r2_hidden(C_806,B_805)
      | ~ r2_hidden(C_806,A_804) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_8205,plain,(
    ! [C_806,A_11,B_12] :
      ( ~ r2_hidden(C_806,k5_xboole_0(A_11,B_12))
      | ~ r2_hidden(C_806,k3_xboole_0(A_11,B_12)) ) ),
    inference(resolution,[status(thm)],[c_22,c_8197])).

tff(c_8701,plain,(
    ! [A_856,B_858,C_857] :
      ( ~ r2_hidden(A_856,k3_xboole_0(B_858,C_857))
      | r2_hidden(A_856,C_857)
      | ~ r2_hidden(A_856,B_858) ) ),
    inference(resolution,[status(thm)],[c_8683,c_8205])).

tff(c_9842,plain,
    ( r2_hidden('#skF_4',k1_tarski('#skF_6'))
    | ~ r2_hidden('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_9831,c_8701])).

tff(c_9849,plain,(
    r2_hidden('#skF_4',k1_tarski('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8133,c_9842])).

tff(c_9877,plain,(
    '#skF_6' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_9849,c_30])).

tff(c_9884,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_6406,c_9877])).

tff(c_9885,plain,(
    '#skF_7' = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_6404])).

tff(c_9886,plain,(
    '#skF_6' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_6404])).

tff(c_9918,plain,(
    r2_hidden('#skF_9',k4_xboole_0('#skF_8',k1_tarski('#skF_9'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9885,c_9886,c_64])).

tff(c_9953,plain,(
    ! [A_968,B_969,C_970] :
      ( ~ r1_xboole_0(A_968,B_969)
      | ~ r2_hidden(C_970,B_969)
      | ~ r2_hidden(C_970,A_968) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_9972,plain,(
    ! [C_974,B_975,A_976] :
      ( ~ r2_hidden(C_974,B_975)
      | ~ r2_hidden(C_974,k4_xboole_0(A_976,B_975)) ) ),
    inference(resolution,[status(thm)],[c_28,c_9953])).

tff(c_9975,plain,(
    ~ r2_hidden('#skF_9',k1_tarski('#skF_9')) ),
    inference(resolution,[status(thm)],[c_9918,c_9972])).

tff(c_9987,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_9975])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.34  % Computer   : n009.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.34  % CPULimit   : 60
% 0.15/0.34  % DateTime   : Tue Dec  1 20:25:41 EST 2020
% 0.15/0.34  % CPUTime    : 
% 0.15/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.38/2.68  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.38/2.69  
% 7.38/2.69  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.38/2.69  %$ r2_hidden > r1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_9 > #skF_8 > #skF_4 > #skF_2 > #skF_1
% 7.38/2.69  
% 7.38/2.69  %Foreground sorts:
% 7.38/2.69  
% 7.38/2.69  
% 7.38/2.69  %Background operators:
% 7.38/2.69  
% 7.38/2.69  
% 7.38/2.69  %Foreground operators:
% 7.38/2.69  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.38/2.69  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.38/2.69  tff(k1_tarski, type, k1_tarski: $i > $i).
% 7.38/2.69  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 7.38/2.69  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 7.38/2.69  tff('#skF_7', type, '#skF_7': $i).
% 7.38/2.69  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 7.38/2.69  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 7.38/2.69  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 7.38/2.69  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 7.38/2.69  tff('#skF_5', type, '#skF_5': $i).
% 7.38/2.69  tff('#skF_6', type, '#skF_6': $i).
% 7.38/2.69  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 7.38/2.69  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 7.70/2.69  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 7.70/2.69  tff('#skF_9', type, '#skF_9': $i).
% 7.70/2.69  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 7.70/2.69  tff('#skF_8', type, '#skF_8': $i).
% 7.70/2.69  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.70/2.69  tff('#skF_4', type, '#skF_4': $i).
% 7.70/2.69  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.70/2.69  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 7.70/2.69  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 7.70/2.69  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 7.70/2.69  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 7.70/2.69  
% 7.70/2.71  tff(f_67, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 7.70/2.71  tff(f_89, negated_conjecture, ~(![A, B, C]: (r2_hidden(A, k4_xboole_0(B, k1_tarski(C))) <=> (r2_hidden(A, B) & ~(A = C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_zfmisc_1)).
% 7.70/2.71  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 7.70/2.71  tff(f_58, axiom, (![A, B, C]: (k3_xboole_0(k3_xboole_0(A, B), C) = k3_xboole_0(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_xboole_1)).
% 7.70/2.71  tff(f_56, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 7.70/2.71  tff(f_54, axiom, (![A, B]: r1_xboole_0(k3_xboole_0(A, B), k5_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l97_xboole_1)).
% 7.70/2.71  tff(f_52, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 7.70/2.71  tff(f_34, axiom, (![A, B, C]: (r2_hidden(A, k5_xboole_0(B, C)) <=> ~(r2_hidden(A, B) <=> r2_hidden(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_0)).
% 7.70/2.71  tff(f_60, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_xboole_1)).
% 7.70/2.71  tff(c_32, plain, (![C_24]: (r2_hidden(C_24, k1_tarski(C_24)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 7.70/2.71  tff(c_64, plain, ('#skF_6'!='#skF_4' | r2_hidden('#skF_7', k4_xboole_0('#skF_8', k1_tarski('#skF_9')))), inference(cnfTransformation, [status(thm)], [f_89])).
% 7.70/2.71  tff(c_120, plain, ('#skF_6'!='#skF_4'), inference(splitLeft, [status(thm)], [c_64])).
% 7.70/2.71  tff(c_66, plain, (r2_hidden('#skF_4', '#skF_5') | r2_hidden('#skF_7', k4_xboole_0('#skF_8', k1_tarski('#skF_9')))), inference(cnfTransformation, [status(thm)], [f_89])).
% 7.70/2.71  tff(c_152, plain, (r2_hidden('#skF_7', k4_xboole_0('#skF_8', k1_tarski('#skF_9')))), inference(splitLeft, [status(thm)], [c_66])).
% 7.70/2.71  tff(c_2, plain, (![A_1]: (k3_xboole_0(A_1, A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 7.70/2.71  tff(c_187, plain, (![A_82, B_83, C_84]: (k3_xboole_0(k3_xboole_0(A_82, B_83), C_84)=k3_xboole_0(A_82, k3_xboole_0(B_83, C_84)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 7.70/2.71  tff(c_212, plain, (![A_1, C_84]: (k3_xboole_0(A_1, k3_xboole_0(A_1, C_84))=k3_xboole_0(A_1, C_84))), inference(superposition, [status(thm), theory('equality')], [c_2, c_187])).
% 7.70/2.71  tff(c_24, plain, (![A_13, B_14]: (k5_xboole_0(A_13, k3_xboole_0(A_13, B_14))=k4_xboole_0(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_56])).
% 7.70/2.71  tff(c_22, plain, (![A_11, B_12]: (r1_xboole_0(k3_xboole_0(A_11, B_12), k5_xboole_0(A_11, B_12)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 7.70/2.71  tff(c_162, plain, (![A_76, B_77, C_78]: (~r1_xboole_0(A_76, B_77) | ~r2_hidden(C_78, B_77) | ~r2_hidden(C_78, A_76))), inference(cnfTransformation, [status(thm)], [f_52])).
% 7.70/2.71  tff(c_442, plain, (![C_104, A_105, B_106]: (~r2_hidden(C_104, k5_xboole_0(A_105, B_106)) | ~r2_hidden(C_104, k3_xboole_0(A_105, B_106)))), inference(resolution, [status(thm)], [c_22, c_162])).
% 7.70/2.71  tff(c_451, plain, (![C_104, A_13, B_14]: (~r2_hidden(C_104, k4_xboole_0(A_13, B_14)) | ~r2_hidden(C_104, k3_xboole_0(A_13, k3_xboole_0(A_13, B_14))))), inference(superposition, [status(thm), theory('equality')], [c_24, c_442])).
% 7.70/2.71  tff(c_467, plain, (![C_107, A_108, B_109]: (~r2_hidden(C_107, k4_xboole_0(A_108, B_109)) | ~r2_hidden(C_107, k3_xboole_0(A_108, B_109)))), inference(demodulation, [status(thm), theory('equality')], [c_212, c_451])).
% 7.70/2.71  tff(c_483, plain, (~r2_hidden('#skF_7', k3_xboole_0('#skF_8', k1_tarski('#skF_9')))), inference(resolution, [status(thm)], [c_152, c_467])).
% 7.70/2.71  tff(c_58, plain, ('#skF_6'!='#skF_4' | '#skF_7'='#skF_9' | ~r2_hidden('#skF_7', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_89])).
% 7.70/2.71  tff(c_98, plain, (~r2_hidden('#skF_7', '#skF_8')), inference(splitLeft, [status(thm)], [c_58])).
% 7.70/2.71  tff(c_583, plain, (![A_114, B_115, C_116]: (r2_hidden(A_114, B_115) | r2_hidden(A_114, C_116) | ~r2_hidden(A_114, k5_xboole_0(B_115, C_116)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 7.70/2.71  tff(c_2143, plain, (![A_253, A_254, B_255]: (r2_hidden(A_253, A_254) | r2_hidden(A_253, k3_xboole_0(A_254, B_255)) | ~r2_hidden(A_253, k4_xboole_0(A_254, B_255)))), inference(superposition, [status(thm), theory('equality')], [c_24, c_583])).
% 7.70/2.71  tff(c_2163, plain, (r2_hidden('#skF_7', '#skF_8') | r2_hidden('#skF_7', k3_xboole_0('#skF_8', k1_tarski('#skF_9')))), inference(resolution, [status(thm)], [c_152, c_2143])).
% 7.70/2.71  tff(c_2180, plain, $false, inference(negUnitSimplification, [status(thm)], [c_483, c_98, c_2163])).
% 7.70/2.71  tff(c_2181, plain, (r2_hidden('#skF_4', '#skF_5')), inference(splitRight, [status(thm)], [c_66])).
% 7.70/2.71  tff(c_2658, plain, (![A_309, C_310, B_311]: (r2_hidden(A_309, C_310) | ~r2_hidden(A_309, B_311) | r2_hidden(A_309, k5_xboole_0(B_311, C_310)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 7.70/2.71  tff(c_4388, plain, (![A_445, A_446, B_447]: (r2_hidden(A_445, k3_xboole_0(A_446, B_447)) | ~r2_hidden(A_445, A_446) | r2_hidden(A_445, k4_xboole_0(A_446, B_447)))), inference(superposition, [status(thm), theory('equality')], [c_24, c_2658])).
% 7.70/2.71  tff(c_2182, plain, (~r2_hidden('#skF_7', k4_xboole_0('#skF_8', k1_tarski('#skF_9')))), inference(splitRight, [status(thm)], [c_66])).
% 7.70/2.71  tff(c_62, plain, (~r2_hidden('#skF_4', k4_xboole_0('#skF_5', k1_tarski('#skF_6'))) | r2_hidden('#skF_7', k4_xboole_0('#skF_8', k1_tarski('#skF_9')))), inference(cnfTransformation, [status(thm)], [f_89])).
% 7.70/2.71  tff(c_2357, plain, (~r2_hidden('#skF_4', k4_xboole_0('#skF_5', k1_tarski('#skF_6')))), inference(negUnitSimplification, [status(thm)], [c_2182, c_62])).
% 7.70/2.71  tff(c_4423, plain, (r2_hidden('#skF_4', k3_xboole_0('#skF_5', k1_tarski('#skF_6'))) | ~r2_hidden('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_4388, c_2357])).
% 7.70/2.71  tff(c_4447, plain, (r2_hidden('#skF_4', k3_xboole_0('#skF_5', k1_tarski('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_2181, c_4423])).
% 7.70/2.71  tff(c_14, plain, (![A_3, C_5, B_4]: (r2_hidden(A_3, C_5) | ~r2_hidden(A_3, B_4) | r2_hidden(A_3, k5_xboole_0(B_4, C_5)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 7.70/2.71  tff(c_2232, plain, (![A_271, B_272, C_273]: (k3_xboole_0(k3_xboole_0(A_271, B_272), C_273)=k3_xboole_0(A_271, k3_xboole_0(B_272, C_273)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 7.70/2.71  tff(c_2688, plain, (![A_314, B_315, C_316]: (r1_xboole_0(k3_xboole_0(A_314, k3_xboole_0(B_315, C_316)), k5_xboole_0(k3_xboole_0(A_314, B_315), C_316)))), inference(superposition, [status(thm), theory('equality')], [c_2232, c_22])).
% 7.70/2.71  tff(c_2748, plain, (![A_317, A_318]: (r1_xboole_0(k3_xboole_0(A_317, A_318), k5_xboole_0(k3_xboole_0(A_317, A_318), A_318)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_2688])).
% 7.70/2.71  tff(c_16, plain, (![A_6, B_7, C_10]: (~r1_xboole_0(A_6, B_7) | ~r2_hidden(C_10, B_7) | ~r2_hidden(C_10, A_6))), inference(cnfTransformation, [status(thm)], [f_52])).
% 7.70/2.71  tff(c_3749, plain, (![C_404, A_405, A_406]: (~r2_hidden(C_404, k5_xboole_0(k3_xboole_0(A_405, A_406), A_406)) | ~r2_hidden(C_404, k3_xboole_0(A_405, A_406)))), inference(resolution, [status(thm)], [c_2748, c_16])).
% 7.70/2.71  tff(c_3788, plain, (![A_3, C_5, A_405]: (r2_hidden(A_3, C_5) | ~r2_hidden(A_3, k3_xboole_0(A_405, C_5)))), inference(resolution, [status(thm)], [c_14, c_3749])).
% 7.70/2.71  tff(c_4462, plain, (r2_hidden('#skF_4', k1_tarski('#skF_6'))), inference(resolution, [status(thm)], [c_4447, c_3788])).
% 7.70/2.71  tff(c_30, plain, (![C_24, A_20]: (C_24=A_20 | ~r2_hidden(C_24, k1_tarski(A_20)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 7.70/2.71  tff(c_4473, plain, ('#skF_6'='#skF_4'), inference(resolution, [status(thm)], [c_4462, c_30])).
% 7.70/2.71  tff(c_4480, plain, $false, inference(negUnitSimplification, [status(thm)], [c_120, c_4473])).
% 7.70/2.71  tff(c_4481, plain, (r2_hidden('#skF_7', k4_xboole_0('#skF_8', k1_tarski('#skF_9')))), inference(splitRight, [status(thm)], [c_64])).
% 7.70/2.71  tff(c_4582, plain, (![A_469, B_470, C_471]: (k3_xboole_0(k3_xboole_0(A_469, B_470), C_471)=k3_xboole_0(A_469, k3_xboole_0(B_470, C_471)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 7.70/2.71  tff(c_4614, plain, (![A_1, C_471]: (k3_xboole_0(A_1, k3_xboole_0(A_1, C_471))=k3_xboole_0(A_1, C_471))), inference(superposition, [status(thm), theory('equality')], [c_2, c_4582])).
% 7.70/2.71  tff(c_4489, plain, (![A_448, B_449]: (k5_xboole_0(A_448, k3_xboole_0(A_448, B_449))=k4_xboole_0(A_448, B_449))), inference(cnfTransformation, [status(thm)], [f_56])).
% 7.70/2.71  tff(c_4495, plain, (![A_448, B_449]: (r1_xboole_0(k3_xboole_0(A_448, k3_xboole_0(A_448, B_449)), k4_xboole_0(A_448, B_449)))), inference(superposition, [status(thm), theory('equality')], [c_4489, c_22])).
% 7.70/2.71  tff(c_4673, plain, (![A_474, B_475]: (r1_xboole_0(k3_xboole_0(A_474, B_475), k4_xboole_0(A_474, B_475)))), inference(demodulation, [status(thm), theory('equality')], [c_4614, c_4495])).
% 7.70/2.71  tff(c_4859, plain, (![C_488, A_489, B_490]: (~r2_hidden(C_488, k4_xboole_0(A_489, B_490)) | ~r2_hidden(C_488, k3_xboole_0(A_489, B_490)))), inference(resolution, [status(thm)], [c_4673, c_16])).
% 7.70/2.71  tff(c_4875, plain, (~r2_hidden('#skF_7', k3_xboole_0('#skF_8', k1_tarski('#skF_9')))), inference(resolution, [status(thm)], [c_4481, c_4859])).
% 7.70/2.71  tff(c_4823, plain, (![A_482, B_483, C_484]: (r2_hidden(A_482, B_483) | r2_hidden(A_482, C_484) | ~r2_hidden(A_482, k5_xboole_0(B_483, C_484)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 7.70/2.71  tff(c_6366, plain, (![A_623, A_624, B_625]: (r2_hidden(A_623, A_624) | r2_hidden(A_623, k3_xboole_0(A_624, B_625)) | ~r2_hidden(A_623, k4_xboole_0(A_624, B_625)))), inference(superposition, [status(thm), theory('equality')], [c_24, c_4823])).
% 7.70/2.71  tff(c_6386, plain, (r2_hidden('#skF_7', '#skF_8') | r2_hidden('#skF_7', k3_xboole_0('#skF_8', k1_tarski('#skF_9')))), inference(resolution, [status(thm)], [c_4481, c_6366])).
% 7.70/2.71  tff(c_6403, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4875, c_98, c_6386])).
% 7.70/2.71  tff(c_6404, plain, ('#skF_6'!='#skF_4' | '#skF_7'='#skF_9'), inference(splitRight, [status(thm)], [c_58])).
% 7.70/2.71  tff(c_6406, plain, ('#skF_6'!='#skF_4'), inference(splitLeft, [status(thm)], [c_6404])).
% 7.70/2.71  tff(c_6405, plain, (r2_hidden('#skF_7', '#skF_8')), inference(splitRight, [status(thm)], [c_58])).
% 7.70/2.71  tff(c_60, plain, (r2_hidden('#skF_4', '#skF_5') | '#skF_7'='#skF_9' | ~r2_hidden('#skF_7', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_89])).
% 7.70/2.71  tff(c_6408, plain, (r2_hidden('#skF_4', '#skF_5') | '#skF_7'='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_6405, c_60])).
% 7.70/2.71  tff(c_6409, plain, ('#skF_7'='#skF_9'), inference(splitLeft, [status(thm)], [c_6408])).
% 7.70/2.71  tff(c_6467, plain, (r2_hidden('#skF_4', '#skF_5') | r2_hidden('#skF_9', k4_xboole_0('#skF_8', k1_tarski('#skF_9')))), inference(demodulation, [status(thm), theory('equality')], [c_6409, c_66])).
% 7.70/2.71  tff(c_6468, plain, (r2_hidden('#skF_9', k4_xboole_0('#skF_8', k1_tarski('#skF_9')))), inference(splitLeft, [status(thm)], [c_6467])).
% 7.70/2.71  tff(c_28, plain, (![A_18, B_19]: (r1_xboole_0(k4_xboole_0(A_18, B_19), B_19))), inference(cnfTransformation, [status(thm)], [f_60])).
% 7.70/2.71  tff(c_6479, plain, (![A_639, B_640, C_641]: (~r1_xboole_0(A_639, B_640) | ~r2_hidden(C_641, B_640) | ~r2_hidden(C_641, A_639))), inference(cnfTransformation, [status(thm)], [f_52])).
% 7.70/2.71  tff(c_6489, plain, (![C_642, B_643, A_644]: (~r2_hidden(C_642, B_643) | ~r2_hidden(C_642, k4_xboole_0(A_644, B_643)))), inference(resolution, [status(thm)], [c_28, c_6479])).
% 7.70/2.71  tff(c_6492, plain, (~r2_hidden('#skF_9', k1_tarski('#skF_9'))), inference(resolution, [status(thm)], [c_6468, c_6489])).
% 7.70/2.71  tff(c_6504, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_6492])).
% 7.70/2.71  tff(c_6505, plain, (r2_hidden('#skF_4', '#skF_5')), inference(splitRight, [status(thm)], [c_6467])).
% 7.70/2.71  tff(c_6955, plain, (![A_689, C_690, B_691]: (r2_hidden(A_689, C_690) | ~r2_hidden(A_689, B_691) | r2_hidden(A_689, k5_xboole_0(B_691, C_690)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 7.70/2.71  tff(c_8044, plain, (![A_786, A_787, B_788]: (r2_hidden(A_786, k3_xboole_0(A_787, B_788)) | ~r2_hidden(A_786, A_787) | r2_hidden(A_786, k4_xboole_0(A_787, B_788)))), inference(superposition, [status(thm), theory('equality')], [c_24, c_6955])).
% 7.70/2.71  tff(c_6506, plain, (~r2_hidden('#skF_9', k4_xboole_0('#skF_8', k1_tarski('#skF_9')))), inference(splitRight, [status(thm)], [c_6467])).
% 7.70/2.71  tff(c_6684, plain, (~r2_hidden('#skF_4', k4_xboole_0('#skF_5', k1_tarski('#skF_6'))) | r2_hidden('#skF_9', k4_xboole_0('#skF_8', k1_tarski('#skF_9')))), inference(demodulation, [status(thm), theory('equality')], [c_6409, c_62])).
% 7.70/2.71  tff(c_6685, plain, (~r2_hidden('#skF_4', k4_xboole_0('#skF_5', k1_tarski('#skF_6')))), inference(negUnitSimplification, [status(thm)], [c_6506, c_6684])).
% 7.70/2.71  tff(c_8071, plain, (r2_hidden('#skF_4', k3_xboole_0('#skF_5', k1_tarski('#skF_6'))) | ~r2_hidden('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_8044, c_6685])).
% 7.70/2.71  tff(c_8091, plain, (r2_hidden('#skF_4', k3_xboole_0('#skF_5', k1_tarski('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_6505, c_8071])).
% 7.70/2.71  tff(c_6519, plain, (![A_648, B_649, C_650]: (~r1_xboole_0(A_648, B_649) | ~r2_hidden(C_650, B_649) | ~r2_hidden(C_650, A_648))), inference(cnfTransformation, [status(thm)], [f_52])).
% 7.70/2.71  tff(c_6527, plain, (![C_650, A_11, B_12]: (~r2_hidden(C_650, k5_xboole_0(A_11, B_12)) | ~r2_hidden(C_650, k3_xboole_0(A_11, B_12)))), inference(resolution, [status(thm)], [c_22, c_6519])).
% 7.70/2.71  tff(c_6968, plain, (![A_689, B_691, C_690]: (~r2_hidden(A_689, k3_xboole_0(B_691, C_690)) | r2_hidden(A_689, C_690) | ~r2_hidden(A_689, B_691))), inference(resolution, [status(thm)], [c_6955, c_6527])).
% 7.70/2.71  tff(c_8106, plain, (r2_hidden('#skF_4', k1_tarski('#skF_6')) | ~r2_hidden('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_8091, c_6968])).
% 7.70/2.71  tff(c_8113, plain, (r2_hidden('#skF_4', k1_tarski('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_6505, c_8106])).
% 7.70/2.71  tff(c_8125, plain, ('#skF_6'='#skF_4'), inference(resolution, [status(thm)], [c_8113, c_30])).
% 7.70/2.71  tff(c_8132, plain, $false, inference(negUnitSimplification, [status(thm)], [c_6406, c_8125])).
% 7.70/2.71  tff(c_8133, plain, (r2_hidden('#skF_4', '#skF_5')), inference(splitRight, [status(thm)], [c_6408])).
% 7.70/2.71  tff(c_8683, plain, (![A_856, C_857, B_858]: (r2_hidden(A_856, C_857) | ~r2_hidden(A_856, B_858) | r2_hidden(A_856, k5_xboole_0(B_858, C_857)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 7.70/2.71  tff(c_9783, plain, (![A_952, A_953, B_954]: (r2_hidden(A_952, k3_xboole_0(A_953, B_954)) | ~r2_hidden(A_952, A_953) | r2_hidden(A_952, k4_xboole_0(A_953, B_954)))), inference(superposition, [status(thm), theory('equality')], [c_24, c_8683])).
% 7.70/2.71  tff(c_8134, plain, ('#skF_7'!='#skF_9'), inference(splitRight, [status(thm)], [c_6408])).
% 7.70/2.71  tff(c_56, plain, (~r2_hidden('#skF_4', k4_xboole_0('#skF_5', k1_tarski('#skF_6'))) | '#skF_7'='#skF_9' | ~r2_hidden('#skF_7', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_89])).
% 7.70/2.71  tff(c_8344, plain, (~r2_hidden('#skF_4', k4_xboole_0('#skF_5', k1_tarski('#skF_6'))) | '#skF_7'='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_6405, c_56])).
% 7.70/2.71  tff(c_8345, plain, (~r2_hidden('#skF_4', k4_xboole_0('#skF_5', k1_tarski('#skF_6')))), inference(negUnitSimplification, [status(thm)], [c_8134, c_8344])).
% 7.70/2.71  tff(c_9813, plain, (r2_hidden('#skF_4', k3_xboole_0('#skF_5', k1_tarski('#skF_6'))) | ~r2_hidden('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_9783, c_8345])).
% 7.70/2.71  tff(c_9831, plain, (r2_hidden('#skF_4', k3_xboole_0('#skF_5', k1_tarski('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_8133, c_9813])).
% 7.70/2.71  tff(c_8197, plain, (![A_804, B_805, C_806]: (~r1_xboole_0(A_804, B_805) | ~r2_hidden(C_806, B_805) | ~r2_hidden(C_806, A_804))), inference(cnfTransformation, [status(thm)], [f_52])).
% 7.70/2.71  tff(c_8205, plain, (![C_806, A_11, B_12]: (~r2_hidden(C_806, k5_xboole_0(A_11, B_12)) | ~r2_hidden(C_806, k3_xboole_0(A_11, B_12)))), inference(resolution, [status(thm)], [c_22, c_8197])).
% 7.70/2.71  tff(c_8701, plain, (![A_856, B_858, C_857]: (~r2_hidden(A_856, k3_xboole_0(B_858, C_857)) | r2_hidden(A_856, C_857) | ~r2_hidden(A_856, B_858))), inference(resolution, [status(thm)], [c_8683, c_8205])).
% 7.70/2.71  tff(c_9842, plain, (r2_hidden('#skF_4', k1_tarski('#skF_6')) | ~r2_hidden('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_9831, c_8701])).
% 7.70/2.71  tff(c_9849, plain, (r2_hidden('#skF_4', k1_tarski('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_8133, c_9842])).
% 7.70/2.71  tff(c_9877, plain, ('#skF_6'='#skF_4'), inference(resolution, [status(thm)], [c_9849, c_30])).
% 7.70/2.71  tff(c_9884, plain, $false, inference(negUnitSimplification, [status(thm)], [c_6406, c_9877])).
% 7.70/2.71  tff(c_9885, plain, ('#skF_7'='#skF_9'), inference(splitRight, [status(thm)], [c_6404])).
% 7.70/2.71  tff(c_9886, plain, ('#skF_6'='#skF_4'), inference(splitRight, [status(thm)], [c_6404])).
% 7.70/2.71  tff(c_9918, plain, (r2_hidden('#skF_9', k4_xboole_0('#skF_8', k1_tarski('#skF_9')))), inference(demodulation, [status(thm), theory('equality')], [c_9885, c_9886, c_64])).
% 7.70/2.71  tff(c_9953, plain, (![A_968, B_969, C_970]: (~r1_xboole_0(A_968, B_969) | ~r2_hidden(C_970, B_969) | ~r2_hidden(C_970, A_968))), inference(cnfTransformation, [status(thm)], [f_52])).
% 7.70/2.71  tff(c_9972, plain, (![C_974, B_975, A_976]: (~r2_hidden(C_974, B_975) | ~r2_hidden(C_974, k4_xboole_0(A_976, B_975)))), inference(resolution, [status(thm)], [c_28, c_9953])).
% 7.70/2.71  tff(c_9975, plain, (~r2_hidden('#skF_9', k1_tarski('#skF_9'))), inference(resolution, [status(thm)], [c_9918, c_9972])).
% 7.70/2.71  tff(c_9987, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_9975])).
% 7.70/2.71  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.70/2.71  
% 7.70/2.71  Inference rules
% 7.70/2.71  ----------------------
% 7.70/2.71  #Ref     : 0
% 7.70/2.71  #Sup     : 2333
% 7.70/2.71  #Fact    : 0
% 7.70/2.71  #Define  : 0
% 7.70/2.71  #Split   : 7
% 7.70/2.71  #Chain   : 0
% 7.70/2.71  #Close   : 0
% 7.70/2.71  
% 7.70/2.71  Ordering : KBO
% 7.70/2.71  
% 7.70/2.71  Simplification rules
% 7.70/2.71  ----------------------
% 7.70/2.71  #Subsume      : 216
% 7.70/2.71  #Demod        : 1810
% 7.70/2.71  #Tautology    : 862
% 7.70/2.71  #SimpNegUnit  : 10
% 7.70/2.71  #BackRed      : 9
% 7.70/2.71  
% 7.70/2.71  #Partial instantiations: 0
% 7.70/2.71  #Strategies tried      : 1
% 7.70/2.71  
% 7.70/2.71  Timing (in seconds)
% 7.70/2.71  ----------------------
% 7.70/2.72  Preprocessing        : 0.37
% 7.70/2.72  Parsing              : 0.19
% 7.70/2.72  CNF conversion       : 0.03
% 7.70/2.72  Main loop            : 1.48
% 7.70/2.72  Inferencing          : 0.51
% 7.70/2.72  Reduction            : 0.52
% 7.70/2.72  Demodulation         : 0.40
% 7.70/2.72  BG Simplification    : 0.07
% 7.70/2.72  Subsumption          : 0.27
% 7.70/2.72  Abstraction          : 0.07
% 7.70/2.72  MUC search           : 0.00
% 7.70/2.72  Cooper               : 0.00
% 7.70/2.72  Total                : 1.89
% 7.70/2.72  Index Insertion      : 0.00
% 7.70/2.72  Index Deletion       : 0.00
% 7.70/2.72  Index Matching       : 0.00
% 7.70/2.72  BG Taut test         : 0.00
%------------------------------------------------------------------------------

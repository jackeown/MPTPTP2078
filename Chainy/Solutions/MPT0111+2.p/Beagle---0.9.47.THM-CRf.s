%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0111+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:07:15 EST 2020

% Result     : Theorem 11.70s
% Output     : CNFRefutation 11.87s
% Verified   : 
% Statistics : Number of formulae       :  129 ( 276 expanded)
%              Number of leaves         :   44 ( 106 expanded)
%              Depth                    :    7
%              Number of atoms          :  148 ( 557 expanded)
%              Number of equality atoms :   29 ( 130 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    1 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r3_xboole_0 > r2_xboole_0 > r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > o_0_0_xboole_0 > k1_xboole_0 > #skF_13 > #skF_24 > #skF_11 > #skF_20 > #skF_18 > #skF_6 > #skF_1 > #skF_17 > #skF_19 > #skF_4 > #skF_10 > #skF_12 > #skF_23 > #skF_5 > #skF_21 > #skF_9 > #skF_7 > #skF_14 > #skF_22 > #skF_3 > #skF_2 > #skF_8 > #skF_16 > #skF_15

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_13',type,(
    '#skF_13': ( $i * ( $i * $i ) ) > $i )).

tff('#skF_24',type,(
    '#skF_24': ( $i * ( $i * $i ) ) > $i )).

tff('#skF_11',type,(
    '#skF_11': ( $i * $i ) > $i )).

tff(o_0_0_xboole_0,type,(
    o_0_0_xboole_0: $i )).

tff('#skF_20',type,(
    '#skF_20': $i )).

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

tff('#skF_19',type,(
    '#skF_19': $i )).

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

tff('#skF_23',type,(
    '#skF_23': ( $i * ( $i * $i ) ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * ( $i * $i ) ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_21',type,(
    '#skF_21': $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * ( $i * $i ) ) > $i )).

tff(r2_xboole_0,type,(
    r2_xboole_0: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_14',type,(
    '#skF_14': ( $i * ( $i * $i ) ) > $i )).

tff('#skF_22',type,(
    '#skF_22': $i )).

tff(r3_xboole_0,type,(
    r3_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': ( $i * ( $i * $i ) ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

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

tff(f_242,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_248,axiom,(
    ! [A,B] :
      ( r3_xboole_0(A,B)
    <=> ( r1_tarski(A,B)
        | r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_xboole_0)).

tff(f_303,negated_conjecture,(
    ~ ! [A,B] :
        ( ~ ( ~ r2_xboole_0(A,B)
            & A != B
            & ~ r2_xboole_0(B,A) )
      <=> r3_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t104_xboole_1)).

tff(f_120,axiom,(
    ! [A,B] :
      ( r2_xboole_0(A,B)
    <=> ( r1_tarski(A,B)
        & A != B ) ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT001+2.ax',d8_xboole_0)).

tff(f_282,axiom,(
    ! [A,B] :
      ( r3_xboole_0(A,B)
     => r3_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r3_xboole_0)).

tff(c_196,plain,(
    ! [B_82] : r1_tarski(B_82,B_82) ),
    inference(cnfTransformation,[status(thm)],[f_242])).

tff(c_12457,plain,(
    ! [A_838,B_839] :
      ( ~ r1_tarski(A_838,B_839)
      | r3_xboole_0(A_838,B_839) ) ),
    inference(cnfTransformation,[status(thm)],[f_248])).

tff(c_234,plain,
    ( '#skF_20' != '#skF_19'
    | ~ r3_xboole_0('#skF_21','#skF_22') ),
    inference(cnfTransformation,[status(thm)],[f_303])).

tff(c_506,plain,(
    ~ r3_xboole_0('#skF_21','#skF_22') ),
    inference(splitLeft,[status(thm)],[c_234])).

tff(c_12464,plain,(
    ~ r1_tarski('#skF_21','#skF_22') ),
    inference(resolution,[status(thm)],[c_12457,c_506])).

tff(c_836,plain,(
    ! [B_426,A_427] :
      ( ~ r1_tarski(B_426,A_427)
      | r3_xboole_0(A_427,B_426) ) ),
    inference(cnfTransformation,[status(thm)],[f_248])).

tff(c_840,plain,(
    ~ r1_tarski('#skF_22','#skF_21') ),
    inference(resolution,[status(thm)],[c_836,c_506])).

tff(c_242,plain,
    ( '#skF_20' != '#skF_19'
    | r2_xboole_0('#skF_22','#skF_21')
    | '#skF_21' = '#skF_22'
    | r2_xboole_0('#skF_21','#skF_22') ),
    inference(cnfTransformation,[status(thm)],[f_303])).

tff(c_841,plain,(
    '#skF_20' != '#skF_19' ),
    inference(splitLeft,[status(thm)],[c_242])).

tff(c_8153,plain,(
    ! [A_701,B_702] :
      ( r2_xboole_0(A_701,B_702)
      | B_702 = A_701
      | ~ r1_tarski(A_701,B_702) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_850,plain,(
    ! [A_430,B_431] :
      ( ~ r1_tarski(A_430,B_431)
      | r3_xboole_0(A_430,B_431) ) ),
    inference(cnfTransformation,[status(thm)],[f_248])).

tff(c_854,plain,(
    ~ r1_tarski('#skF_21','#skF_22') ),
    inference(resolution,[status(thm)],[c_850,c_506])).

tff(c_246,plain,
    ( r3_xboole_0('#skF_19','#skF_20')
    | r2_xboole_0('#skF_22','#skF_21')
    | '#skF_21' = '#skF_22'
    | r2_xboole_0('#skF_21','#skF_22') ),
    inference(cnfTransformation,[status(thm)],[f_303])).

tff(c_918,plain,(
    r2_xboole_0('#skF_21','#skF_22') ),
    inference(splitLeft,[status(thm)],[c_246])).

tff(c_88,plain,(
    ! [A_42,B_43] :
      ( r1_tarski(A_42,B_43)
      | ~ r2_xboole_0(A_42,B_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_926,plain,(
    r1_tarski('#skF_21','#skF_22') ),
    inference(resolution,[status(thm)],[c_918,c_88])).

tff(c_932,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_854,c_926])).

tff(c_934,plain,(
    ~ r2_xboole_0('#skF_21','#skF_22') ),
    inference(splitRight,[status(thm)],[c_246])).

tff(c_240,plain,
    ( ~ r2_xboole_0('#skF_20','#skF_19')
    | r2_xboole_0('#skF_22','#skF_21')
    | '#skF_21' = '#skF_22'
    | r2_xboole_0('#skF_21','#skF_22') ),
    inference(cnfTransformation,[status(thm)],[f_303])).

tff(c_1267,plain,
    ( ~ r2_xboole_0('#skF_20','#skF_19')
    | r2_xboole_0('#skF_22','#skF_21')
    | '#skF_21' = '#skF_22' ),
    inference(negUnitSimplification,[status(thm)],[c_934,c_240])).

tff(c_1268,plain,(
    ~ r2_xboole_0('#skF_20','#skF_19') ),
    inference(splitLeft,[status(thm)],[c_1267])).

tff(c_8159,plain,
    ( '#skF_20' = '#skF_19'
    | ~ r1_tarski('#skF_20','#skF_19') ),
    inference(resolution,[status(thm)],[c_8153,c_1268])).

tff(c_8185,plain,(
    ~ r1_tarski('#skF_20','#skF_19') ),
    inference(negUnitSimplification,[status(thm)],[c_841,c_8159])).

tff(c_244,plain,
    ( ~ r2_xboole_0('#skF_19','#skF_20')
    | r2_xboole_0('#skF_22','#skF_21')
    | '#skF_21' = '#skF_22'
    | r2_xboole_0('#skF_21','#skF_22') ),
    inference(cnfTransformation,[status(thm)],[f_303])).

tff(c_1107,plain,
    ( ~ r2_xboole_0('#skF_19','#skF_20')
    | r2_xboole_0('#skF_22','#skF_21')
    | '#skF_21' = '#skF_22' ),
    inference(negUnitSimplification,[status(thm)],[c_934,c_244])).

tff(c_1108,plain,(
    ~ r2_xboole_0('#skF_19','#skF_20') ),
    inference(splitLeft,[status(thm)],[c_1107])).

tff(c_8162,plain,
    ( '#skF_20' = '#skF_19'
    | ~ r1_tarski('#skF_19','#skF_20') ),
    inference(resolution,[status(thm)],[c_8153,c_1108])).

tff(c_8188,plain,(
    ~ r1_tarski('#skF_19','#skF_20') ),
    inference(negUnitSimplification,[status(thm)],[c_841,c_8162])).

tff(c_933,plain,
    ( '#skF_21' = '#skF_22'
    | r2_xboole_0('#skF_22','#skF_21')
    | r3_xboole_0('#skF_19','#skF_20') ),
    inference(splitRight,[status(thm)],[c_246])).

tff(c_1484,plain,(
    r3_xboole_0('#skF_19','#skF_20') ),
    inference(splitLeft,[status(thm)],[c_933])).

tff(c_222,plain,(
    ! [B_104,A_103] :
      ( r3_xboole_0(B_104,A_103)
      | ~ r3_xboole_0(A_103,B_104) ) ),
    inference(cnfTransformation,[status(thm)],[f_282])).

tff(c_1487,plain,(
    r3_xboole_0('#skF_20','#skF_19') ),
    inference(resolution,[status(thm)],[c_1484,c_222])).

tff(c_11756,plain,(
    ! [B_807,A_808] :
      ( r1_tarski(B_807,A_808)
      | r1_tarski(A_808,B_807)
      | ~ r3_xboole_0(A_808,B_807) ) ),
    inference(cnfTransformation,[status(thm)],[f_248])).

tff(c_11759,plain,
    ( r1_tarski('#skF_19','#skF_20')
    | r1_tarski('#skF_20','#skF_19') ),
    inference(resolution,[status(thm)],[c_1487,c_11756])).

tff(c_11775,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_8185,c_8188,c_11759])).

tff(c_11776,plain,
    ( r2_xboole_0('#skF_22','#skF_21')
    | '#skF_21' = '#skF_22' ),
    inference(splitRight,[status(thm)],[c_933])).

tff(c_11787,plain,(
    '#skF_21' = '#skF_22' ),
    inference(splitLeft,[status(thm)],[c_11776])).

tff(c_11789,plain,(
    ~ r1_tarski('#skF_22','#skF_22') ),
    inference(demodulation,[status(thm),theory(equality)],[c_11787,c_854])).

tff(c_11794,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_196,c_11789])).

tff(c_11795,plain,(
    r2_xboole_0('#skF_22','#skF_21') ),
    inference(splitRight,[status(thm)],[c_11776])).

tff(c_11804,plain,(
    r1_tarski('#skF_22','#skF_21') ),
    inference(resolution,[status(thm)],[c_11795,c_88])).

tff(c_11810,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_840,c_11804])).

tff(c_11811,plain,
    ( '#skF_21' = '#skF_22'
    | r2_xboole_0('#skF_22','#skF_21') ),
    inference(splitRight,[status(thm)],[c_1267])).

tff(c_11832,plain,(
    r2_xboole_0('#skF_22','#skF_21') ),
    inference(splitLeft,[status(thm)],[c_11811])).

tff(c_11840,plain,(
    r1_tarski('#skF_22','#skF_21') ),
    inference(resolution,[status(thm)],[c_11832,c_88])).

tff(c_11846,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_840,c_11840])).

tff(c_11847,plain,(
    '#skF_21' = '#skF_22' ),
    inference(splitRight,[status(thm)],[c_11811])).

tff(c_11850,plain,(
    ~ r1_tarski('#skF_22','#skF_22') ),
    inference(demodulation,[status(thm),theory(equality)],[c_11847,c_854])).

tff(c_11855,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_196,c_11850])).

tff(c_11856,plain,
    ( '#skF_21' = '#skF_22'
    | r2_xboole_0('#skF_22','#skF_21') ),
    inference(splitRight,[status(thm)],[c_1107])).

tff(c_11870,plain,(
    r2_xboole_0('#skF_22','#skF_21') ),
    inference(splitLeft,[status(thm)],[c_11856])).

tff(c_11878,plain,(
    r1_tarski('#skF_22','#skF_21') ),
    inference(resolution,[status(thm)],[c_11870,c_88])).

tff(c_11884,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_840,c_11878])).

tff(c_11885,plain,(
    '#skF_21' = '#skF_22' ),
    inference(splitRight,[status(thm)],[c_11856])).

tff(c_11888,plain,(
    ~ r1_tarski('#skF_22','#skF_22') ),
    inference(demodulation,[status(thm),theory(equality)],[c_11885,c_854])).

tff(c_11893,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_196,c_11888])).

tff(c_11894,plain,
    ( r2_xboole_0('#skF_21','#skF_22')
    | '#skF_21' = '#skF_22'
    | r2_xboole_0('#skF_22','#skF_21') ),
    inference(splitRight,[status(thm)],[c_242])).

tff(c_12465,plain,(
    r2_xboole_0('#skF_22','#skF_21') ),
    inference(splitLeft,[status(thm)],[c_11894])).

tff(c_12473,plain,(
    r1_tarski('#skF_22','#skF_21') ),
    inference(resolution,[status(thm)],[c_12465,c_88])).

tff(c_12479,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_840,c_12473])).

tff(c_12480,plain,
    ( '#skF_21' = '#skF_22'
    | r2_xboole_0('#skF_21','#skF_22') ),
    inference(splitRight,[status(thm)],[c_11894])).

tff(c_12482,plain,(
    r2_xboole_0('#skF_21','#skF_22') ),
    inference(splitLeft,[status(thm)],[c_12480])).

tff(c_12490,plain,(
    r1_tarski('#skF_21','#skF_22') ),
    inference(resolution,[status(thm)],[c_12482,c_88])).

tff(c_12496,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_12464,c_12490])).

tff(c_12497,plain,(
    '#skF_21' = '#skF_22' ),
    inference(splitRight,[status(thm)],[c_12480])).

tff(c_12500,plain,(
    ~ r1_tarski('#skF_22','#skF_22') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12497,c_12464])).

tff(c_12505,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_196,c_12500])).

tff(c_12506,plain,(
    '#skF_20' != '#skF_19' ),
    inference(splitRight,[status(thm)],[c_234])).

tff(c_22793,plain,(
    ! [A_1231,B_1232] :
      ( r2_xboole_0(A_1231,B_1232)
      | B_1232 = A_1231
      | ~ r1_tarski(A_1231,B_1232) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_12507,plain,(
    r3_xboole_0('#skF_21','#skF_22') ),
    inference(splitRight,[status(thm)],[c_234])).

tff(c_232,plain,
    ( ~ r2_xboole_0('#skF_20','#skF_19')
    | ~ r3_xboole_0('#skF_21','#skF_22') ),
    inference(cnfTransformation,[status(thm)],[f_303])).

tff(c_12592,plain,(
    ~ r2_xboole_0('#skF_20','#skF_19') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12507,c_232])).

tff(c_22810,plain,
    ( '#skF_20' = '#skF_19'
    | ~ r1_tarski('#skF_20','#skF_19') ),
    inference(resolution,[status(thm)],[c_22793,c_12592])).

tff(c_22829,plain,(
    ~ r1_tarski('#skF_20','#skF_19') ),
    inference(negUnitSimplification,[status(thm)],[c_12506,c_22810])).

tff(c_236,plain,
    ( ~ r2_xboole_0('#skF_19','#skF_20')
    | ~ r3_xboole_0('#skF_21','#skF_22') ),
    inference(cnfTransformation,[status(thm)],[f_303])).

tff(c_12517,plain,(
    ~ r2_xboole_0('#skF_19','#skF_20') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12507,c_236])).

tff(c_22817,plain,
    ( '#skF_20' = '#skF_19'
    | ~ r1_tarski('#skF_19','#skF_20') ),
    inference(resolution,[status(thm)],[c_22793,c_12517])).

tff(c_22833,plain,(
    ~ r1_tarski('#skF_19','#skF_20') ),
    inference(negUnitSimplification,[status(thm)],[c_12506,c_22817])).

tff(c_238,plain,
    ( r3_xboole_0('#skF_19','#skF_20')
    | ~ r3_xboole_0('#skF_21','#skF_22') ),
    inference(cnfTransformation,[status(thm)],[f_303])).

tff(c_12692,plain,(
    r3_xboole_0('#skF_19','#skF_20') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12507,c_238])).

tff(c_13418,plain,(
    ! [B_911,A_912] :
      ( r3_xboole_0(B_911,A_912)
      | ~ r3_xboole_0(A_912,B_911) ) ),
    inference(cnfTransformation,[status(thm)],[f_282])).

tff(c_13431,plain,(
    r3_xboole_0('#skF_20','#skF_19') ),
    inference(resolution,[status(thm)],[c_12692,c_13418])).

tff(c_24409,plain,(
    ! [B_1286,A_1287] :
      ( r1_tarski(B_1286,A_1287)
      | r1_tarski(A_1287,B_1286)
      | ~ r3_xboole_0(A_1287,B_1286) ) ),
    inference(cnfTransformation,[status(thm)],[f_248])).

tff(c_24415,plain,
    ( r1_tarski('#skF_19','#skF_20')
    | r1_tarski('#skF_20','#skF_19') ),
    inference(resolution,[status(thm)],[c_13431,c_24409])).

tff(c_24435,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_22829,c_22833,c_24415])).
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0044+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:07:11 EST 2020

% Result     : Theorem 5.37s
% Output     : CNFRefutation 5.74s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 126 expanded)
%              Number of leaves         :   42 (  67 expanded)
%              Depth                    :    6
%              Number of atoms          :   47 ( 135 expanded)
%              Number of equality atoms :   24 (  62 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    2 (   1 average)

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

tff(f_136,axiom,(
    ? [A] : v1_xboole_0(A) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT001+2.ax',rc1_xboole_0)).

tff(f_405,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_boole)).

tff(f_389,negated_conjecture,(
    ~ ! [A,B] :
        ( k4_xboole_0(A,B) = k1_xboole_0
      <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_xboole_1)).

tff(f_258,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(c_112,plain,(
    v1_xboole_0('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_320,plain,(
    ! [A_200] :
      ( k1_xboole_0 = A_200
      | ~ v1_xboole_0(A_200) ) ),
    inference(cnfTransformation,[status(thm)],[f_405])).

tff(c_329,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(resolution,[status(thm)],[c_112,c_320])).

tff(c_282,plain,
    ( r1_tarski('#skF_21','#skF_22')
    | k4_xboole_0('#skF_23','#skF_24') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_389])).

tff(c_429,plain,
    ( r1_tarski('#skF_21','#skF_22')
    | k4_xboole_0('#skF_23','#skF_24') = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_329,c_282])).

tff(c_430,plain,(
    k4_xboole_0('#skF_23','#skF_24') = '#skF_9' ),
    inference(splitLeft,[status(thm)],[c_429])).

tff(c_202,plain,(
    ! [A_87,B_88] :
      ( r1_tarski(A_87,B_88)
      | k4_xboole_0(A_87,B_88) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_258])).

tff(c_1478,plain,(
    ! [A_271,B_272] :
      ( r1_tarski(A_271,B_272)
      | k4_xboole_0(A_271,B_272) != '#skF_9' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_329,c_202])).

tff(c_278,plain,
    ( r1_tarski('#skF_21','#skF_22')
    | ~ r1_tarski('#skF_23','#skF_24') ),
    inference(cnfTransformation,[status(thm)],[f_389])).

tff(c_339,plain,(
    ~ r1_tarski('#skF_23','#skF_24') ),
    inference(splitLeft,[status(thm)],[c_278])).

tff(c_1488,plain,(
    k4_xboole_0('#skF_23','#skF_24') != '#skF_9' ),
    inference(resolution,[status(thm)],[c_1478,c_339])).

tff(c_1495,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_430,c_1488])).

tff(c_1497,plain,(
    k4_xboole_0('#skF_23','#skF_24') != '#skF_9' ),
    inference(splitRight,[status(thm)],[c_429])).

tff(c_280,plain,
    ( k4_xboole_0('#skF_21','#skF_22') != k1_xboole_0
    | k4_xboole_0('#skF_23','#skF_24') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_389])).

tff(c_1634,plain,
    ( k4_xboole_0('#skF_21','#skF_22') != '#skF_9'
    | k4_xboole_0('#skF_23','#skF_24') = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_329,c_329,c_280])).

tff(c_1635,plain,(
    k4_xboole_0('#skF_21','#skF_22') != '#skF_9' ),
    inference(negUnitSimplification,[status(thm)],[c_1497,c_1634])).

tff(c_1496,plain,(
    r1_tarski('#skF_21','#skF_22') ),
    inference(splitRight,[status(thm)],[c_429])).

tff(c_204,plain,(
    ! [A_87,B_88] :
      ( k4_xboole_0(A_87,B_88) = k1_xboole_0
      | ~ r1_tarski(A_87,B_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_258])).

tff(c_3000,plain,(
    ! [A_351,B_352] :
      ( k4_xboole_0(A_351,B_352) = '#skF_9'
      | ~ r1_tarski(A_351,B_352) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_329,c_204])).

tff(c_3033,plain,(
    k4_xboole_0('#skF_21','#skF_22') = '#skF_9' ),
    inference(resolution,[status(thm)],[c_1496,c_3000])).

tff(c_3053,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1635,c_3033])).

tff(c_3055,plain,(
    r1_tarski('#skF_23','#skF_24') ),
    inference(splitRight,[status(thm)],[c_278])).

tff(c_276,plain,
    ( k4_xboole_0('#skF_21','#skF_22') != k1_xboole_0
    | ~ r1_tarski('#skF_23','#skF_24') ),
    inference(cnfTransformation,[status(thm)],[f_389])).

tff(c_3154,plain,(
    k4_xboole_0('#skF_21','#skF_22') != '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3055,c_329,c_276])).

tff(c_3054,plain,(
    r1_tarski('#skF_21','#skF_22') ),
    inference(splitRight,[status(thm)],[c_278])).

tff(c_4384,plain,(
    ! [A_430,B_431] :
      ( k4_xboole_0(A_430,B_431) = '#skF_9'
      | ~ r1_tarski(A_430,B_431) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_329,c_204])).

tff(c_4414,plain,(
    k4_xboole_0('#skF_21','#skF_22') = '#skF_9' ),
    inference(resolution,[status(thm)],[c_3054,c_4384])).

tff(c_4434,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3154,c_4414])).
%------------------------------------------------------------------------------

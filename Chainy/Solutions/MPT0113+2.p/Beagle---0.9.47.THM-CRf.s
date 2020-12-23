%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0113+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:07:15 EST 2020

% Result     : Theorem 9.26s
% Output     : CNFRefutation 9.45s
% Verified   : 
% Statistics : Number of formulae       :  101 ( 122 expanded)
%              Number of leaves         :   55 (  66 expanded)
%              Depth                    :    8
%              Number of atoms          :   88 ( 122 expanded)
%              Number of equality atoms :   37 (  49 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r3_xboole_0 > r2_xboole_0 > r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > o_0_0_xboole_0 > k1_xboole_0 > #skF_13 > #skF_11 > #skF_20 > #skF_18 > #skF_6 > #skF_1 > #skF_17 > #skF_22 > #skF_19 > #skF_4 > #skF_10 > #skF_12 > #skF_23 > #skF_5 > #skF_21 > #skF_9 > #skF_7 > #skF_14 > #skF_3 > #skF_2 > #skF_8 > #skF_16 > #skF_15

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_13',type,(
    '#skF_13': ( $i * ( $i * $i ) ) > $i )).

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

tff('#skF_22',type,(
    '#skF_22': ( $i * ( $i * $i ) ) > $i )).

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

tff(f_63,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT001+2.ax',commutativity_k3_xboole_0)).

tff(f_136,axiom,(
    ? [A] : v1_xboole_0(A) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT001+2.ax',rc1_xboole_0)).

tff(f_596,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_boole)).

tff(f_113,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT001+2.ax',d7_xboole_0)).

tff(f_314,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_tarski(A,k4_xboole_0(B,C))
       => ( r1_tarski(A,B)
          & r1_xboole_0(A,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_xboole_1)).

tff(f_440,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_450,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_474,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => B = k2_xboole_0(A,k4_xboole_0(B,A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_xboole_1)).

tff(f_386,axiom,(
    ! [A,B] : k3_xboole_0(A,k2_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_xboole_1)).

tff(f_410,axiom,(
    ! [A,B,C] : r1_tarski(k3_xboole_0(A,B),k2_xboole_0(A,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_xboole_1)).

tff(f_666,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_143,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT001+2.ax',symmetry_r1_xboole_0)).

tff(f_687,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_61,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT001+2.ax',commutativity_k2_xboole_0)).

tff(f_408,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_388,axiom,(
    ! [A,B] : k2_xboole_0(A,k3_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_xboole_1)).

tff(f_614,axiom,(
    ! [A,B,C] :
      ( ~ ( ~ r1_xboole_0(A,k2_xboole_0(B,C))
          & r1_xboole_0(A,B)
          & r1_xboole_0(A,C) )
      & ~ ( ~ ( r1_xboole_0(A,B)
              & r1_xboole_0(A,C) )
          & r1_xboole_0(A,k2_xboole_0(B,C)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_xboole_1)).

tff(c_8,plain,(
    ! [B_8,A_7] : k3_xboole_0(B_8,A_7) = k3_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_112,plain,(
    v1_xboole_0('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_541,plain,(
    ! [A_392] :
      ( k1_xboole_0 = A_392
      | ~ v1_xboole_0(A_392) ) ),
    inference(cnfTransformation,[status(thm)],[f_596])).

tff(c_550,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(resolution,[status(thm)],[c_112,c_541])).

tff(c_82,plain,(
    ! [A_40,B_41] :
      ( r1_xboole_0(A_40,B_41)
      | k3_xboole_0(A_40,B_41) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_7563,plain,(
    ! [A_716,B_717] :
      ( r1_xboole_0(A_716,B_717)
      | k3_xboole_0(A_716,B_717) != '#skF_9' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_550,c_82])).

tff(c_242,plain,
    ( ~ r1_xboole_0('#skF_19','#skF_21')
    | ~ r1_tarski('#skF_19','#skF_20') ),
    inference(cnfTransformation,[status(thm)],[f_314])).

tff(c_578,plain,(
    ~ r1_tarski('#skF_19','#skF_20') ),
    inference(splitLeft,[status(thm)],[c_242])).

tff(c_314,plain,(
    ! [A_200,B_201] : r1_tarski(k4_xboole_0(A_200,B_201),A_200) ),
    inference(cnfTransformation,[status(thm)],[f_440])).

tff(c_322,plain,(
    ! [A_206,B_207] : k2_xboole_0(A_206,k4_xboole_0(B_207,A_206)) = k2_xboole_0(A_206,B_207) ),
    inference(cnfTransformation,[status(thm)],[f_450])).

tff(c_338,plain,(
    ! [A_224,B_225] :
      ( k2_xboole_0(A_224,k4_xboole_0(B_225,A_224)) = B_225
      | ~ r1_tarski(A_224,B_225) ) ),
    inference(cnfTransformation,[status(thm)],[f_474])).

tff(c_1845,plain,(
    ! [A_488,B_489] :
      ( k2_xboole_0(A_488,B_489) = B_489
      | ~ r1_tarski(A_488,B_489) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_322,c_338])).

tff(c_1877,plain,(
    ! [A_200,B_201] : k2_xboole_0(k4_xboole_0(A_200,B_201),A_200) = A_200 ),
    inference(resolution,[status(thm)],[c_314,c_1845])).

tff(c_244,plain,(
    r1_tarski('#skF_19',k4_xboole_0('#skF_20','#skF_21')) ),
    inference(cnfTransformation,[status(thm)],[f_314])).

tff(c_1883,plain,(
    k2_xboole_0('#skF_19',k4_xboole_0('#skF_20','#skF_21')) = k4_xboole_0('#skF_20','#skF_21') ),
    inference(resolution,[status(thm)],[c_244,c_1845])).

tff(c_280,plain,(
    ! [A_155,B_156] : k3_xboole_0(A_155,k2_xboole_0(A_155,B_156)) = A_155 ),
    inference(cnfTransformation,[status(thm)],[f_386])).

tff(c_2187,plain,(
    k3_xboole_0('#skF_19',k4_xboole_0('#skF_20','#skF_21')) = '#skF_19' ),
    inference(superposition,[status(thm),theory(equality)],[c_1883,c_280])).

tff(c_1651,plain,(
    ! [A_478,B_479,C_480] : r1_tarski(k3_xboole_0(A_478,B_479),k2_xboole_0(A_478,C_480)) ),
    inference(cnfTransformation,[status(thm)],[f_410])).

tff(c_4513,plain,(
    ! [B_568,A_569,C_570] : r1_tarski(k3_xboole_0(B_568,A_569),k2_xboole_0(A_569,C_570)) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_1651])).

tff(c_4880,plain,(
    ! [C_583] : r1_tarski('#skF_19',k2_xboole_0(k4_xboole_0('#skF_20','#skF_21'),C_583)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2187,c_4513])).

tff(c_4902,plain,(
    r1_tarski('#skF_19','#skF_20') ),
    inference(superposition,[status(thm),theory(equality)],[c_1877,c_4880])).

tff(c_4934,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_578,c_4902])).

tff(c_4935,plain,(
    ~ r1_xboole_0('#skF_19','#skF_21') ),
    inference(splitRight,[status(thm)],[c_242])).

tff(c_7575,plain,(
    k3_xboole_0('#skF_19','#skF_21') != '#skF_9' ),
    inference(resolution,[status(thm)],[c_7563,c_4935])).

tff(c_7581,plain,(
    k3_xboole_0('#skF_21','#skF_19') != '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_7575])).

tff(c_424,plain,(
    ! [A_321,B_322] : r1_xboole_0(k4_xboole_0(A_321,B_322),B_322) ),
    inference(cnfTransformation,[status(thm)],[f_666])).

tff(c_5567,plain,(
    ! [B_648,A_649] :
      ( r1_xboole_0(B_648,A_649)
      | ~ r1_xboole_0(A_649,B_648) ) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_5576,plain,(
    ! [B_322,A_321] : r1_xboole_0(B_322,k4_xboole_0(A_321,B_322)) ),
    inference(resolution,[status(thm)],[c_424,c_5567])).

tff(c_7831,plain,(
    ! [A_720,B_721] :
      ( k4_xboole_0(A_720,B_721) = A_720
      | ~ r1_xboole_0(A_720,B_721) ) ),
    inference(cnfTransformation,[status(thm)],[f_687])).

tff(c_7856,plain,(
    ! [B_322,A_321] : k4_xboole_0(B_322,k4_xboole_0(A_321,B_322)) = B_322 ),
    inference(resolution,[status(thm)],[c_5576,c_7831])).

tff(c_6,plain,(
    ! [B_6,A_5] : k2_xboole_0(B_6,A_5) = k2_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_6826,plain,(
    ! [A_700,B_701] :
      ( k3_xboole_0(A_700,B_701) = A_700
      | ~ r1_tarski(A_700,B_701) ) ),
    inference(cnfTransformation,[status(thm)],[f_408])).

tff(c_6870,plain,(
    k3_xboole_0('#skF_19',k4_xboole_0('#skF_20','#skF_21')) = '#skF_19' ),
    inference(resolution,[status(thm)],[c_244,c_6826])).

tff(c_5483,plain,(
    ! [B_646,A_647] : k3_xboole_0(B_646,A_647) = k3_xboole_0(A_647,B_646) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_282,plain,(
    ! [A_157,B_158] : k2_xboole_0(A_157,k3_xboole_0(A_157,B_158)) = A_157 ),
    inference(cnfTransformation,[status(thm)],[f_388])).

tff(c_5498,plain,(
    ! [A_647,B_646] : k2_xboole_0(A_647,k3_xboole_0(B_646,A_647)) = A_647 ),
    inference(superposition,[status(thm),theory(equality)],[c_5483,c_282])).

tff(c_6980,plain,(
    k2_xboole_0(k4_xboole_0('#skF_20','#skF_21'),'#skF_19') = k4_xboole_0('#skF_20','#skF_21') ),
    inference(superposition,[status(thm),theory(equality)],[c_6870,c_5498])).

tff(c_7260,plain,(
    k2_xboole_0('#skF_19',k4_xboole_0('#skF_20','#skF_21')) = k4_xboole_0('#skF_20','#skF_21') ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_6980])).

tff(c_11692,plain,(
    ! [A_796,B_797,C_798] :
      ( r1_xboole_0(A_796,B_797)
      | ~ r1_xboole_0(A_796,k2_xboole_0(B_797,C_798)) ) ),
    inference(cnfTransformation,[status(thm)],[f_614])).

tff(c_13780,plain,(
    ! [A_837,B_838,C_839] : r1_xboole_0(k4_xboole_0(A_837,k2_xboole_0(B_838,C_839)),B_838) ),
    inference(resolution,[status(thm)],[c_424,c_11692])).

tff(c_13917,plain,(
    ! [A_840] : r1_xboole_0(k4_xboole_0(A_840,k4_xboole_0('#skF_20','#skF_21')),'#skF_19') ),
    inference(superposition,[status(thm),theory(equality)],[c_7260,c_13780])).

tff(c_13952,plain,(
    r1_xboole_0('#skF_21','#skF_19') ),
    inference(superposition,[status(thm),theory(equality)],[c_7856,c_13917])).

tff(c_80,plain,(
    ! [A_40,B_41] :
      ( k3_xboole_0(A_40,B_41) = k1_xboole_0
      | ~ r1_xboole_0(A_40,B_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_6173,plain,(
    ! [A_40,B_41] :
      ( k3_xboole_0(A_40,B_41) = '#skF_9'
      | ~ r1_xboole_0(A_40,B_41) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_550,c_80])).

tff(c_13985,plain,(
    k3_xboole_0('#skF_21','#skF_19') = '#skF_9' ),
    inference(resolution,[status(thm)],[c_13952,c_6173])).

tff(c_13992,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_7581,c_13985])).
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:04 EST 2020

% Result     : Theorem 3.72s
% Output     : CNFRefutation 3.72s
% Verified   : 
% Statistics : Number of formulae       :  105 ( 302 expanded)
%              Number of leaves         :   30 ( 107 expanded)
%              Depth                    :   13
%              Number of atoms          :  136 ( 634 expanded)
%              Number of equality atoms :   91 ( 508 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_96,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( k1_tarski(A) = k2_xboole_0(B,C)
          & ~ ( B = k1_tarski(A)
              & C = k1_tarski(A) )
          & ~ ( B = k1_xboole_0
              & C = k1_tarski(A) )
          & ~ ( B = k1_tarski(A)
              & C = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_zfmisc_1)).

tff(f_61,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_75,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(f_63,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_77,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_41,axiom,(
    ! [A,B] : k3_xboole_0(A,k2_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ( ~ ( ~ r1_xboole_0(A,k2_xboole_0(B,C))
          & r1_xboole_0(A,B)
          & r1_xboole_0(A,C) )
      & ~ ( ~ ( r1_xboole_0(A,B)
              & r1_xboole_0(A,C) )
          & r1_xboole_0(A,k2_xboole_0(B,C)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_xboole_1)).

tff(f_43,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_39,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(c_44,plain,
    ( k1_tarski('#skF_1') != '#skF_3'
    | k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_78,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_44])).

tff(c_42,plain,
    ( k1_xboole_0 != '#skF_3'
    | k1_tarski('#skF_1') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_59,plain,(
    k1_tarski('#skF_1') != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_42])).

tff(c_48,plain,(
    k2_xboole_0('#skF_2','#skF_3') = k1_tarski('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_74,plain,(
    ! [A_33,B_34] : r1_tarski(A_33,k2_xboole_0(A_33,B_34)) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_77,plain,(
    r1_tarski('#skF_2',k1_tarski('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_74])).

tff(c_806,plain,(
    ! [B_86,A_87] :
      ( k1_tarski(B_86) = A_87
      | k1_xboole_0 = A_87
      | ~ r1_tarski(A_87,k1_tarski(B_86)) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_816,plain,
    ( k1_tarski('#skF_1') = '#skF_2'
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_77,c_806])).

tff(c_828,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_59,c_816])).

tff(c_829,plain,(
    k1_tarski('#skF_1') != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_26,plain,(
    ! [B_18,A_17] : k2_tarski(B_18,A_17) = k2_tarski(A_17,B_18) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_1004,plain,(
    ! [A_112,B_113] : k3_tarski(k2_tarski(A_112,B_113)) = k2_xboole_0(A_112,B_113) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_1194,plain,(
    ! [A_127,B_128] : k3_tarski(k2_tarski(A_127,B_128)) = k2_xboole_0(B_128,A_127) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_1004])).

tff(c_40,plain,(
    ! [A_27,B_28] : k3_tarski(k2_tarski(A_27,B_28)) = k2_xboole_0(A_27,B_28) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_1242,plain,(
    ! [B_130,A_131] : k2_xboole_0(B_130,A_131) = k2_xboole_0(A_131,B_130) ),
    inference(superposition,[status(thm),theory(equality)],[c_1194,c_40])).

tff(c_1284,plain,(
    k2_xboole_0('#skF_3','#skF_2') = k1_tarski('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_1242,c_48])).

tff(c_14,plain,(
    ! [A_9,B_10] : k3_xboole_0(A_9,k2_xboole_0(A_9,B_10)) = A_9 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_1390,plain,(
    k3_xboole_0('#skF_3',k1_tarski('#skF_1')) = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_1284,c_14])).

tff(c_830,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( r1_xboole_0(A_1,B_2)
      | k3_xboole_0(A_1,B_2) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_998,plain,(
    ! [A_1,B_2] :
      ( r1_xboole_0(A_1,B_2)
      | k3_xboole_0(A_1,B_2) != '#skF_2' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_830,c_4])).

tff(c_1169,plain,(
    ! [A_123,C_124,B_125] :
      ( r1_xboole_0(A_123,C_124)
      | ~ r1_xboole_0(A_123,k2_xboole_0(B_125,C_124)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_1188,plain,(
    ! [A_126] :
      ( r1_xboole_0(A_126,'#skF_3')
      | ~ r1_xboole_0(A_126,k1_tarski('#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_1169])).

tff(c_1193,plain,(
    ! [A_1] :
      ( r1_xboole_0(A_1,'#skF_3')
      | k3_xboole_0(A_1,k1_tarski('#skF_1')) != '#skF_2' ) ),
    inference(resolution,[status(thm)],[c_998,c_1188])).

tff(c_1406,plain,
    ( r1_xboole_0('#skF_3','#skF_3')
    | '#skF_2' != '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_1390,c_1193])).

tff(c_1428,plain,(
    '#skF_2' != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_1406])).

tff(c_24,plain,(
    ! [A_15,B_16] : r1_tarski(A_15,k2_xboole_0(A_15,B_16)) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_1311,plain,(
    ! [A_132,B_133] : r1_tarski(A_132,k2_xboole_0(B_133,A_132)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1242,c_24])).

tff(c_1335,plain,(
    r1_tarski('#skF_3',k1_tarski('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_1311])).

tff(c_34,plain,(
    ! [B_26,A_25] :
      ( k1_tarski(B_26) = A_25
      | k1_xboole_0 = A_25
      | ~ r1_tarski(A_25,k1_tarski(B_26)) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_1531,plain,(
    ! [B_145,A_146] :
      ( k1_tarski(B_145) = A_146
      | A_146 = '#skF_2'
      | ~ r1_tarski(A_146,k1_tarski(B_145)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_830,c_34])).

tff(c_1534,plain,
    ( k1_tarski('#skF_1') = '#skF_3'
    | '#skF_2' = '#skF_3' ),
    inference(resolution,[status(thm)],[c_1335,c_1531])).

tff(c_1548,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1428,c_829,c_1534])).

tff(c_1550,plain,(
    '#skF_2' = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_1406])).

tff(c_16,plain,(
    ! [A_11] : k5_xboole_0(A_11,k1_xboole_0) = A_11 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_831,plain,(
    ! [A_11] : k5_xboole_0(A_11,'#skF_2') = A_11 ),
    inference(demodulation,[status(thm),theory(equality)],[c_830,c_16])).

tff(c_38,plain,(
    ! [B_26] : r1_tarski(k1_xboole_0,k1_tarski(B_26)) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_832,plain,(
    ! [B_26] : r1_tarski('#skF_2',k1_tarski(B_26)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_830,c_38])).

tff(c_897,plain,(
    ! [A_94,B_95] :
      ( k2_xboole_0(A_94,B_95) = B_95
      | ~ r1_tarski(A_94,B_95) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_919,plain,(
    ! [B_98] : k2_xboole_0('#skF_2',k1_tarski(B_98)) = k1_tarski(B_98) ),
    inference(resolution,[status(thm)],[c_832,c_897])).

tff(c_925,plain,(
    ! [B_98] : k3_xboole_0('#skF_2',k1_tarski(B_98)) = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_919,c_14])).

tff(c_1220,plain,(
    ! [A_129] :
      ( r1_xboole_0(A_129,'#skF_3')
      | k3_xboole_0(A_129,k1_tarski('#skF_1')) != '#skF_2' ) ),
    inference(resolution,[status(thm)],[c_998,c_1188])).

tff(c_1225,plain,(
    r1_xboole_0('#skF_2','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_925,c_1220])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( k3_xboole_0(A_1,B_2) = k1_xboole_0
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_943,plain,(
    ! [A_1,B_2] :
      ( k3_xboole_0(A_1,B_2) = '#skF_2'
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_830,c_2])).

tff(c_1229,plain,(
    k3_xboole_0('#skF_2','#skF_3') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_1225,c_943])).

tff(c_10,plain,(
    ! [A_5,B_6] : k5_xboole_0(A_5,k3_xboole_0(A_5,B_6)) = k4_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_1233,plain,(
    k5_xboole_0('#skF_2','#skF_2') = k4_xboole_0('#skF_2','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1229,c_10])).

tff(c_1236,plain,(
    k4_xboole_0('#skF_2','#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_831,c_1233])).

tff(c_1553,plain,(
    k4_xboole_0('#skF_3','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1550,c_1550,c_1236])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( r1_tarski(A_3,B_4)
      | k4_xboole_0(A_3,B_4) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_989,plain,(
    ! [A_108,B_109] :
      ( r1_tarski(A_108,B_109)
      | k4_xboole_0(A_108,B_109) != '#skF_2' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_830,c_6])).

tff(c_12,plain,(
    ! [A_7,B_8] :
      ( k2_xboole_0(A_7,B_8) = B_8
      | ~ r1_tarski(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_997,plain,(
    ! [A_108,B_109] :
      ( k2_xboole_0(A_108,B_109) = B_109
      | k4_xboole_0(A_108,B_109) != '#skF_2' ) ),
    inference(resolution,[status(thm)],[c_989,c_12])).

tff(c_2128,plain,(
    ! [A_176,B_177] :
      ( k2_xboole_0(A_176,B_177) = B_177
      | k4_xboole_0(A_176,B_177) != '#skF_3' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1550,c_997])).

tff(c_2155,plain,(
    k2_xboole_0('#skF_3','#skF_3') = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_1553,c_2128])).

tff(c_1571,plain,(
    k2_xboole_0('#skF_3','#skF_3') = k1_tarski('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1550,c_48])).

tff(c_2156,plain,(
    k1_tarski('#skF_1') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2155,c_1571])).

tff(c_2158,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_829,c_2156])).

tff(c_2159,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_2160,plain,(
    k1_tarski('#skF_1') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_46,plain,
    ( k1_tarski('#skF_1') != '#skF_3'
    | k1_tarski('#skF_1') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_2199,plain,(
    '#skF_2' != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2160,c_2160,c_46])).

tff(c_2167,plain,(
    k2_xboole_0('#skF_2','#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2160,c_48])).

tff(c_2249,plain,(
    ! [A_186,B_187] : k3_tarski(k2_tarski(A_186,B_187)) = k2_xboole_0(A_186,B_187) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_2610,plain,(
    ! [A_212,B_213] : k3_tarski(k2_tarski(A_212,B_213)) = k2_xboole_0(B_213,A_212) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_2249])).

tff(c_2636,plain,(
    ! [B_214,A_215] : k2_xboole_0(B_214,A_215) = k2_xboole_0(A_215,B_214) ),
    inference(superposition,[status(thm),theory(equality)],[c_2610,c_40])).

tff(c_2702,plain,(
    k2_xboole_0('#skF_3','#skF_2') = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_2167,c_2636])).

tff(c_2775,plain,(
    r1_tarski('#skF_3','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_2702,c_24])).

tff(c_2981,plain,(
    ! [B_227,A_228] :
      ( k1_tarski(B_227) = A_228
      | k1_xboole_0 = A_228
      | ~ r1_tarski(A_228,k1_tarski(B_227)) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_2991,plain,(
    ! [A_228] :
      ( k1_tarski('#skF_1') = A_228
      | k1_xboole_0 = A_228
      | ~ r1_tarski(A_228,'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2160,c_2981])).

tff(c_3182,plain,(
    ! [A_237] :
      ( A_237 = '#skF_2'
      | k1_xboole_0 = A_237
      | ~ r1_tarski(A_237,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2160,c_2991])).

tff(c_3185,plain,
    ( '#skF_2' = '#skF_3'
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_2775,c_3182])).

tff(c_3199,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2159,c_2199,c_3185])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:17:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.72/1.65  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.72/1.66  
% 3.72/1.66  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.72/1.66  %$ r1_xboole_0 > r1_tarski > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 3.72/1.66  
% 3.72/1.66  %Foreground sorts:
% 3.72/1.66  
% 3.72/1.66  
% 3.72/1.66  %Background operators:
% 3.72/1.66  
% 3.72/1.66  
% 3.72/1.66  %Foreground operators:
% 3.72/1.66  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.72/1.66  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.72/1.66  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.72/1.66  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.72/1.66  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.72/1.66  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.72/1.66  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.72/1.66  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.72/1.66  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.72/1.66  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.72/1.66  tff('#skF_2', type, '#skF_2': $i).
% 3.72/1.66  tff('#skF_3', type, '#skF_3': $i).
% 3.72/1.66  tff('#skF_1', type, '#skF_1': $i).
% 3.72/1.66  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.72/1.66  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.72/1.66  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.72/1.66  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.72/1.66  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.72/1.66  
% 3.72/1.68  tff(f_96, negated_conjecture, ~(![A, B, C]: ~((((k1_tarski(A) = k2_xboole_0(B, C)) & ~((B = k1_tarski(A)) & (C = k1_tarski(A)))) & ~((B = k1_xboole_0) & (C = k1_tarski(A)))) & ~((B = k1_tarski(A)) & (C = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_zfmisc_1)).
% 3.72/1.68  tff(f_61, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 3.72/1.68  tff(f_75, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 3.72/1.68  tff(f_63, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 3.72/1.68  tff(f_77, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 3.72/1.68  tff(f_41, axiom, (![A, B]: (k3_xboole_0(A, k2_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_xboole_1)).
% 3.72/1.68  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 3.72/1.68  tff(f_59, axiom, (![A, B, C]: (~((~r1_xboole_0(A, k2_xboole_0(B, C)) & r1_xboole_0(A, B)) & r1_xboole_0(A, C)) & ~(~(r1_xboole_0(A, B) & r1_xboole_0(A, C)) & r1_xboole_0(A, k2_xboole_0(B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_xboole_1)).
% 3.72/1.68  tff(f_43, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 3.72/1.68  tff(f_39, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 3.72/1.68  tff(f_35, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.72/1.68  tff(f_33, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 3.72/1.68  tff(c_44, plain, (k1_tarski('#skF_1')!='#skF_3' | k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.72/1.68  tff(c_78, plain, (k1_xboole_0!='#skF_2'), inference(splitLeft, [status(thm)], [c_44])).
% 3.72/1.68  tff(c_42, plain, (k1_xboole_0!='#skF_3' | k1_tarski('#skF_1')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.72/1.68  tff(c_59, plain, (k1_tarski('#skF_1')!='#skF_2'), inference(splitLeft, [status(thm)], [c_42])).
% 3.72/1.68  tff(c_48, plain, (k2_xboole_0('#skF_2', '#skF_3')=k1_tarski('#skF_1')), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.72/1.68  tff(c_74, plain, (![A_33, B_34]: (r1_tarski(A_33, k2_xboole_0(A_33, B_34)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.72/1.68  tff(c_77, plain, (r1_tarski('#skF_2', k1_tarski('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_48, c_74])).
% 3.72/1.68  tff(c_806, plain, (![B_86, A_87]: (k1_tarski(B_86)=A_87 | k1_xboole_0=A_87 | ~r1_tarski(A_87, k1_tarski(B_86)))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.72/1.68  tff(c_816, plain, (k1_tarski('#skF_1')='#skF_2' | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_77, c_806])).
% 3.72/1.68  tff(c_828, plain, $false, inference(negUnitSimplification, [status(thm)], [c_78, c_59, c_816])).
% 3.72/1.68  tff(c_829, plain, (k1_tarski('#skF_1')!='#skF_3'), inference(splitRight, [status(thm)], [c_44])).
% 3.72/1.68  tff(c_26, plain, (![B_18, A_17]: (k2_tarski(B_18, A_17)=k2_tarski(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.72/1.68  tff(c_1004, plain, (![A_112, B_113]: (k3_tarski(k2_tarski(A_112, B_113))=k2_xboole_0(A_112, B_113))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.72/1.68  tff(c_1194, plain, (![A_127, B_128]: (k3_tarski(k2_tarski(A_127, B_128))=k2_xboole_0(B_128, A_127))), inference(superposition, [status(thm), theory('equality')], [c_26, c_1004])).
% 3.72/1.68  tff(c_40, plain, (![A_27, B_28]: (k3_tarski(k2_tarski(A_27, B_28))=k2_xboole_0(A_27, B_28))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.72/1.68  tff(c_1242, plain, (![B_130, A_131]: (k2_xboole_0(B_130, A_131)=k2_xboole_0(A_131, B_130))), inference(superposition, [status(thm), theory('equality')], [c_1194, c_40])).
% 3.72/1.68  tff(c_1284, plain, (k2_xboole_0('#skF_3', '#skF_2')=k1_tarski('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_1242, c_48])).
% 3.72/1.68  tff(c_14, plain, (![A_9, B_10]: (k3_xboole_0(A_9, k2_xboole_0(A_9, B_10))=A_9)), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.72/1.68  tff(c_1390, plain, (k3_xboole_0('#skF_3', k1_tarski('#skF_1'))='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_1284, c_14])).
% 3.72/1.68  tff(c_830, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_44])).
% 3.72/1.68  tff(c_4, plain, (![A_1, B_2]: (r1_xboole_0(A_1, B_2) | k3_xboole_0(A_1, B_2)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.72/1.68  tff(c_998, plain, (![A_1, B_2]: (r1_xboole_0(A_1, B_2) | k3_xboole_0(A_1, B_2)!='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_830, c_4])).
% 3.72/1.68  tff(c_1169, plain, (![A_123, C_124, B_125]: (r1_xboole_0(A_123, C_124) | ~r1_xboole_0(A_123, k2_xboole_0(B_125, C_124)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.72/1.68  tff(c_1188, plain, (![A_126]: (r1_xboole_0(A_126, '#skF_3') | ~r1_xboole_0(A_126, k1_tarski('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_48, c_1169])).
% 3.72/1.68  tff(c_1193, plain, (![A_1]: (r1_xboole_0(A_1, '#skF_3') | k3_xboole_0(A_1, k1_tarski('#skF_1'))!='#skF_2')), inference(resolution, [status(thm)], [c_998, c_1188])).
% 3.72/1.68  tff(c_1406, plain, (r1_xboole_0('#skF_3', '#skF_3') | '#skF_2'!='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_1390, c_1193])).
% 3.72/1.68  tff(c_1428, plain, ('#skF_2'!='#skF_3'), inference(splitLeft, [status(thm)], [c_1406])).
% 3.72/1.68  tff(c_24, plain, (![A_15, B_16]: (r1_tarski(A_15, k2_xboole_0(A_15, B_16)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.72/1.68  tff(c_1311, plain, (![A_132, B_133]: (r1_tarski(A_132, k2_xboole_0(B_133, A_132)))), inference(superposition, [status(thm), theory('equality')], [c_1242, c_24])).
% 3.72/1.68  tff(c_1335, plain, (r1_tarski('#skF_3', k1_tarski('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_48, c_1311])).
% 3.72/1.68  tff(c_34, plain, (![B_26, A_25]: (k1_tarski(B_26)=A_25 | k1_xboole_0=A_25 | ~r1_tarski(A_25, k1_tarski(B_26)))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.72/1.68  tff(c_1531, plain, (![B_145, A_146]: (k1_tarski(B_145)=A_146 | A_146='#skF_2' | ~r1_tarski(A_146, k1_tarski(B_145)))), inference(demodulation, [status(thm), theory('equality')], [c_830, c_34])).
% 3.72/1.68  tff(c_1534, plain, (k1_tarski('#skF_1')='#skF_3' | '#skF_2'='#skF_3'), inference(resolution, [status(thm)], [c_1335, c_1531])).
% 3.72/1.68  tff(c_1548, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1428, c_829, c_1534])).
% 3.72/1.68  tff(c_1550, plain, ('#skF_2'='#skF_3'), inference(splitRight, [status(thm)], [c_1406])).
% 3.72/1.68  tff(c_16, plain, (![A_11]: (k5_xboole_0(A_11, k1_xboole_0)=A_11)), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.72/1.68  tff(c_831, plain, (![A_11]: (k5_xboole_0(A_11, '#skF_2')=A_11)), inference(demodulation, [status(thm), theory('equality')], [c_830, c_16])).
% 3.72/1.68  tff(c_38, plain, (![B_26]: (r1_tarski(k1_xboole_0, k1_tarski(B_26)))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.72/1.68  tff(c_832, plain, (![B_26]: (r1_tarski('#skF_2', k1_tarski(B_26)))), inference(demodulation, [status(thm), theory('equality')], [c_830, c_38])).
% 3.72/1.68  tff(c_897, plain, (![A_94, B_95]: (k2_xboole_0(A_94, B_95)=B_95 | ~r1_tarski(A_94, B_95))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.72/1.68  tff(c_919, plain, (![B_98]: (k2_xboole_0('#skF_2', k1_tarski(B_98))=k1_tarski(B_98))), inference(resolution, [status(thm)], [c_832, c_897])).
% 3.72/1.68  tff(c_925, plain, (![B_98]: (k3_xboole_0('#skF_2', k1_tarski(B_98))='#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_919, c_14])).
% 3.72/1.68  tff(c_1220, plain, (![A_129]: (r1_xboole_0(A_129, '#skF_3') | k3_xboole_0(A_129, k1_tarski('#skF_1'))!='#skF_2')), inference(resolution, [status(thm)], [c_998, c_1188])).
% 3.72/1.68  tff(c_1225, plain, (r1_xboole_0('#skF_2', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_925, c_1220])).
% 3.72/1.68  tff(c_2, plain, (![A_1, B_2]: (k3_xboole_0(A_1, B_2)=k1_xboole_0 | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.72/1.68  tff(c_943, plain, (![A_1, B_2]: (k3_xboole_0(A_1, B_2)='#skF_2' | ~r1_xboole_0(A_1, B_2))), inference(demodulation, [status(thm), theory('equality')], [c_830, c_2])).
% 3.72/1.68  tff(c_1229, plain, (k3_xboole_0('#skF_2', '#skF_3')='#skF_2'), inference(resolution, [status(thm)], [c_1225, c_943])).
% 3.72/1.68  tff(c_10, plain, (![A_5, B_6]: (k5_xboole_0(A_5, k3_xboole_0(A_5, B_6))=k4_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.72/1.68  tff(c_1233, plain, (k5_xboole_0('#skF_2', '#skF_2')=k4_xboole_0('#skF_2', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1229, c_10])).
% 3.72/1.68  tff(c_1236, plain, (k4_xboole_0('#skF_2', '#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_831, c_1233])).
% 3.72/1.68  tff(c_1553, plain, (k4_xboole_0('#skF_3', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1550, c_1550, c_1236])).
% 3.72/1.68  tff(c_6, plain, (![A_3, B_4]: (r1_tarski(A_3, B_4) | k4_xboole_0(A_3, B_4)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.72/1.68  tff(c_989, plain, (![A_108, B_109]: (r1_tarski(A_108, B_109) | k4_xboole_0(A_108, B_109)!='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_830, c_6])).
% 3.72/1.68  tff(c_12, plain, (![A_7, B_8]: (k2_xboole_0(A_7, B_8)=B_8 | ~r1_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.72/1.68  tff(c_997, plain, (![A_108, B_109]: (k2_xboole_0(A_108, B_109)=B_109 | k4_xboole_0(A_108, B_109)!='#skF_2')), inference(resolution, [status(thm)], [c_989, c_12])).
% 3.72/1.68  tff(c_2128, plain, (![A_176, B_177]: (k2_xboole_0(A_176, B_177)=B_177 | k4_xboole_0(A_176, B_177)!='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1550, c_997])).
% 3.72/1.68  tff(c_2155, plain, (k2_xboole_0('#skF_3', '#skF_3')='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_1553, c_2128])).
% 3.72/1.68  tff(c_1571, plain, (k2_xboole_0('#skF_3', '#skF_3')=k1_tarski('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1550, c_48])).
% 3.72/1.68  tff(c_2156, plain, (k1_tarski('#skF_1')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_2155, c_1571])).
% 3.72/1.68  tff(c_2158, plain, $false, inference(negUnitSimplification, [status(thm)], [c_829, c_2156])).
% 3.72/1.68  tff(c_2159, plain, (k1_xboole_0!='#skF_3'), inference(splitRight, [status(thm)], [c_42])).
% 3.72/1.68  tff(c_2160, plain, (k1_tarski('#skF_1')='#skF_2'), inference(splitRight, [status(thm)], [c_42])).
% 3.72/1.68  tff(c_46, plain, (k1_tarski('#skF_1')!='#skF_3' | k1_tarski('#skF_1')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.72/1.68  tff(c_2199, plain, ('#skF_2'!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_2160, c_2160, c_46])).
% 3.72/1.68  tff(c_2167, plain, (k2_xboole_0('#skF_2', '#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_2160, c_48])).
% 3.72/1.68  tff(c_2249, plain, (![A_186, B_187]: (k3_tarski(k2_tarski(A_186, B_187))=k2_xboole_0(A_186, B_187))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.72/1.68  tff(c_2610, plain, (![A_212, B_213]: (k3_tarski(k2_tarski(A_212, B_213))=k2_xboole_0(B_213, A_212))), inference(superposition, [status(thm), theory('equality')], [c_26, c_2249])).
% 3.72/1.68  tff(c_2636, plain, (![B_214, A_215]: (k2_xboole_0(B_214, A_215)=k2_xboole_0(A_215, B_214))), inference(superposition, [status(thm), theory('equality')], [c_2610, c_40])).
% 3.72/1.68  tff(c_2702, plain, (k2_xboole_0('#skF_3', '#skF_2')='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_2167, c_2636])).
% 3.72/1.68  tff(c_2775, plain, (r1_tarski('#skF_3', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_2702, c_24])).
% 3.72/1.68  tff(c_2981, plain, (![B_227, A_228]: (k1_tarski(B_227)=A_228 | k1_xboole_0=A_228 | ~r1_tarski(A_228, k1_tarski(B_227)))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.72/1.68  tff(c_2991, plain, (![A_228]: (k1_tarski('#skF_1')=A_228 | k1_xboole_0=A_228 | ~r1_tarski(A_228, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_2160, c_2981])).
% 3.72/1.68  tff(c_3182, plain, (![A_237]: (A_237='#skF_2' | k1_xboole_0=A_237 | ~r1_tarski(A_237, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_2160, c_2991])).
% 3.72/1.68  tff(c_3185, plain, ('#skF_2'='#skF_3' | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_2775, c_3182])).
% 3.72/1.68  tff(c_3199, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2159, c_2199, c_3185])).
% 3.72/1.68  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.72/1.68  
% 3.72/1.68  Inference rules
% 3.72/1.68  ----------------------
% 3.72/1.68  #Ref     : 0
% 3.72/1.68  #Sup     : 825
% 3.72/1.68  #Fact    : 0
% 3.72/1.68  #Define  : 0
% 3.72/1.68  #Split   : 4
% 3.72/1.68  #Chain   : 0
% 3.72/1.68  #Close   : 0
% 3.72/1.68  
% 3.72/1.68  Ordering : KBO
% 3.72/1.68  
% 3.72/1.68  Simplification rules
% 3.72/1.68  ----------------------
% 3.72/1.68  #Subsume      : 28
% 3.72/1.68  #Demod        : 364
% 3.72/1.68  #Tautology    : 609
% 3.72/1.68  #SimpNegUnit  : 4
% 3.72/1.68  #BackRed      : 25
% 3.72/1.68  
% 3.72/1.68  #Partial instantiations: 0
% 3.72/1.68  #Strategies tried      : 1
% 3.72/1.68  
% 3.72/1.68  Timing (in seconds)
% 3.72/1.68  ----------------------
% 3.72/1.68  Preprocessing        : 0.30
% 3.72/1.68  Parsing              : 0.15
% 3.72/1.68  CNF conversion       : 0.02
% 3.72/1.68  Main loop            : 0.61
% 3.72/1.68  Inferencing          : 0.22
% 3.72/1.68  Reduction            : 0.22
% 3.72/1.68  Demodulation         : 0.17
% 3.72/1.68  BG Simplification    : 0.02
% 3.72/1.68  Subsumption          : 0.08
% 3.72/1.68  Abstraction          : 0.03
% 3.72/1.68  MUC search           : 0.00
% 3.72/1.68  Cooper               : 0.00
% 3.72/1.68  Total                : 0.95
% 3.72/1.68  Index Insertion      : 0.00
% 3.72/1.68  Index Deletion       : 0.00
% 3.72/1.68  Index Matching       : 0.00
% 3.72/1.68  BG Taut test         : 0.00
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:53:21 EST 2020

% Result     : Theorem 6.06s
% Output     : CNFRefutation 6.06s
% Verified   : 
% Statistics : Number of formulae       :  183 ( 639 expanded)
%              Number of leaves         :   26 ( 183 expanded)
%              Depth                    :    9
%              Number of atoms          :  256 (1653 expanded)
%              Number of equality atoms :  198 (1556 expanded)
%              Maximal formula depth    :   11 (   2 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_8 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

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

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_93,negated_conjecture,(
    ~ ! [A,B,C] :
        ( k4_xboole_0(A,k2_tarski(B,C)) = k1_xboole_0
      <=> ~ ( A != k1_xboole_0
            & A != k1_tarski(B)
            & A != k1_tarski(C)
            & A != k2_tarski(B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

tff(f_29,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_41,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

tff(f_33,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_xboole_1)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k4_xboole_0(A,B),C)
     => r1_tarski(A,k2_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_xboole_1)).

tff(f_71,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k2_tarski(B,C))
    <=> ~ ( A != k1_xboole_0
          & A != k1_tarski(B)
          & A != k1_tarski(C)
          & A != k2_tarski(B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l45_zfmisc_1)).

tff(f_73,axiom,(
    ! [A,B] : k4_xboole_0(k1_tarski(A),k2_tarski(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_zfmisc_1)).

tff(c_66,plain,
    ( k4_xboole_0('#skF_3',k2_tarski('#skF_4','#skF_5')) != k1_xboole_0
    | k1_xboole_0 != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_114,plain,(
    k1_xboole_0 != '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_66])).

tff(c_62,plain,
    ( k4_xboole_0('#skF_3',k2_tarski('#skF_4','#skF_5')) != k1_xboole_0
    | k1_tarski('#skF_7') != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_303,plain,(
    k1_tarski('#skF_7') != '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_62])).

tff(c_58,plain,
    ( k4_xboole_0('#skF_3',k2_tarski('#skF_4','#skF_5')) != k1_xboole_0
    | k1_tarski('#skF_8') != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_195,plain,(
    k1_tarski('#skF_8') != '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_58])).

tff(c_54,plain,
    ( k4_xboole_0('#skF_3',k2_tarski('#skF_4','#skF_5')) != k1_xboole_0
    | k2_tarski('#skF_7','#skF_8') != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_333,plain,(
    k2_tarski('#skF_7','#skF_8') != '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_54])).

tff(c_2,plain,(
    ! [A_1] : k2_xboole_0(A_1,A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4,plain,(
    ! [A_3] : r1_tarski(k1_xboole_0,A_3) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_14,plain,(
    ! [A_11] : k4_xboole_0(k1_xboole_0,A_11) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_72,plain,
    ( k2_tarski('#skF_4','#skF_5') = '#skF_3'
    | k1_tarski('#skF_5') = '#skF_3'
    | k1_tarski('#skF_4') = '#skF_3'
    | k1_xboole_0 = '#skF_3'
    | k4_xboole_0('#skF_6',k2_tarski('#skF_7','#skF_8')) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_1142,plain,(
    k4_xboole_0('#skF_6',k2_tarski('#skF_7','#skF_8')) = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_72])).

tff(c_6,plain,(
    ! [A_4,B_5] :
      ( r1_tarski(A_4,B_5)
      | k4_xboole_0(A_4,B_5) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_340,plain,(
    ! [A_68,B_69,C_70] :
      ( r1_tarski(A_68,k2_xboole_0(B_69,C_70))
      | ~ r1_tarski(k4_xboole_0(A_68,B_69),C_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_1046,plain,(
    ! [A_146,B_147,B_148] :
      ( r1_tarski(A_146,k2_xboole_0(B_147,B_148))
      | k4_xboole_0(k4_xboole_0(A_146,B_147),B_148) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_6,c_340])).

tff(c_1059,plain,(
    ! [A_146,A_1] :
      ( r1_tarski(A_146,A_1)
      | k4_xboole_0(k4_xboole_0(A_146,A_1),A_1) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_1046])).

tff(c_1146,plain,
    ( r1_tarski('#skF_6',k2_tarski('#skF_7','#skF_8'))
    | k4_xboole_0(k1_xboole_0,k2_tarski('#skF_7','#skF_8')) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1142,c_1059])).

tff(c_1153,plain,(
    r1_tarski('#skF_6',k2_tarski('#skF_7','#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_1146])).

tff(c_1356,plain,(
    ! [B_175,C_176,A_177] :
      ( k2_tarski(B_175,C_176) = A_177
      | k1_tarski(C_176) = A_177
      | k1_tarski(B_175) = A_177
      | k1_xboole_0 = A_177
      | ~ r1_tarski(A_177,k2_tarski(B_175,C_176)) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_1363,plain,
    ( k2_tarski('#skF_7','#skF_8') = '#skF_6'
    | k1_tarski('#skF_8') = '#skF_6'
    | k1_tarski('#skF_7') = '#skF_6'
    | k1_xboole_0 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_1153,c_1356])).

tff(c_1392,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_114,c_303,c_195,c_333,c_1363])).

tff(c_1393,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_tarski('#skF_4') = '#skF_3'
    | k1_tarski('#skF_5') = '#skF_3'
    | k2_tarski('#skF_4','#skF_5') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_72])).

tff(c_1436,plain,(
    k2_tarski('#skF_4','#skF_5') = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_1393])).

tff(c_70,plain,
    ( k4_xboole_0('#skF_3',k2_tarski('#skF_4','#skF_5')) != k1_xboole_0
    | k4_xboole_0('#skF_6',k2_tarski('#skF_7','#skF_8')) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_397,plain,(
    k4_xboole_0('#skF_3',k2_tarski('#skF_4','#skF_5')) != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_70])).

tff(c_1437,plain,(
    k4_xboole_0('#skF_3','#skF_3') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1436,c_397])).

tff(c_40,plain,(
    ! [B_22,C_23] : r1_tarski(k2_tarski(B_22,C_23),k2_tarski(B_22,C_23)) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_1492,plain,(
    r1_tarski('#skF_3',k2_tarski('#skF_4','#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1436,c_40])).

tff(c_1516,plain,(
    r1_tarski('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1436,c_1492])).

tff(c_8,plain,(
    ! [A_4,B_5] :
      ( k4_xboole_0(A_4,B_5) = k1_xboole_0
      | ~ r1_tarski(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_1522,plain,(
    k4_xboole_0('#skF_3','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1516,c_8])).

tff(c_1542,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1437,c_1522])).

tff(c_1543,plain,
    ( k1_tarski('#skF_5') = '#skF_3'
    | k1_tarski('#skF_4') = '#skF_3'
    | k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_1393])).

tff(c_1545,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_1543])).

tff(c_1568,plain,(
    ! [A_11] : k4_xboole_0('#skF_3',A_11) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1545,c_1545,c_14])).

tff(c_1558,plain,(
    k4_xboole_0('#skF_3',k2_tarski('#skF_4','#skF_5')) != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1545,c_397])).

tff(c_1588,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1568,c_1558])).

tff(c_1589,plain,
    ( k1_tarski('#skF_4') = '#skF_3'
    | k1_tarski('#skF_5') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_1543])).

tff(c_1591,plain,(
    k1_tarski('#skF_5') = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_1589])).

tff(c_42,plain,(
    ! [C_23,B_22] : r1_tarski(k1_tarski(C_23),k2_tarski(B_22,C_23)) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_1774,plain,(
    ! [B_188] : r1_tarski('#skF_3',k2_tarski(B_188,'#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1591,c_42])).

tff(c_1782,plain,(
    ! [B_188] : k4_xboole_0('#skF_3',k2_tarski(B_188,'#skF_5')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1774,c_8])).

tff(c_1831,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1782,c_397])).

tff(c_1832,plain,(
    k1_tarski('#skF_4') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_1589])).

tff(c_48,plain,(
    ! [A_24,B_25] : k4_xboole_0(k1_tarski(A_24),k2_tarski(A_24,B_25)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_1938,plain,(
    ! [B_25] : k4_xboole_0('#skF_3',k2_tarski('#skF_4',B_25)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1832,c_48])).

tff(c_2051,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1938,c_397])).

tff(c_2052,plain,(
    k4_xboole_0('#skF_6',k2_tarski('#skF_7','#skF_8')) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_70])).

tff(c_12,plain,(
    ! [A_8,B_9,C_10] :
      ( r1_tarski(A_8,k2_xboole_0(B_9,C_10))
      | ~ r1_tarski(k4_xboole_0(A_8,B_9),C_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_2057,plain,(
    ! [C_10] :
      ( r1_tarski('#skF_6',k2_xboole_0(k2_tarski('#skF_7','#skF_8'),C_10))
      | ~ r1_tarski(k1_xboole_0,C_10) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2052,c_12])).

tff(c_2072,plain,(
    ! [C_199] : r1_tarski('#skF_6',k2_xboole_0(k2_tarski('#skF_7','#skF_8'),C_199)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_2057])).

tff(c_2079,plain,(
    r1_tarski('#skF_6',k2_tarski('#skF_7','#skF_8')) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_2072])).

tff(c_3104,plain,(
    ! [B_301,C_302,A_303] :
      ( k2_tarski(B_301,C_302) = A_303
      | k1_tarski(C_302) = A_303
      | k1_tarski(B_301) = A_303
      | k1_xboole_0 = A_303
      | ~ r1_tarski(A_303,k2_tarski(B_301,C_302)) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_3114,plain,
    ( k2_tarski('#skF_7','#skF_8') = '#skF_6'
    | k1_tarski('#skF_8') = '#skF_6'
    | k1_tarski('#skF_7') = '#skF_6'
    | k1_xboole_0 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_2079,c_3104])).

tff(c_3144,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_114,c_303,c_195,c_333,c_3114])).

tff(c_3145,plain,(
    k4_xboole_0('#skF_3',k2_tarski('#skF_4','#skF_5')) != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_3146,plain,(
    k2_tarski('#skF_7','#skF_8') = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_56,plain,
    ( k2_tarski('#skF_4','#skF_5') = '#skF_3'
    | k1_tarski('#skF_5') = '#skF_3'
    | k1_tarski('#skF_4') = '#skF_3'
    | k1_xboole_0 = '#skF_3'
    | k2_tarski('#skF_7','#skF_8') != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_3469,plain,
    ( k2_tarski('#skF_4','#skF_5') = '#skF_3'
    | k1_tarski('#skF_5') = '#skF_3'
    | k1_tarski('#skF_4') = '#skF_3'
    | k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3146,c_56])).

tff(c_3470,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_3469])).

tff(c_3487,plain,(
    ! [A_11] : k4_xboole_0('#skF_3',A_11) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3470,c_3470,c_14])).

tff(c_3193,plain,
    ( k4_xboole_0('#skF_3',k2_tarski('#skF_4','#skF_5')) != k1_xboole_0
    | k4_xboole_0('#skF_6','#skF_6') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_3146,c_70])).

tff(c_3194,plain,(
    k4_xboole_0('#skF_3',k2_tarski('#skF_4','#skF_5')) != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_3193])).

tff(c_3476,plain,(
    k4_xboole_0('#skF_3',k2_tarski('#skF_4','#skF_5')) != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3470,c_3194])).

tff(c_3516,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3487,c_3476])).

tff(c_3517,plain,
    ( k1_tarski('#skF_4') = '#skF_3'
    | k1_tarski('#skF_5') = '#skF_3'
    | k2_tarski('#skF_4','#skF_5') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_3469])).

tff(c_3635,plain,(
    k2_tarski('#skF_4','#skF_5') = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_3517])).

tff(c_3636,plain,(
    k4_xboole_0('#skF_3','#skF_3') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_3635,c_3194])).

tff(c_3661,plain,(
    r1_tarski('#skF_3',k2_tarski('#skF_4','#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_3635,c_40])).

tff(c_3681,plain,(
    r1_tarski('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3635,c_3661])).

tff(c_3687,plain,(
    k4_xboole_0('#skF_3','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_3681,c_8])).

tff(c_3697,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3636,c_3687])).

tff(c_3698,plain,
    ( k1_tarski('#skF_5') = '#skF_3'
    | k1_tarski('#skF_4') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_3517])).

tff(c_3700,plain,(
    k1_tarski('#skF_4') = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_3698])).

tff(c_3749,plain,(
    ! [B_25] : k4_xboole_0('#skF_3',k2_tarski('#skF_4',B_25)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_3700,c_48])).

tff(c_3833,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3749,c_3194])).

tff(c_3834,plain,(
    k1_tarski('#skF_5') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_3698])).

tff(c_148,plain,(
    ! [A_49,B_50] :
      ( k4_xboole_0(A_49,B_50) = k1_xboole_0
      | ~ r1_tarski(A_49,B_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_169,plain,(
    ! [C_23,B_22] : k4_xboole_0(k1_tarski(C_23),k2_tarski(B_22,C_23)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_42,c_148])).

tff(c_3875,plain,(
    ! [B_22] : k4_xboole_0('#skF_3',k2_tarski(B_22,'#skF_5')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_3834,c_169])).

tff(c_3986,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3875,c_3194])).

tff(c_3988,plain,(
    k4_xboole_0('#skF_3',k2_tarski('#skF_4','#skF_5')) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_3193])).

tff(c_4048,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3145,c_3988])).

tff(c_4050,plain,(
    k1_tarski('#skF_7') = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_64,plain,
    ( k2_tarski('#skF_4','#skF_5') = '#skF_3'
    | k1_tarski('#skF_5') = '#skF_3'
    | k1_tarski('#skF_4') = '#skF_3'
    | k1_xboole_0 = '#skF_3'
    | k1_tarski('#skF_7') != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_4466,plain,
    ( k2_tarski('#skF_4','#skF_5') = '#skF_3'
    | k1_tarski('#skF_5') = '#skF_3'
    | k1_tarski('#skF_4') = '#skF_3'
    | k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4050,c_64])).

tff(c_4467,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_4466])).

tff(c_4486,plain,(
    ! [A_11] : k4_xboole_0('#skF_3',A_11) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4467,c_4467,c_14])).

tff(c_4049,plain,(
    k4_xboole_0('#skF_3',k2_tarski('#skF_4','#skF_5')) != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_4476,plain,(
    k4_xboole_0('#skF_3',k2_tarski('#skF_4','#skF_5')) != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4467,c_4049])).

tff(c_4515,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4486,c_4476])).

tff(c_4516,plain,
    ( k1_tarski('#skF_4') = '#skF_3'
    | k1_tarski('#skF_5') = '#skF_3'
    | k2_tarski('#skF_4','#skF_5') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_4466])).

tff(c_4642,plain,(
    k2_tarski('#skF_4','#skF_5') = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_4516])).

tff(c_4643,plain,(
    k4_xboole_0('#skF_3','#skF_3') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4642,c_4049])).

tff(c_168,plain,(
    ! [B_22,C_23] : k4_xboole_0(k2_tarski(B_22,C_23),k2_tarski(B_22,C_23)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_40,c_148])).

tff(c_4656,plain,(
    k4_xboole_0(k2_tarski('#skF_4','#skF_5'),'#skF_3') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_4642,c_168])).

tff(c_4687,plain,(
    k4_xboole_0('#skF_3','#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4642,c_4656])).

tff(c_4707,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4643,c_4687])).

tff(c_4708,plain,
    ( k1_tarski('#skF_5') = '#skF_3'
    | k1_tarski('#skF_4') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_4516])).

tff(c_4710,plain,(
    k1_tarski('#skF_4') = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_4708])).

tff(c_4754,plain,(
    ! [B_25] : k4_xboole_0('#skF_3',k2_tarski('#skF_4',B_25)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_4710,c_48])).

tff(c_4832,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4754,c_4049])).

tff(c_4833,plain,(
    k1_tarski('#skF_5') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_4708])).

tff(c_4931,plain,(
    ! [B_414] : r1_tarski('#skF_3',k2_tarski(B_414,'#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_4833,c_42])).

tff(c_4939,plain,(
    ! [B_414] : k4_xboole_0('#skF_3',k2_tarski(B_414,'#skF_5')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_4931,c_8])).

tff(c_4974,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4939,c_4049])).

tff(c_4976,plain,(
    k1_tarski('#skF_8') = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_60,plain,
    ( k2_tarski('#skF_4','#skF_5') = '#skF_3'
    | k1_tarski('#skF_5') = '#skF_3'
    | k1_tarski('#skF_4') = '#skF_3'
    | k1_xboole_0 = '#skF_3'
    | k1_tarski('#skF_8') != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_5747,plain,
    ( k2_tarski('#skF_4','#skF_5') = '#skF_3'
    | k1_tarski('#skF_5') = '#skF_3'
    | k1_tarski('#skF_4') = '#skF_3'
    | k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4976,c_60])).

tff(c_5748,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_5747])).

tff(c_5769,plain,(
    ! [A_11] : k4_xboole_0('#skF_3',A_11) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5748,c_5748,c_14])).

tff(c_4975,plain,(
    k4_xboole_0('#skF_3',k2_tarski('#skF_4','#skF_5')) != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_5762,plain,(
    k4_xboole_0('#skF_3',k2_tarski('#skF_4','#skF_5')) != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5748,c_4975])).

tff(c_5799,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5769,c_5762])).

tff(c_5800,plain,
    ( k1_tarski('#skF_4') = '#skF_3'
    | k1_tarski('#skF_5') = '#skF_3'
    | k2_tarski('#skF_4','#skF_5') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_5747])).

tff(c_5836,plain,(
    k2_tarski('#skF_4','#skF_5') = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_5800])).

tff(c_5837,plain,(
    k4_xboole_0('#skF_3','#skF_3') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_5836,c_4975])).

tff(c_5847,plain,(
    k4_xboole_0('#skF_3',k2_tarski('#skF_4','#skF_5')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_5836,c_168])).

tff(c_5880,plain,(
    k4_xboole_0('#skF_3','#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_5836,c_5847])).

tff(c_5901,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_5837,c_5880])).

tff(c_5902,plain,
    ( k1_tarski('#skF_5') = '#skF_3'
    | k1_tarski('#skF_4') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_5800])).

tff(c_5904,plain,(
    k1_tarski('#skF_4') = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_5902])).

tff(c_5958,plain,(
    ! [B_25] : k4_xboole_0('#skF_3',k2_tarski('#skF_4',B_25)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_5904,c_48])).

tff(c_6045,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5958,c_4975])).

tff(c_6046,plain,(
    k1_tarski('#skF_5') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_5902])).

tff(c_6145,plain,(
    ! [B_496] : r1_tarski('#skF_3',k2_tarski(B_496,'#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_6046,c_42])).

tff(c_6153,plain,(
    ! [B_496] : k4_xboole_0('#skF_3',k2_tarski(B_496,'#skF_5')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6145,c_8])).

tff(c_6206,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6153,c_4975])).

tff(c_6208,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_68,plain,
    ( k2_tarski('#skF_4','#skF_5') = '#skF_3'
    | k1_tarski('#skF_5') = '#skF_3'
    | k1_tarski('#skF_4') = '#skF_3'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_6574,plain,
    ( k2_tarski('#skF_4','#skF_5') = '#skF_3'
    | k1_tarski('#skF_5') = '#skF_3'
    | k1_tarski('#skF_4') = '#skF_3'
    | '#skF_6' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6208,c_6208,c_68])).

tff(c_6575,plain,(
    '#skF_6' = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_6574])).

tff(c_6210,plain,(
    ! [A_11] : k4_xboole_0('#skF_6',A_11) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6208,c_6208,c_14])).

tff(c_6586,plain,(
    ! [A_11] : k4_xboole_0('#skF_3',A_11) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6575,c_6575,c_6210])).

tff(c_6207,plain,(
    k4_xboole_0('#skF_3',k2_tarski('#skF_4','#skF_5')) != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_6225,plain,(
    k4_xboole_0('#skF_3',k2_tarski('#skF_4','#skF_5')) != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6208,c_6207])).

tff(c_6585,plain,(
    k4_xboole_0('#skF_3',k2_tarski('#skF_4','#skF_5')) != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6575,c_6225])).

tff(c_6612,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6586,c_6585])).

tff(c_6613,plain,
    ( k1_tarski('#skF_4') = '#skF_3'
    | k1_tarski('#skF_5') = '#skF_3'
    | k2_tarski('#skF_4','#skF_5') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_6574])).

tff(c_6742,plain,(
    k2_tarski('#skF_4','#skF_5') = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_6613])).

tff(c_6743,plain,(
    k4_xboole_0('#skF_3','#skF_3') != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6742,c_6225])).

tff(c_6262,plain,(
    ! [A_516,B_517] :
      ( k4_xboole_0(A_516,B_517) = '#skF_6'
      | ~ r1_tarski(A_516,B_517) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6208,c_8])).

tff(c_6281,plain,(
    ! [B_22,C_23] : k4_xboole_0(k2_tarski(B_22,C_23),k2_tarski(B_22,C_23)) = '#skF_6' ),
    inference(resolution,[status(thm)],[c_40,c_6262])).

tff(c_6771,plain,(
    k4_xboole_0('#skF_3',k2_tarski('#skF_4','#skF_5')) = '#skF_6' ),
    inference(superposition,[status(thm),theory(equality)],[c_6742,c_6281])).

tff(c_6803,plain,(
    k4_xboole_0('#skF_3','#skF_3') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6742,c_6771])).

tff(c_6824,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_6743,c_6803])).

tff(c_6825,plain,
    ( k1_tarski('#skF_5') = '#skF_3'
    | k1_tarski('#skF_4') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_6613])).

tff(c_6827,plain,(
    k1_tarski('#skF_4') = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_6825])).

tff(c_6233,plain,(
    ! [A_24,B_25] : k4_xboole_0(k1_tarski(A_24),k2_tarski(A_24,B_25)) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6208,c_48])).

tff(c_6887,plain,(
    ! [B_25] : k4_xboole_0('#skF_3',k2_tarski('#skF_4',B_25)) = '#skF_6' ),
    inference(superposition,[status(thm),theory(equality)],[c_6827,c_6233])).

tff(c_6974,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6887,c_6225])).

tff(c_6975,plain,(
    k1_tarski('#skF_5') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_6825])).

tff(c_7080,plain,(
    ! [B_585] : r1_tarski('#skF_3',k2_tarski(B_585,'#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_6975,c_42])).

tff(c_6261,plain,(
    ! [A_4,B_5] :
      ( k4_xboole_0(A_4,B_5) = '#skF_6'
      | ~ r1_tarski(A_4,B_5) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6208,c_8])).

tff(c_7088,plain,(
    ! [B_585] : k4_xboole_0('#skF_3',k2_tarski(B_585,'#skF_5')) = '#skF_6' ),
    inference(resolution,[status(thm)],[c_7080,c_6261])).

tff(c_7141,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_7088,c_6225])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.35  % Computer   : n020.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 12:38:52 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.06/2.22  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.06/2.24  
% 6.06/2.24  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.06/2.24  %$ r2_hidden > r1_tarski > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_8 > #skF_4
% 6.06/2.24  
% 6.06/2.24  %Foreground sorts:
% 6.06/2.24  
% 6.06/2.24  
% 6.06/2.24  %Background operators:
% 6.06/2.24  
% 6.06/2.24  
% 6.06/2.24  %Foreground operators:
% 6.06/2.24  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 6.06/2.24  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.06/2.24  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.06/2.24  tff(k1_tarski, type, k1_tarski: $i > $i).
% 6.06/2.24  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 6.06/2.24  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.06/2.24  tff('#skF_7', type, '#skF_7': $i).
% 6.06/2.24  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.06/2.24  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 6.06/2.24  tff('#skF_5', type, '#skF_5': $i).
% 6.06/2.24  tff('#skF_6', type, '#skF_6': $i).
% 6.06/2.24  tff('#skF_3', type, '#skF_3': $i).
% 6.06/2.24  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 6.06/2.24  tff('#skF_8', type, '#skF_8': $i).
% 6.06/2.24  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.06/2.24  tff('#skF_4', type, '#skF_4': $i).
% 6.06/2.24  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.06/2.24  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 6.06/2.24  
% 6.06/2.26  tff(f_93, negated_conjecture, ~(![A, B, C]: ((k4_xboole_0(A, k2_tarski(B, C)) = k1_xboole_0) <=> ~(((~(A = k1_xboole_0) & ~(A = k1_tarski(B))) & ~(A = k1_tarski(C))) & ~(A = k2_tarski(B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t75_zfmisc_1)).
% 6.06/2.26  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 6.06/2.26  tff(f_29, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 6.06/2.26  tff(f_41, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_boole)).
% 6.06/2.26  tff(f_33, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t37_xboole_1)).
% 6.06/2.26  tff(f_39, axiom, (![A, B, C]: (r1_tarski(k4_xboole_0(A, B), C) => r1_tarski(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_xboole_1)).
% 6.06/2.26  tff(f_71, axiom, (![A, B, C]: (r1_tarski(A, k2_tarski(B, C)) <=> ~(((~(A = k1_xboole_0) & ~(A = k1_tarski(B))) & ~(A = k1_tarski(C))) & ~(A = k2_tarski(B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l45_zfmisc_1)).
% 6.06/2.26  tff(f_73, axiom, (![A, B]: (k4_xboole_0(k1_tarski(A), k2_tarski(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_zfmisc_1)).
% 6.06/2.26  tff(c_66, plain, (k4_xboole_0('#skF_3', k2_tarski('#skF_4', '#skF_5'))!=k1_xboole_0 | k1_xboole_0!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_93])).
% 6.06/2.26  tff(c_114, plain, (k1_xboole_0!='#skF_6'), inference(splitLeft, [status(thm)], [c_66])).
% 6.06/2.26  tff(c_62, plain, (k4_xboole_0('#skF_3', k2_tarski('#skF_4', '#skF_5'))!=k1_xboole_0 | k1_tarski('#skF_7')!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_93])).
% 6.06/2.26  tff(c_303, plain, (k1_tarski('#skF_7')!='#skF_6'), inference(splitLeft, [status(thm)], [c_62])).
% 6.06/2.26  tff(c_58, plain, (k4_xboole_0('#skF_3', k2_tarski('#skF_4', '#skF_5'))!=k1_xboole_0 | k1_tarski('#skF_8')!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_93])).
% 6.06/2.26  tff(c_195, plain, (k1_tarski('#skF_8')!='#skF_6'), inference(splitLeft, [status(thm)], [c_58])).
% 6.06/2.26  tff(c_54, plain, (k4_xboole_0('#skF_3', k2_tarski('#skF_4', '#skF_5'))!=k1_xboole_0 | k2_tarski('#skF_7', '#skF_8')!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_93])).
% 6.06/2.26  tff(c_333, plain, (k2_tarski('#skF_7', '#skF_8')!='#skF_6'), inference(splitLeft, [status(thm)], [c_54])).
% 6.06/2.26  tff(c_2, plain, (![A_1]: (k2_xboole_0(A_1, A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 6.06/2.26  tff(c_4, plain, (![A_3]: (r1_tarski(k1_xboole_0, A_3))), inference(cnfTransformation, [status(thm)], [f_29])).
% 6.06/2.26  tff(c_14, plain, (![A_11]: (k4_xboole_0(k1_xboole_0, A_11)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_41])).
% 6.06/2.26  tff(c_72, plain, (k2_tarski('#skF_4', '#skF_5')='#skF_3' | k1_tarski('#skF_5')='#skF_3' | k1_tarski('#skF_4')='#skF_3' | k1_xboole_0='#skF_3' | k4_xboole_0('#skF_6', k2_tarski('#skF_7', '#skF_8'))=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_93])).
% 6.06/2.26  tff(c_1142, plain, (k4_xboole_0('#skF_6', k2_tarski('#skF_7', '#skF_8'))=k1_xboole_0), inference(splitLeft, [status(thm)], [c_72])).
% 6.06/2.26  tff(c_6, plain, (![A_4, B_5]: (r1_tarski(A_4, B_5) | k4_xboole_0(A_4, B_5)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 6.06/2.26  tff(c_340, plain, (![A_68, B_69, C_70]: (r1_tarski(A_68, k2_xboole_0(B_69, C_70)) | ~r1_tarski(k4_xboole_0(A_68, B_69), C_70))), inference(cnfTransformation, [status(thm)], [f_39])).
% 6.06/2.26  tff(c_1046, plain, (![A_146, B_147, B_148]: (r1_tarski(A_146, k2_xboole_0(B_147, B_148)) | k4_xboole_0(k4_xboole_0(A_146, B_147), B_148)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_340])).
% 6.06/2.26  tff(c_1059, plain, (![A_146, A_1]: (r1_tarski(A_146, A_1) | k4_xboole_0(k4_xboole_0(A_146, A_1), A_1)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2, c_1046])).
% 6.06/2.26  tff(c_1146, plain, (r1_tarski('#skF_6', k2_tarski('#skF_7', '#skF_8')) | k4_xboole_0(k1_xboole_0, k2_tarski('#skF_7', '#skF_8'))!=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_1142, c_1059])).
% 6.06/2.26  tff(c_1153, plain, (r1_tarski('#skF_6', k2_tarski('#skF_7', '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_1146])).
% 6.06/2.26  tff(c_1356, plain, (![B_175, C_176, A_177]: (k2_tarski(B_175, C_176)=A_177 | k1_tarski(C_176)=A_177 | k1_tarski(B_175)=A_177 | k1_xboole_0=A_177 | ~r1_tarski(A_177, k2_tarski(B_175, C_176)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 6.06/2.26  tff(c_1363, plain, (k2_tarski('#skF_7', '#skF_8')='#skF_6' | k1_tarski('#skF_8')='#skF_6' | k1_tarski('#skF_7')='#skF_6' | k1_xboole_0='#skF_6'), inference(resolution, [status(thm)], [c_1153, c_1356])).
% 6.06/2.26  tff(c_1392, plain, $false, inference(negUnitSimplification, [status(thm)], [c_114, c_303, c_195, c_333, c_1363])).
% 6.06/2.26  tff(c_1393, plain, (k1_xboole_0='#skF_3' | k1_tarski('#skF_4')='#skF_3' | k1_tarski('#skF_5')='#skF_3' | k2_tarski('#skF_4', '#skF_5')='#skF_3'), inference(splitRight, [status(thm)], [c_72])).
% 6.06/2.26  tff(c_1436, plain, (k2_tarski('#skF_4', '#skF_5')='#skF_3'), inference(splitLeft, [status(thm)], [c_1393])).
% 6.06/2.26  tff(c_70, plain, (k4_xboole_0('#skF_3', k2_tarski('#skF_4', '#skF_5'))!=k1_xboole_0 | k4_xboole_0('#skF_6', k2_tarski('#skF_7', '#skF_8'))=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_93])).
% 6.06/2.26  tff(c_397, plain, (k4_xboole_0('#skF_3', k2_tarski('#skF_4', '#skF_5'))!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_70])).
% 6.06/2.26  tff(c_1437, plain, (k4_xboole_0('#skF_3', '#skF_3')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_1436, c_397])).
% 6.06/2.26  tff(c_40, plain, (![B_22, C_23]: (r1_tarski(k2_tarski(B_22, C_23), k2_tarski(B_22, C_23)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 6.06/2.26  tff(c_1492, plain, (r1_tarski('#skF_3', k2_tarski('#skF_4', '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_1436, c_40])).
% 6.06/2.26  tff(c_1516, plain, (r1_tarski('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1436, c_1492])).
% 6.06/2.26  tff(c_8, plain, (![A_4, B_5]: (k4_xboole_0(A_4, B_5)=k1_xboole_0 | ~r1_tarski(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_33])).
% 6.06/2.26  tff(c_1522, plain, (k4_xboole_0('#skF_3', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_1516, c_8])).
% 6.06/2.26  tff(c_1542, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1437, c_1522])).
% 6.06/2.26  tff(c_1543, plain, (k1_tarski('#skF_5')='#skF_3' | k1_tarski('#skF_4')='#skF_3' | k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_1393])).
% 6.06/2.26  tff(c_1545, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_1543])).
% 6.06/2.26  tff(c_1568, plain, (![A_11]: (k4_xboole_0('#skF_3', A_11)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1545, c_1545, c_14])).
% 6.06/2.26  tff(c_1558, plain, (k4_xboole_0('#skF_3', k2_tarski('#skF_4', '#skF_5'))!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1545, c_397])).
% 6.06/2.26  tff(c_1588, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1568, c_1558])).
% 6.06/2.26  tff(c_1589, plain, (k1_tarski('#skF_4')='#skF_3' | k1_tarski('#skF_5')='#skF_3'), inference(splitRight, [status(thm)], [c_1543])).
% 6.06/2.26  tff(c_1591, plain, (k1_tarski('#skF_5')='#skF_3'), inference(splitLeft, [status(thm)], [c_1589])).
% 6.06/2.26  tff(c_42, plain, (![C_23, B_22]: (r1_tarski(k1_tarski(C_23), k2_tarski(B_22, C_23)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 6.06/2.26  tff(c_1774, plain, (![B_188]: (r1_tarski('#skF_3', k2_tarski(B_188, '#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_1591, c_42])).
% 6.06/2.26  tff(c_1782, plain, (![B_188]: (k4_xboole_0('#skF_3', k2_tarski(B_188, '#skF_5'))=k1_xboole_0)), inference(resolution, [status(thm)], [c_1774, c_8])).
% 6.06/2.26  tff(c_1831, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1782, c_397])).
% 6.06/2.26  tff(c_1832, plain, (k1_tarski('#skF_4')='#skF_3'), inference(splitRight, [status(thm)], [c_1589])).
% 6.06/2.26  tff(c_48, plain, (![A_24, B_25]: (k4_xboole_0(k1_tarski(A_24), k2_tarski(A_24, B_25))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_73])).
% 6.06/2.26  tff(c_1938, plain, (![B_25]: (k4_xboole_0('#skF_3', k2_tarski('#skF_4', B_25))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1832, c_48])).
% 6.06/2.26  tff(c_2051, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1938, c_397])).
% 6.06/2.26  tff(c_2052, plain, (k4_xboole_0('#skF_6', k2_tarski('#skF_7', '#skF_8'))=k1_xboole_0), inference(splitRight, [status(thm)], [c_70])).
% 6.06/2.26  tff(c_12, plain, (![A_8, B_9, C_10]: (r1_tarski(A_8, k2_xboole_0(B_9, C_10)) | ~r1_tarski(k4_xboole_0(A_8, B_9), C_10))), inference(cnfTransformation, [status(thm)], [f_39])).
% 6.06/2.26  tff(c_2057, plain, (![C_10]: (r1_tarski('#skF_6', k2_xboole_0(k2_tarski('#skF_7', '#skF_8'), C_10)) | ~r1_tarski(k1_xboole_0, C_10))), inference(superposition, [status(thm), theory('equality')], [c_2052, c_12])).
% 6.06/2.26  tff(c_2072, plain, (![C_199]: (r1_tarski('#skF_6', k2_xboole_0(k2_tarski('#skF_7', '#skF_8'), C_199)))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_2057])).
% 6.06/2.26  tff(c_2079, plain, (r1_tarski('#skF_6', k2_tarski('#skF_7', '#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_2, c_2072])).
% 6.06/2.26  tff(c_3104, plain, (![B_301, C_302, A_303]: (k2_tarski(B_301, C_302)=A_303 | k1_tarski(C_302)=A_303 | k1_tarski(B_301)=A_303 | k1_xboole_0=A_303 | ~r1_tarski(A_303, k2_tarski(B_301, C_302)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 6.06/2.26  tff(c_3114, plain, (k2_tarski('#skF_7', '#skF_8')='#skF_6' | k1_tarski('#skF_8')='#skF_6' | k1_tarski('#skF_7')='#skF_6' | k1_xboole_0='#skF_6'), inference(resolution, [status(thm)], [c_2079, c_3104])).
% 6.06/2.26  tff(c_3144, plain, $false, inference(negUnitSimplification, [status(thm)], [c_114, c_303, c_195, c_333, c_3114])).
% 6.06/2.26  tff(c_3145, plain, (k4_xboole_0('#skF_3', k2_tarski('#skF_4', '#skF_5'))!=k1_xboole_0), inference(splitRight, [status(thm)], [c_54])).
% 6.06/2.26  tff(c_3146, plain, (k2_tarski('#skF_7', '#skF_8')='#skF_6'), inference(splitRight, [status(thm)], [c_54])).
% 6.06/2.26  tff(c_56, plain, (k2_tarski('#skF_4', '#skF_5')='#skF_3' | k1_tarski('#skF_5')='#skF_3' | k1_tarski('#skF_4')='#skF_3' | k1_xboole_0='#skF_3' | k2_tarski('#skF_7', '#skF_8')!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_93])).
% 6.06/2.26  tff(c_3469, plain, (k2_tarski('#skF_4', '#skF_5')='#skF_3' | k1_tarski('#skF_5')='#skF_3' | k1_tarski('#skF_4')='#skF_3' | k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_3146, c_56])).
% 6.06/2.26  tff(c_3470, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_3469])).
% 6.06/2.26  tff(c_3487, plain, (![A_11]: (k4_xboole_0('#skF_3', A_11)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_3470, c_3470, c_14])).
% 6.06/2.26  tff(c_3193, plain, (k4_xboole_0('#skF_3', k2_tarski('#skF_4', '#skF_5'))!=k1_xboole_0 | k4_xboole_0('#skF_6', '#skF_6')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_3146, c_70])).
% 6.06/2.26  tff(c_3194, plain, (k4_xboole_0('#skF_3', k2_tarski('#skF_4', '#skF_5'))!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_3193])).
% 6.06/2.26  tff(c_3476, plain, (k4_xboole_0('#skF_3', k2_tarski('#skF_4', '#skF_5'))!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_3470, c_3194])).
% 6.06/2.26  tff(c_3516, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3487, c_3476])).
% 6.06/2.26  tff(c_3517, plain, (k1_tarski('#skF_4')='#skF_3' | k1_tarski('#skF_5')='#skF_3' | k2_tarski('#skF_4', '#skF_5')='#skF_3'), inference(splitRight, [status(thm)], [c_3469])).
% 6.06/2.26  tff(c_3635, plain, (k2_tarski('#skF_4', '#skF_5')='#skF_3'), inference(splitLeft, [status(thm)], [c_3517])).
% 6.06/2.26  tff(c_3636, plain, (k4_xboole_0('#skF_3', '#skF_3')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_3635, c_3194])).
% 6.06/2.26  tff(c_3661, plain, (r1_tarski('#skF_3', k2_tarski('#skF_4', '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_3635, c_40])).
% 6.06/2.26  tff(c_3681, plain, (r1_tarski('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_3635, c_3661])).
% 6.06/2.26  tff(c_3687, plain, (k4_xboole_0('#skF_3', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_3681, c_8])).
% 6.06/2.26  tff(c_3697, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3636, c_3687])).
% 6.06/2.26  tff(c_3698, plain, (k1_tarski('#skF_5')='#skF_3' | k1_tarski('#skF_4')='#skF_3'), inference(splitRight, [status(thm)], [c_3517])).
% 6.06/2.26  tff(c_3700, plain, (k1_tarski('#skF_4')='#skF_3'), inference(splitLeft, [status(thm)], [c_3698])).
% 6.06/2.26  tff(c_3749, plain, (![B_25]: (k4_xboole_0('#skF_3', k2_tarski('#skF_4', B_25))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_3700, c_48])).
% 6.06/2.26  tff(c_3833, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3749, c_3194])).
% 6.06/2.26  tff(c_3834, plain, (k1_tarski('#skF_5')='#skF_3'), inference(splitRight, [status(thm)], [c_3698])).
% 6.06/2.26  tff(c_148, plain, (![A_49, B_50]: (k4_xboole_0(A_49, B_50)=k1_xboole_0 | ~r1_tarski(A_49, B_50))), inference(cnfTransformation, [status(thm)], [f_33])).
% 6.06/2.26  tff(c_169, plain, (![C_23, B_22]: (k4_xboole_0(k1_tarski(C_23), k2_tarski(B_22, C_23))=k1_xboole_0)), inference(resolution, [status(thm)], [c_42, c_148])).
% 6.06/2.26  tff(c_3875, plain, (![B_22]: (k4_xboole_0('#skF_3', k2_tarski(B_22, '#skF_5'))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_3834, c_169])).
% 6.06/2.26  tff(c_3986, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3875, c_3194])).
% 6.06/2.26  tff(c_3988, plain, (k4_xboole_0('#skF_3', k2_tarski('#skF_4', '#skF_5'))=k1_xboole_0), inference(splitRight, [status(thm)], [c_3193])).
% 6.06/2.26  tff(c_4048, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3145, c_3988])).
% 6.06/2.26  tff(c_4050, plain, (k1_tarski('#skF_7')='#skF_6'), inference(splitRight, [status(thm)], [c_62])).
% 6.06/2.26  tff(c_64, plain, (k2_tarski('#skF_4', '#skF_5')='#skF_3' | k1_tarski('#skF_5')='#skF_3' | k1_tarski('#skF_4')='#skF_3' | k1_xboole_0='#skF_3' | k1_tarski('#skF_7')!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_93])).
% 6.06/2.26  tff(c_4466, plain, (k2_tarski('#skF_4', '#skF_5')='#skF_3' | k1_tarski('#skF_5')='#skF_3' | k1_tarski('#skF_4')='#skF_3' | k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_4050, c_64])).
% 6.06/2.26  tff(c_4467, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_4466])).
% 6.06/2.26  tff(c_4486, plain, (![A_11]: (k4_xboole_0('#skF_3', A_11)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4467, c_4467, c_14])).
% 6.06/2.26  tff(c_4049, plain, (k4_xboole_0('#skF_3', k2_tarski('#skF_4', '#skF_5'))!=k1_xboole_0), inference(splitRight, [status(thm)], [c_62])).
% 6.06/2.26  tff(c_4476, plain, (k4_xboole_0('#skF_3', k2_tarski('#skF_4', '#skF_5'))!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_4467, c_4049])).
% 6.06/2.26  tff(c_4515, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4486, c_4476])).
% 6.06/2.26  tff(c_4516, plain, (k1_tarski('#skF_4')='#skF_3' | k1_tarski('#skF_5')='#skF_3' | k2_tarski('#skF_4', '#skF_5')='#skF_3'), inference(splitRight, [status(thm)], [c_4466])).
% 6.06/2.26  tff(c_4642, plain, (k2_tarski('#skF_4', '#skF_5')='#skF_3'), inference(splitLeft, [status(thm)], [c_4516])).
% 6.06/2.26  tff(c_4643, plain, (k4_xboole_0('#skF_3', '#skF_3')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_4642, c_4049])).
% 6.06/2.26  tff(c_168, plain, (![B_22, C_23]: (k4_xboole_0(k2_tarski(B_22, C_23), k2_tarski(B_22, C_23))=k1_xboole_0)), inference(resolution, [status(thm)], [c_40, c_148])).
% 6.06/2.26  tff(c_4656, plain, (k4_xboole_0(k2_tarski('#skF_4', '#skF_5'), '#skF_3')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_4642, c_168])).
% 6.06/2.26  tff(c_4687, plain, (k4_xboole_0('#skF_3', '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_4642, c_4656])).
% 6.06/2.26  tff(c_4707, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4643, c_4687])).
% 6.06/2.26  tff(c_4708, plain, (k1_tarski('#skF_5')='#skF_3' | k1_tarski('#skF_4')='#skF_3'), inference(splitRight, [status(thm)], [c_4516])).
% 6.06/2.26  tff(c_4710, plain, (k1_tarski('#skF_4')='#skF_3'), inference(splitLeft, [status(thm)], [c_4708])).
% 6.06/2.26  tff(c_4754, plain, (![B_25]: (k4_xboole_0('#skF_3', k2_tarski('#skF_4', B_25))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_4710, c_48])).
% 6.06/2.26  tff(c_4832, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4754, c_4049])).
% 6.06/2.26  tff(c_4833, plain, (k1_tarski('#skF_5')='#skF_3'), inference(splitRight, [status(thm)], [c_4708])).
% 6.06/2.26  tff(c_4931, plain, (![B_414]: (r1_tarski('#skF_3', k2_tarski(B_414, '#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_4833, c_42])).
% 6.06/2.26  tff(c_4939, plain, (![B_414]: (k4_xboole_0('#skF_3', k2_tarski(B_414, '#skF_5'))=k1_xboole_0)), inference(resolution, [status(thm)], [c_4931, c_8])).
% 6.06/2.26  tff(c_4974, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4939, c_4049])).
% 6.06/2.26  tff(c_4976, plain, (k1_tarski('#skF_8')='#skF_6'), inference(splitRight, [status(thm)], [c_58])).
% 6.06/2.26  tff(c_60, plain, (k2_tarski('#skF_4', '#skF_5')='#skF_3' | k1_tarski('#skF_5')='#skF_3' | k1_tarski('#skF_4')='#skF_3' | k1_xboole_0='#skF_3' | k1_tarski('#skF_8')!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_93])).
% 6.06/2.26  tff(c_5747, plain, (k2_tarski('#skF_4', '#skF_5')='#skF_3' | k1_tarski('#skF_5')='#skF_3' | k1_tarski('#skF_4')='#skF_3' | k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_4976, c_60])).
% 6.06/2.26  tff(c_5748, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_5747])).
% 6.06/2.26  tff(c_5769, plain, (![A_11]: (k4_xboole_0('#skF_3', A_11)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_5748, c_5748, c_14])).
% 6.06/2.26  tff(c_4975, plain, (k4_xboole_0('#skF_3', k2_tarski('#skF_4', '#skF_5'))!=k1_xboole_0), inference(splitRight, [status(thm)], [c_58])).
% 6.06/2.26  tff(c_5762, plain, (k4_xboole_0('#skF_3', k2_tarski('#skF_4', '#skF_5'))!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_5748, c_4975])).
% 6.06/2.26  tff(c_5799, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_5769, c_5762])).
% 6.06/2.26  tff(c_5800, plain, (k1_tarski('#skF_4')='#skF_3' | k1_tarski('#skF_5')='#skF_3' | k2_tarski('#skF_4', '#skF_5')='#skF_3'), inference(splitRight, [status(thm)], [c_5747])).
% 6.06/2.26  tff(c_5836, plain, (k2_tarski('#skF_4', '#skF_5')='#skF_3'), inference(splitLeft, [status(thm)], [c_5800])).
% 6.06/2.26  tff(c_5837, plain, (k4_xboole_0('#skF_3', '#skF_3')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_5836, c_4975])).
% 6.06/2.26  tff(c_5847, plain, (k4_xboole_0('#skF_3', k2_tarski('#skF_4', '#skF_5'))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_5836, c_168])).
% 6.06/2.26  tff(c_5880, plain, (k4_xboole_0('#skF_3', '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_5836, c_5847])).
% 6.06/2.26  tff(c_5901, plain, $false, inference(negUnitSimplification, [status(thm)], [c_5837, c_5880])).
% 6.06/2.26  tff(c_5902, plain, (k1_tarski('#skF_5')='#skF_3' | k1_tarski('#skF_4')='#skF_3'), inference(splitRight, [status(thm)], [c_5800])).
% 6.06/2.26  tff(c_5904, plain, (k1_tarski('#skF_4')='#skF_3'), inference(splitLeft, [status(thm)], [c_5902])).
% 6.06/2.26  tff(c_5958, plain, (![B_25]: (k4_xboole_0('#skF_3', k2_tarski('#skF_4', B_25))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_5904, c_48])).
% 6.06/2.26  tff(c_6045, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_5958, c_4975])).
% 6.06/2.26  tff(c_6046, plain, (k1_tarski('#skF_5')='#skF_3'), inference(splitRight, [status(thm)], [c_5902])).
% 6.06/2.26  tff(c_6145, plain, (![B_496]: (r1_tarski('#skF_3', k2_tarski(B_496, '#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_6046, c_42])).
% 6.06/2.26  tff(c_6153, plain, (![B_496]: (k4_xboole_0('#skF_3', k2_tarski(B_496, '#skF_5'))=k1_xboole_0)), inference(resolution, [status(thm)], [c_6145, c_8])).
% 6.06/2.26  tff(c_6206, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6153, c_4975])).
% 6.06/2.26  tff(c_6208, plain, (k1_xboole_0='#skF_6'), inference(splitRight, [status(thm)], [c_66])).
% 6.06/2.26  tff(c_68, plain, (k2_tarski('#skF_4', '#skF_5')='#skF_3' | k1_tarski('#skF_5')='#skF_3' | k1_tarski('#skF_4')='#skF_3' | k1_xboole_0='#skF_3' | k1_xboole_0!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_93])).
% 6.06/2.26  tff(c_6574, plain, (k2_tarski('#skF_4', '#skF_5')='#skF_3' | k1_tarski('#skF_5')='#skF_3' | k1_tarski('#skF_4')='#skF_3' | '#skF_6'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_6208, c_6208, c_68])).
% 6.06/2.26  tff(c_6575, plain, ('#skF_6'='#skF_3'), inference(splitLeft, [status(thm)], [c_6574])).
% 6.06/2.26  tff(c_6210, plain, (![A_11]: (k4_xboole_0('#skF_6', A_11)='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_6208, c_6208, c_14])).
% 6.06/2.26  tff(c_6586, plain, (![A_11]: (k4_xboole_0('#skF_3', A_11)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_6575, c_6575, c_6210])).
% 6.06/2.26  tff(c_6207, plain, (k4_xboole_0('#skF_3', k2_tarski('#skF_4', '#skF_5'))!=k1_xboole_0), inference(splitRight, [status(thm)], [c_66])).
% 6.06/2.26  tff(c_6225, plain, (k4_xboole_0('#skF_3', k2_tarski('#skF_4', '#skF_5'))!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_6208, c_6207])).
% 6.06/2.26  tff(c_6585, plain, (k4_xboole_0('#skF_3', k2_tarski('#skF_4', '#skF_5'))!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_6575, c_6225])).
% 6.06/2.26  tff(c_6612, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6586, c_6585])).
% 6.06/2.26  tff(c_6613, plain, (k1_tarski('#skF_4')='#skF_3' | k1_tarski('#skF_5')='#skF_3' | k2_tarski('#skF_4', '#skF_5')='#skF_3'), inference(splitRight, [status(thm)], [c_6574])).
% 6.06/2.26  tff(c_6742, plain, (k2_tarski('#skF_4', '#skF_5')='#skF_3'), inference(splitLeft, [status(thm)], [c_6613])).
% 6.06/2.26  tff(c_6743, plain, (k4_xboole_0('#skF_3', '#skF_3')!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_6742, c_6225])).
% 6.06/2.26  tff(c_6262, plain, (![A_516, B_517]: (k4_xboole_0(A_516, B_517)='#skF_6' | ~r1_tarski(A_516, B_517))), inference(demodulation, [status(thm), theory('equality')], [c_6208, c_8])).
% 6.06/2.26  tff(c_6281, plain, (![B_22, C_23]: (k4_xboole_0(k2_tarski(B_22, C_23), k2_tarski(B_22, C_23))='#skF_6')), inference(resolution, [status(thm)], [c_40, c_6262])).
% 6.06/2.26  tff(c_6771, plain, (k4_xboole_0('#skF_3', k2_tarski('#skF_4', '#skF_5'))='#skF_6'), inference(superposition, [status(thm), theory('equality')], [c_6742, c_6281])).
% 6.06/2.26  tff(c_6803, plain, (k4_xboole_0('#skF_3', '#skF_3')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_6742, c_6771])).
% 6.06/2.26  tff(c_6824, plain, $false, inference(negUnitSimplification, [status(thm)], [c_6743, c_6803])).
% 6.06/2.26  tff(c_6825, plain, (k1_tarski('#skF_5')='#skF_3' | k1_tarski('#skF_4')='#skF_3'), inference(splitRight, [status(thm)], [c_6613])).
% 6.06/2.26  tff(c_6827, plain, (k1_tarski('#skF_4')='#skF_3'), inference(splitLeft, [status(thm)], [c_6825])).
% 6.06/2.26  tff(c_6233, plain, (![A_24, B_25]: (k4_xboole_0(k1_tarski(A_24), k2_tarski(A_24, B_25))='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_6208, c_48])).
% 6.06/2.26  tff(c_6887, plain, (![B_25]: (k4_xboole_0('#skF_3', k2_tarski('#skF_4', B_25))='#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_6827, c_6233])).
% 6.06/2.26  tff(c_6974, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6887, c_6225])).
% 6.06/2.26  tff(c_6975, plain, (k1_tarski('#skF_5')='#skF_3'), inference(splitRight, [status(thm)], [c_6825])).
% 6.06/2.26  tff(c_7080, plain, (![B_585]: (r1_tarski('#skF_3', k2_tarski(B_585, '#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_6975, c_42])).
% 6.06/2.26  tff(c_6261, plain, (![A_4, B_5]: (k4_xboole_0(A_4, B_5)='#skF_6' | ~r1_tarski(A_4, B_5))), inference(demodulation, [status(thm), theory('equality')], [c_6208, c_8])).
% 6.06/2.26  tff(c_7088, plain, (![B_585]: (k4_xboole_0('#skF_3', k2_tarski(B_585, '#skF_5'))='#skF_6')), inference(resolution, [status(thm)], [c_7080, c_6261])).
% 6.06/2.26  tff(c_7141, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_7088, c_6225])).
% 6.06/2.26  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.06/2.26  
% 6.06/2.26  Inference rules
% 6.06/2.26  ----------------------
% 6.06/2.26  #Ref     : 0
% 6.06/2.26  #Sup     : 1607
% 6.06/2.26  #Fact    : 0
% 6.06/2.26  #Define  : 0
% 6.06/2.26  #Split   : 27
% 6.06/2.26  #Chain   : 0
% 6.06/2.26  #Close   : 0
% 6.06/2.26  
% 6.06/2.26  Ordering : KBO
% 6.06/2.26  
% 6.06/2.26  Simplification rules
% 6.06/2.26  ----------------------
% 6.06/2.26  #Subsume      : 96
% 6.06/2.26  #Demod        : 1119
% 6.06/2.26  #Tautology    : 890
% 6.06/2.26  #SimpNegUnit  : 26
% 6.06/2.26  #BackRed      : 115
% 6.06/2.26  
% 6.06/2.26  #Partial instantiations: 0
% 6.06/2.26  #Strategies tried      : 1
% 6.06/2.26  
% 6.06/2.26  Timing (in seconds)
% 6.06/2.26  ----------------------
% 6.06/2.26  Preprocessing        : 0.34
% 6.06/2.27  Parsing              : 0.18
% 6.06/2.27  CNF conversion       : 0.03
% 6.06/2.27  Main loop            : 1.06
% 6.06/2.27  Inferencing          : 0.37
% 6.06/2.27  Reduction            : 0.39
% 6.06/2.27  Demodulation         : 0.29
% 6.06/2.27  BG Simplification    : 0.04
% 6.06/2.27  Subsumption          : 0.18
% 6.06/2.27  Abstraction          : 0.04
% 6.06/2.27  MUC search           : 0.00
% 6.06/2.27  Cooper               : 0.00
% 6.06/2.27  Total                : 1.46
% 6.06/2.27  Index Insertion      : 0.00
% 6.06/2.27  Index Deletion       : 0.00
% 6.06/2.27  Index Matching       : 0.00
% 6.06/2.27  BG Taut test         : 0.00
%------------------------------------------------------------------------------

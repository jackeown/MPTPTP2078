%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:49:56 EST 2020

% Result     : Theorem 3.04s
% Output     : CNFRefutation 3.15s
% Verified   : 
% Statistics : Number of formulae       :  112 ( 272 expanded)
%              Number of leaves         :   27 (  93 expanded)
%              Depth                    :    8
%              Number of atoms          :  139 ( 469 expanded)
%              Number of equality atoms :   80 ( 290 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(f_33,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_37,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_69,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_tarski(A,k1_tarski(B))
      <=> ( A = k1_xboole_0
          | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_zfmisc_1)).

tff(f_62,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_39,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_43,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

tff(c_8,plain,(
    ! [B_4] : r1_tarski(B_4,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_1377,plain,(
    ! [A_105,B_106] :
      ( k4_xboole_0(A_105,B_106) = k1_xboole_0
      | ~ r1_tarski(A_105,B_106) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_1389,plain,(
    ! [B_4] : k4_xboole_0(B_4,B_4) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_8,c_1377])).

tff(c_32,plain,(
    ! [A_19,B_20] :
      ( r1_tarski(k1_tarski(A_19),B_20)
      | ~ r2_hidden(A_19,B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_36,plain,
    ( ~ r1_tarski('#skF_1',k1_tarski('#skF_2'))
    | k1_tarski('#skF_4') != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_147,plain,(
    k1_tarski('#skF_4') != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_36])).

tff(c_148,plain,(
    ! [A_42,B_43] :
      ( k4_xboole_0(A_42,B_43) = k1_xboole_0
      | ~ r1_tarski(A_42,B_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_160,plain,(
    ! [B_4] : k4_xboole_0(B_4,B_4) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_8,c_148])).

tff(c_46,plain,
    ( k1_tarski('#skF_2') = '#skF_1'
    | k1_xboole_0 = '#skF_1'
    | r1_tarski('#skF_3',k1_tarski('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_337,plain,(
    r1_tarski('#skF_3',k1_tarski('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_46])).

tff(c_4,plain,(
    ! [B_4,A_3] :
      ( B_4 = A_3
      | ~ r1_tarski(B_4,A_3)
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_339,plain,
    ( k1_tarski('#skF_4') = '#skF_3'
    | ~ r1_tarski(k1_tarski('#skF_4'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_337,c_4])).

tff(c_345,plain,(
    ~ r1_tarski(k1_tarski('#skF_4'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_147,c_339])).

tff(c_353,plain,(
    ~ r2_hidden('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_32,c_345])).

tff(c_40,plain,
    ( ~ r1_tarski('#skF_1',k1_tarski('#skF_2'))
    | k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_117,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_40])).

tff(c_120,plain,(
    ! [A_33,B_34] :
      ( r1_xboole_0(k1_tarski(A_33),B_34)
      | r2_hidden(A_33,B_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_20,plain,(
    ! [A_11,B_12] :
      ( k4_xboole_0(A_11,B_12) = A_11
      | ~ r1_xboole_0(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_448,plain,(
    ! [A_63,B_64] :
      ( k4_xboole_0(k1_tarski(A_63),B_64) = k1_tarski(A_63)
      | r2_hidden(A_63,B_64) ) ),
    inference(resolution,[status(thm)],[c_120,c_20])).

tff(c_16,plain,(
    ! [A_8,B_9] : k4_xboole_0(A_8,k4_xboole_0(A_8,B_9)) = k3_xboole_0(A_8,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_463,plain,(
    ! [A_63,B_64] :
      ( k4_xboole_0(k1_tarski(A_63),k1_tarski(A_63)) = k3_xboole_0(k1_tarski(A_63),B_64)
      | r2_hidden(A_63,B_64) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_448,c_16])).

tff(c_502,plain,(
    ! [A_65,B_66] :
      ( k3_xboole_0(k1_tarski(A_65),B_66) = k1_xboole_0
      | r2_hidden(A_65,B_66) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_160,c_463])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_545,plain,(
    ! [B_67,A_68] :
      ( k3_xboole_0(B_67,k1_tarski(A_68)) = k1_xboole_0
      | r2_hidden(A_68,B_67) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_502,c_2])).

tff(c_14,plain,(
    ! [A_7] : k4_xboole_0(A_7,k1_xboole_0) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_12,plain,(
    ! [A_5,B_6] :
      ( k4_xboole_0(A_5,B_6) = k1_xboole_0
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_346,plain,(
    k4_xboole_0('#skF_3',k1_tarski('#skF_4')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_337,c_12])).

tff(c_358,plain,(
    k3_xboole_0('#skF_3',k1_tarski('#skF_4')) = k4_xboole_0('#skF_3',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_346,c_16])).

tff(c_361,plain,(
    k3_xboole_0('#skF_3',k1_tarski('#skF_4')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_358])).

tff(c_555,plain,
    ( k1_xboole_0 = '#skF_3'
    | r2_hidden('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_545,c_361])).

tff(c_599,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_353,c_117,c_555])).

tff(c_600,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_tarski('#skF_2') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_606,plain,(
    k1_tarski('#skF_2') = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_600])).

tff(c_10,plain,(
    ! [A_5,B_6] :
      ( r1_tarski(A_5,B_6)
      | k4_xboole_0(A_5,B_6) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_44,plain,
    ( ~ r1_tarski('#skF_1',k1_tarski('#skF_2'))
    | r1_tarski('#skF_3',k1_tarski('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_186,plain,(
    ~ r1_tarski('#skF_1',k1_tarski('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_44])).

tff(c_190,plain,(
    k4_xboole_0('#skF_1',k1_tarski('#skF_2')) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_10,c_186])).

tff(c_607,plain,(
    k4_xboole_0('#skF_1','#skF_1') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_606,c_190])).

tff(c_611,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_160,c_607])).

tff(c_612,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_600])).

tff(c_18,plain,(
    ! [A_10] : k4_xboole_0(k1_xboole_0,A_10) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_622,plain,(
    ! [A_10] : k4_xboole_0('#skF_1',A_10) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_612,c_612,c_18])).

tff(c_616,plain,(
    k4_xboole_0('#skF_1',k1_tarski('#skF_2')) != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_612,c_190])).

tff(c_786,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_622,c_616])).

tff(c_787,plain,(
    r1_tarski('#skF_3',k1_tarski('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_814,plain,(
    ! [B_78,A_79] :
      ( B_78 = A_79
      | ~ r1_tarski(B_78,A_79)
      | ~ r1_tarski(A_79,B_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_818,plain,
    ( k1_tarski('#skF_4') = '#skF_3'
    | ~ r1_tarski(k1_tarski('#skF_4'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_787,c_814])).

tff(c_828,plain,(
    ~ r1_tarski(k1_tarski('#skF_4'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_147,c_818])).

tff(c_841,plain,(
    ~ r2_hidden('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_32,c_828])).

tff(c_1103,plain,(
    ! [A_96,B_97] :
      ( k4_xboole_0(k1_tarski(A_96),B_97) = k1_tarski(A_96)
      | r2_hidden(A_96,B_97) ) ),
    inference(resolution,[status(thm)],[c_120,c_20])).

tff(c_1115,plain,(
    ! [A_96,B_97] :
      ( k4_xboole_0(k1_tarski(A_96),k1_tarski(A_96)) = k3_xboole_0(k1_tarski(A_96),B_97)
      | r2_hidden(A_96,B_97) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1103,c_16])).

tff(c_1229,plain,(
    ! [A_100,B_101] :
      ( k3_xboole_0(k1_tarski(A_100),B_101) = k1_xboole_0
      | r2_hidden(A_100,B_101) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_160,c_1115])).

tff(c_1276,plain,(
    ! [B_102,A_103] :
      ( k3_xboole_0(B_102,k1_tarski(A_103)) = k1_xboole_0
      | r2_hidden(A_103,B_102) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1229,c_2])).

tff(c_792,plain,(
    k4_xboole_0('#skF_3',k1_tarski('#skF_4')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_787,c_12])).

tff(c_852,plain,(
    ! [A_80,B_81] : k4_xboole_0(A_80,k4_xboole_0(A_80,B_81)) = k3_xboole_0(A_80,B_81) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_874,plain,(
    k3_xboole_0('#skF_3',k1_tarski('#skF_4')) = k4_xboole_0('#skF_3',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_792,c_852])).

tff(c_891,plain,(
    k3_xboole_0('#skF_3',k1_tarski('#skF_4')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_874])).

tff(c_1296,plain,
    ( k1_xboole_0 = '#skF_3'
    | r2_hidden('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1276,c_891])).

tff(c_1342,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_841,c_117,c_1296])).

tff(c_1344,plain,(
    k1_tarski('#skF_4') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_38,plain,
    ( k1_tarski('#skF_2') = '#skF_1'
    | k1_xboole_0 = '#skF_1'
    | k1_tarski('#skF_4') != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_1497,plain,
    ( k1_tarski('#skF_2') = '#skF_1'
    | k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1344,c_38])).

tff(c_1498,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_1497])).

tff(c_1505,plain,(
    ! [A_10] : k4_xboole_0('#skF_1',A_10) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1498,c_1498,c_18])).

tff(c_1343,plain,(
    ~ r1_tarski('#skF_1',k1_tarski('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_1364,plain,(
    k4_xboole_0('#skF_1',k1_tarski('#skF_2')) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_10,c_1343])).

tff(c_1501,plain,(
    k4_xboole_0('#skF_1',k1_tarski('#skF_2')) != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1498,c_1364])).

tff(c_1655,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1505,c_1501])).

tff(c_1656,plain,(
    k1_tarski('#skF_2') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_1497])).

tff(c_1658,plain,(
    k4_xboole_0('#skF_1','#skF_1') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1656,c_1364])).

tff(c_1662,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1389,c_1658])).

tff(c_1664,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_42,plain,
    ( k1_tarski('#skF_2') = '#skF_1'
    | k1_xboole_0 = '#skF_1'
    | k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_1710,plain,
    ( k1_tarski('#skF_2') = '#skF_1'
    | '#skF_3' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1664,c_1664,c_42])).

tff(c_1711,plain,(
    '#skF_3' = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_1710])).

tff(c_1666,plain,(
    ! [A_10] : k4_xboole_0('#skF_3',A_10) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1664,c_1664,c_18])).

tff(c_1713,plain,(
    ! [A_10] : k4_xboole_0('#skF_1',A_10) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1711,c_1711,c_1666])).

tff(c_1715,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1711,c_1664])).

tff(c_1777,plain,(
    ! [A_136,B_137] :
      ( r1_tarski(A_136,B_137)
      | k4_xboole_0(A_136,B_137) != '#skF_1' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1715,c_10])).

tff(c_1663,plain,(
    ~ r1_tarski('#skF_1',k1_tarski('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_1780,plain,(
    k4_xboole_0('#skF_1',k1_tarski('#skF_2')) != '#skF_1' ),
    inference(resolution,[status(thm)],[c_1777,c_1663])).

tff(c_1784,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1713,c_1780])).

tff(c_1785,plain,(
    k1_tarski('#skF_2') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_1710])).

tff(c_1787,plain,(
    ~ r1_tarski('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1785,c_1663])).

tff(c_1790,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_1787])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.13/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.36  % Computer   : n022.cluster.edu
% 0.15/0.36  % Model      : x86_64 x86_64
% 0.15/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.36  % Memory     : 8042.1875MB
% 0.15/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.36  % CPULimit   : 60
% 0.15/0.36  % DateTime   : Tue Dec  1 14:44:25 EST 2020
% 0.15/0.36  % CPUTime    : 
% 0.15/0.37  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.04/1.52  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.04/1.53  
% 3.04/1.53  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.04/1.53  %$ r2_hidden > r1_xboole_0 > r1_tarski > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.04/1.53  
% 3.04/1.53  %Foreground sorts:
% 3.04/1.53  
% 3.04/1.53  
% 3.04/1.53  %Background operators:
% 3.04/1.53  
% 3.04/1.53  
% 3.04/1.53  %Foreground operators:
% 3.04/1.53  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.04/1.53  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.04/1.53  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.04/1.53  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.04/1.53  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.04/1.53  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.04/1.53  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.04/1.53  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.04/1.53  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.04/1.53  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.04/1.53  tff('#skF_2', type, '#skF_2': $i).
% 3.04/1.53  tff('#skF_3', type, '#skF_3': $i).
% 3.04/1.53  tff('#skF_1', type, '#skF_1': $i).
% 3.04/1.53  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.04/1.53  tff('#skF_4', type, '#skF_4': $i).
% 3.04/1.53  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.04/1.53  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.04/1.53  
% 3.15/1.55  tff(f_33, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.15/1.55  tff(f_37, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 3.15/1.55  tff(f_57, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 3.15/1.55  tff(f_69, negated_conjecture, ~(![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_zfmisc_1)).
% 3.15/1.55  tff(f_62, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 3.15/1.55  tff(f_47, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 3.15/1.55  tff(f_41, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 3.15/1.55  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 3.15/1.55  tff(f_39, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 3.15/1.55  tff(f_43, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_boole)).
% 3.15/1.55  tff(c_8, plain, (![B_4]: (r1_tarski(B_4, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.15/1.55  tff(c_1377, plain, (![A_105, B_106]: (k4_xboole_0(A_105, B_106)=k1_xboole_0 | ~r1_tarski(A_105, B_106))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.15/1.55  tff(c_1389, plain, (![B_4]: (k4_xboole_0(B_4, B_4)=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_1377])).
% 3.15/1.55  tff(c_32, plain, (![A_19, B_20]: (r1_tarski(k1_tarski(A_19), B_20) | ~r2_hidden(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.15/1.55  tff(c_36, plain, (~r1_tarski('#skF_1', k1_tarski('#skF_2')) | k1_tarski('#skF_4')!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.15/1.55  tff(c_147, plain, (k1_tarski('#skF_4')!='#skF_3'), inference(splitLeft, [status(thm)], [c_36])).
% 3.15/1.55  tff(c_148, plain, (![A_42, B_43]: (k4_xboole_0(A_42, B_43)=k1_xboole_0 | ~r1_tarski(A_42, B_43))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.15/1.55  tff(c_160, plain, (![B_4]: (k4_xboole_0(B_4, B_4)=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_148])).
% 3.15/1.55  tff(c_46, plain, (k1_tarski('#skF_2')='#skF_1' | k1_xboole_0='#skF_1' | r1_tarski('#skF_3', k1_tarski('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.15/1.55  tff(c_337, plain, (r1_tarski('#skF_3', k1_tarski('#skF_4'))), inference(splitLeft, [status(thm)], [c_46])).
% 3.15/1.55  tff(c_4, plain, (![B_4, A_3]: (B_4=A_3 | ~r1_tarski(B_4, A_3) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.15/1.55  tff(c_339, plain, (k1_tarski('#skF_4')='#skF_3' | ~r1_tarski(k1_tarski('#skF_4'), '#skF_3')), inference(resolution, [status(thm)], [c_337, c_4])).
% 3.15/1.55  tff(c_345, plain, (~r1_tarski(k1_tarski('#skF_4'), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_147, c_339])).
% 3.15/1.55  tff(c_353, plain, (~r2_hidden('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_32, c_345])).
% 3.15/1.55  tff(c_40, plain, (~r1_tarski('#skF_1', k1_tarski('#skF_2')) | k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.15/1.55  tff(c_117, plain, (k1_xboole_0!='#skF_3'), inference(splitLeft, [status(thm)], [c_40])).
% 3.15/1.55  tff(c_120, plain, (![A_33, B_34]: (r1_xboole_0(k1_tarski(A_33), B_34) | r2_hidden(A_33, B_34))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.15/1.55  tff(c_20, plain, (![A_11, B_12]: (k4_xboole_0(A_11, B_12)=A_11 | ~r1_xboole_0(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.15/1.55  tff(c_448, plain, (![A_63, B_64]: (k4_xboole_0(k1_tarski(A_63), B_64)=k1_tarski(A_63) | r2_hidden(A_63, B_64))), inference(resolution, [status(thm)], [c_120, c_20])).
% 3.15/1.55  tff(c_16, plain, (![A_8, B_9]: (k4_xboole_0(A_8, k4_xboole_0(A_8, B_9))=k3_xboole_0(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.15/1.55  tff(c_463, plain, (![A_63, B_64]: (k4_xboole_0(k1_tarski(A_63), k1_tarski(A_63))=k3_xboole_0(k1_tarski(A_63), B_64) | r2_hidden(A_63, B_64))), inference(superposition, [status(thm), theory('equality')], [c_448, c_16])).
% 3.15/1.55  tff(c_502, plain, (![A_65, B_66]: (k3_xboole_0(k1_tarski(A_65), B_66)=k1_xboole_0 | r2_hidden(A_65, B_66))), inference(demodulation, [status(thm), theory('equality')], [c_160, c_463])).
% 3.15/1.55  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.15/1.55  tff(c_545, plain, (![B_67, A_68]: (k3_xboole_0(B_67, k1_tarski(A_68))=k1_xboole_0 | r2_hidden(A_68, B_67))), inference(superposition, [status(thm), theory('equality')], [c_502, c_2])).
% 3.15/1.55  tff(c_14, plain, (![A_7]: (k4_xboole_0(A_7, k1_xboole_0)=A_7)), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.15/1.55  tff(c_12, plain, (![A_5, B_6]: (k4_xboole_0(A_5, B_6)=k1_xboole_0 | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.15/1.55  tff(c_346, plain, (k4_xboole_0('#skF_3', k1_tarski('#skF_4'))=k1_xboole_0), inference(resolution, [status(thm)], [c_337, c_12])).
% 3.15/1.55  tff(c_358, plain, (k3_xboole_0('#skF_3', k1_tarski('#skF_4'))=k4_xboole_0('#skF_3', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_346, c_16])).
% 3.15/1.55  tff(c_361, plain, (k3_xboole_0('#skF_3', k1_tarski('#skF_4'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_14, c_358])).
% 3.15/1.55  tff(c_555, plain, (k1_xboole_0='#skF_3' | r2_hidden('#skF_4', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_545, c_361])).
% 3.15/1.55  tff(c_599, plain, $false, inference(negUnitSimplification, [status(thm)], [c_353, c_117, c_555])).
% 3.15/1.55  tff(c_600, plain, (k1_xboole_0='#skF_1' | k1_tarski('#skF_2')='#skF_1'), inference(splitRight, [status(thm)], [c_46])).
% 3.15/1.55  tff(c_606, plain, (k1_tarski('#skF_2')='#skF_1'), inference(splitLeft, [status(thm)], [c_600])).
% 3.15/1.55  tff(c_10, plain, (![A_5, B_6]: (r1_tarski(A_5, B_6) | k4_xboole_0(A_5, B_6)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.15/1.55  tff(c_44, plain, (~r1_tarski('#skF_1', k1_tarski('#skF_2')) | r1_tarski('#skF_3', k1_tarski('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.15/1.55  tff(c_186, plain, (~r1_tarski('#skF_1', k1_tarski('#skF_2'))), inference(splitLeft, [status(thm)], [c_44])).
% 3.15/1.55  tff(c_190, plain, (k4_xboole_0('#skF_1', k1_tarski('#skF_2'))!=k1_xboole_0), inference(resolution, [status(thm)], [c_10, c_186])).
% 3.15/1.55  tff(c_607, plain, (k4_xboole_0('#skF_1', '#skF_1')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_606, c_190])).
% 3.15/1.55  tff(c_611, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_160, c_607])).
% 3.15/1.55  tff(c_612, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_600])).
% 3.15/1.55  tff(c_18, plain, (![A_10]: (k4_xboole_0(k1_xboole_0, A_10)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.15/1.55  tff(c_622, plain, (![A_10]: (k4_xboole_0('#skF_1', A_10)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_612, c_612, c_18])).
% 3.15/1.55  tff(c_616, plain, (k4_xboole_0('#skF_1', k1_tarski('#skF_2'))!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_612, c_190])).
% 3.15/1.55  tff(c_786, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_622, c_616])).
% 3.15/1.55  tff(c_787, plain, (r1_tarski('#skF_3', k1_tarski('#skF_4'))), inference(splitRight, [status(thm)], [c_44])).
% 3.15/1.55  tff(c_814, plain, (![B_78, A_79]: (B_78=A_79 | ~r1_tarski(B_78, A_79) | ~r1_tarski(A_79, B_78))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.15/1.55  tff(c_818, plain, (k1_tarski('#skF_4')='#skF_3' | ~r1_tarski(k1_tarski('#skF_4'), '#skF_3')), inference(resolution, [status(thm)], [c_787, c_814])).
% 3.15/1.55  tff(c_828, plain, (~r1_tarski(k1_tarski('#skF_4'), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_147, c_818])).
% 3.15/1.55  tff(c_841, plain, (~r2_hidden('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_32, c_828])).
% 3.15/1.55  tff(c_1103, plain, (![A_96, B_97]: (k4_xboole_0(k1_tarski(A_96), B_97)=k1_tarski(A_96) | r2_hidden(A_96, B_97))), inference(resolution, [status(thm)], [c_120, c_20])).
% 3.15/1.55  tff(c_1115, plain, (![A_96, B_97]: (k4_xboole_0(k1_tarski(A_96), k1_tarski(A_96))=k3_xboole_0(k1_tarski(A_96), B_97) | r2_hidden(A_96, B_97))), inference(superposition, [status(thm), theory('equality')], [c_1103, c_16])).
% 3.15/1.55  tff(c_1229, plain, (![A_100, B_101]: (k3_xboole_0(k1_tarski(A_100), B_101)=k1_xboole_0 | r2_hidden(A_100, B_101))), inference(demodulation, [status(thm), theory('equality')], [c_160, c_1115])).
% 3.15/1.55  tff(c_1276, plain, (![B_102, A_103]: (k3_xboole_0(B_102, k1_tarski(A_103))=k1_xboole_0 | r2_hidden(A_103, B_102))), inference(superposition, [status(thm), theory('equality')], [c_1229, c_2])).
% 3.15/1.55  tff(c_792, plain, (k4_xboole_0('#skF_3', k1_tarski('#skF_4'))=k1_xboole_0), inference(resolution, [status(thm)], [c_787, c_12])).
% 3.15/1.55  tff(c_852, plain, (![A_80, B_81]: (k4_xboole_0(A_80, k4_xboole_0(A_80, B_81))=k3_xboole_0(A_80, B_81))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.15/1.55  tff(c_874, plain, (k3_xboole_0('#skF_3', k1_tarski('#skF_4'))=k4_xboole_0('#skF_3', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_792, c_852])).
% 3.15/1.55  tff(c_891, plain, (k3_xboole_0('#skF_3', k1_tarski('#skF_4'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_14, c_874])).
% 3.15/1.55  tff(c_1296, plain, (k1_xboole_0='#skF_3' | r2_hidden('#skF_4', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1276, c_891])).
% 3.15/1.55  tff(c_1342, plain, $false, inference(negUnitSimplification, [status(thm)], [c_841, c_117, c_1296])).
% 3.15/1.55  tff(c_1344, plain, (k1_tarski('#skF_4')='#skF_3'), inference(splitRight, [status(thm)], [c_36])).
% 3.15/1.55  tff(c_38, plain, (k1_tarski('#skF_2')='#skF_1' | k1_xboole_0='#skF_1' | k1_tarski('#skF_4')!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.15/1.55  tff(c_1497, plain, (k1_tarski('#skF_2')='#skF_1' | k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_1344, c_38])).
% 3.15/1.55  tff(c_1498, plain, (k1_xboole_0='#skF_1'), inference(splitLeft, [status(thm)], [c_1497])).
% 3.15/1.55  tff(c_1505, plain, (![A_10]: (k4_xboole_0('#skF_1', A_10)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1498, c_1498, c_18])).
% 3.15/1.55  tff(c_1343, plain, (~r1_tarski('#skF_1', k1_tarski('#skF_2'))), inference(splitRight, [status(thm)], [c_36])).
% 3.15/1.55  tff(c_1364, plain, (k4_xboole_0('#skF_1', k1_tarski('#skF_2'))!=k1_xboole_0), inference(resolution, [status(thm)], [c_10, c_1343])).
% 3.15/1.55  tff(c_1501, plain, (k4_xboole_0('#skF_1', k1_tarski('#skF_2'))!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_1498, c_1364])).
% 3.15/1.55  tff(c_1655, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1505, c_1501])).
% 3.15/1.55  tff(c_1656, plain, (k1_tarski('#skF_2')='#skF_1'), inference(splitRight, [status(thm)], [c_1497])).
% 3.15/1.55  tff(c_1658, plain, (k4_xboole_0('#skF_1', '#skF_1')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_1656, c_1364])).
% 3.15/1.55  tff(c_1662, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1389, c_1658])).
% 3.15/1.55  tff(c_1664, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_40])).
% 3.15/1.55  tff(c_42, plain, (k1_tarski('#skF_2')='#skF_1' | k1_xboole_0='#skF_1' | k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.15/1.55  tff(c_1710, plain, (k1_tarski('#skF_2')='#skF_1' | '#skF_3'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_1664, c_1664, c_42])).
% 3.15/1.55  tff(c_1711, plain, ('#skF_3'='#skF_1'), inference(splitLeft, [status(thm)], [c_1710])).
% 3.15/1.55  tff(c_1666, plain, (![A_10]: (k4_xboole_0('#skF_3', A_10)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1664, c_1664, c_18])).
% 3.15/1.55  tff(c_1713, plain, (![A_10]: (k4_xboole_0('#skF_1', A_10)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1711, c_1711, c_1666])).
% 3.15/1.55  tff(c_1715, plain, (k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_1711, c_1664])).
% 3.15/1.55  tff(c_1777, plain, (![A_136, B_137]: (r1_tarski(A_136, B_137) | k4_xboole_0(A_136, B_137)!='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1715, c_10])).
% 3.15/1.55  tff(c_1663, plain, (~r1_tarski('#skF_1', k1_tarski('#skF_2'))), inference(splitRight, [status(thm)], [c_40])).
% 3.15/1.55  tff(c_1780, plain, (k4_xboole_0('#skF_1', k1_tarski('#skF_2'))!='#skF_1'), inference(resolution, [status(thm)], [c_1777, c_1663])).
% 3.15/1.55  tff(c_1784, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1713, c_1780])).
% 3.15/1.55  tff(c_1785, plain, (k1_tarski('#skF_2')='#skF_1'), inference(splitRight, [status(thm)], [c_1710])).
% 3.15/1.55  tff(c_1787, plain, (~r1_tarski('#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1785, c_1663])).
% 3.15/1.55  tff(c_1790, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8, c_1787])).
% 3.15/1.55  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.15/1.55  
% 3.15/1.55  Inference rules
% 3.15/1.55  ----------------------
% 3.15/1.55  #Ref     : 0
% 3.15/1.55  #Sup     : 402
% 3.15/1.55  #Fact    : 0
% 3.15/1.55  #Define  : 0
% 3.15/1.55  #Split   : 8
% 3.15/1.55  #Chain   : 0
% 3.15/1.55  #Close   : 0
% 3.15/1.55  
% 3.15/1.55  Ordering : KBO
% 3.15/1.55  
% 3.15/1.55  Simplification rules
% 3.15/1.55  ----------------------
% 3.15/1.55  #Subsume      : 11
% 3.15/1.55  #Demod        : 161
% 3.15/1.55  #Tautology    : 257
% 3.15/1.55  #SimpNegUnit  : 9
% 3.15/1.55  #BackRed      : 27
% 3.15/1.55  
% 3.15/1.55  #Partial instantiations: 0
% 3.15/1.55  #Strategies tried      : 1
% 3.15/1.55  
% 3.15/1.55  Timing (in seconds)
% 3.15/1.55  ----------------------
% 3.15/1.55  Preprocessing        : 0.31
% 3.15/1.55  Parsing              : 0.17
% 3.15/1.55  CNF conversion       : 0.02
% 3.15/1.55  Main loop            : 0.44
% 3.15/1.55  Inferencing          : 0.17
% 3.15/1.55  Reduction            : 0.14
% 3.15/1.55  Demodulation         : 0.10
% 3.15/1.55  BG Simplification    : 0.02
% 3.15/1.55  Subsumption          : 0.07
% 3.15/1.55  Abstraction          : 0.02
% 3.15/1.55  MUC search           : 0.00
% 3.15/1.55  Cooper               : 0.00
% 3.15/1.55  Total                : 0.79
% 3.15/1.55  Index Insertion      : 0.00
% 3.15/1.55  Index Deletion       : 0.00
% 3.15/1.55  Index Matching       : 0.00
% 3.15/1.55  BG Taut test         : 0.00
%------------------------------------------------------------------------------

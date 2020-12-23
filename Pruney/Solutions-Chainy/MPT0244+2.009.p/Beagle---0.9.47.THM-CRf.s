%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:49:57 EST 2020

% Result     : Theorem 3.36s
% Output     : CNFRefutation 3.36s
% Verified   : 
% Statistics : Number of formulae       :  147 ( 553 expanded)
%              Number of leaves         :   26 ( 175 expanded)
%              Depth                    :   13
%              Number of atoms          :  204 (1122 expanded)
%              Number of equality atoms :   98 ( 550 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_2 > #skF_1

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

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

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

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_49,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_53,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_81,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_tarski(A,k1_tarski(B))
      <=> ( A = k1_xboole_0
          | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_zfmisc_1)).

tff(f_74,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_64,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(f_57,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

tff(c_12,plain,(
    ! [B_7] : r1_tarski(B_7,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_92,plain,(
    ! [A_36,B_37] :
      ( k4_xboole_0(A_36,B_37) = k1_xboole_0
      | ~ r1_tarski(A_36,B_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_104,plain,(
    ! [B_7] : k4_xboole_0(B_7,B_7) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_12,c_92])).

tff(c_48,plain,
    ( ~ r1_tarski('#skF_4',k1_tarski('#skF_5'))
    | k1_xboole_0 != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_67,plain,(
    k1_xboole_0 != '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_42,plain,(
    ! [A_23,B_24] :
      ( r1_tarski(k1_tarski(A_23),B_24)
      | ~ r2_hidden(A_23,B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_44,plain,
    ( ~ r1_tarski('#skF_4',k1_tarski('#skF_5'))
    | k1_tarski('#skF_7') != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_127,plain,(
    k1_tarski('#skF_7') != '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_44])).

tff(c_54,plain,
    ( k1_tarski('#skF_5') = '#skF_4'
    | k1_xboole_0 = '#skF_4'
    | r1_tarski('#skF_6',k1_tarski('#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_205,plain,(
    r1_tarski('#skF_6',k1_tarski('#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_54])).

tff(c_8,plain,(
    ! [B_7,A_6] :
      ( B_7 = A_6
      | ~ r1_tarski(B_7,A_6)
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_207,plain,
    ( k1_tarski('#skF_7') = '#skF_6'
    | ~ r1_tarski(k1_tarski('#skF_7'),'#skF_6') ),
    inference(resolution,[status(thm)],[c_205,c_8])).

tff(c_213,plain,(
    ~ r1_tarski(k1_tarski('#skF_7'),'#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_127,c_207])).

tff(c_222,plain,(
    ~ r2_hidden('#skF_7','#skF_6') ),
    inference(resolution,[status(thm)],[c_42,c_213])).

tff(c_152,plain,(
    ! [A_49,B_50] :
      ( r2_hidden('#skF_1'(A_49,B_50),B_50)
      | r1_xboole_0(A_49,B_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_22,plain,(
    ! [C_16,A_12] :
      ( C_16 = A_12
      | ~ r2_hidden(C_16,k1_tarski(A_12)) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_231,plain,(
    ! [A_61,A_62] :
      ( '#skF_1'(A_61,k1_tarski(A_62)) = A_62
      | r1_xboole_0(A_61,k1_tarski(A_62)) ) ),
    inference(resolution,[status(thm)],[c_152,c_22])).

tff(c_18,plain,(
    ! [A_10,B_11] :
      ( k4_xboole_0(A_10,B_11) = A_10
      | ~ r1_xboole_0(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_334,plain,(
    ! [A_81,A_82] :
      ( k4_xboole_0(A_81,k1_tarski(A_82)) = A_81
      | '#skF_1'(A_81,k1_tarski(A_82)) = A_82 ) ),
    inference(resolution,[status(thm)],[c_231,c_18])).

tff(c_16,plain,(
    ! [A_8,B_9] :
      ( k4_xboole_0(A_8,B_9) = k1_xboole_0
      | ~ r1_tarski(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_214,plain,(
    k4_xboole_0('#skF_6',k1_tarski('#skF_7')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_205,c_16])).

tff(c_345,plain,
    ( k1_xboole_0 = '#skF_6'
    | '#skF_1'('#skF_6',k1_tarski('#skF_7')) = '#skF_7' ),
    inference(superposition,[status(thm),theory(equality)],[c_334,c_214])).

tff(c_377,plain,(
    '#skF_1'('#skF_6',k1_tarski('#skF_7')) = '#skF_7' ),
    inference(negUnitSimplification,[status(thm)],[c_67,c_345])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_399,plain,
    ( r2_hidden('#skF_7','#skF_6')
    | r1_xboole_0('#skF_6',k1_tarski('#skF_7')) ),
    inference(superposition,[status(thm),theory(equality)],[c_377,c_6])).

tff(c_403,plain,(
    r1_xboole_0('#skF_6',k1_tarski('#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_222,c_399])).

tff(c_411,plain,(
    k4_xboole_0('#skF_6',k1_tarski('#skF_7')) = '#skF_6' ),
    inference(resolution,[status(thm)],[c_403,c_18])).

tff(c_414,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_411,c_214])).

tff(c_416,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_67,c_414])).

tff(c_417,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_tarski('#skF_5') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_423,plain,(
    k1_tarski('#skF_5') = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_417])).

tff(c_14,plain,(
    ! [A_8,B_9] :
      ( r1_tarski(A_8,B_9)
      | k4_xboole_0(A_8,B_9) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_52,plain,
    ( ~ r1_tarski('#skF_4',k1_tarski('#skF_5'))
    | r1_tarski('#skF_6',k1_tarski('#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_141,plain,(
    ~ r1_tarski('#skF_4',k1_tarski('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_145,plain,(
    k4_xboole_0('#skF_4',k1_tarski('#skF_5')) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_14,c_141])).

tff(c_424,plain,(
    k4_xboole_0('#skF_4','#skF_4') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_423,c_145])).

tff(c_428,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_424])).

tff(c_429,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_417])).

tff(c_434,plain,(
    ! [B_7] : k4_xboole_0(B_7,B_7) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_429,c_104])).

tff(c_433,plain,(
    k4_xboole_0('#skF_4',k1_tarski('#skF_5')) != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_429,c_145])).

tff(c_516,plain,(
    ! [A_96,A_97] :
      ( '#skF_1'(A_96,k1_tarski(A_97)) = A_97
      | r1_xboole_0(A_96,k1_tarski(A_97)) ) ),
    inference(resolution,[status(thm)],[c_152,c_22])).

tff(c_601,plain,(
    ! [A_114,A_115] :
      ( k4_xboole_0(A_114,k1_tarski(A_115)) = A_114
      | '#skF_1'(A_114,k1_tarski(A_115)) = A_115 ) ),
    inference(resolution,[status(thm)],[c_516,c_18])).

tff(c_640,plain,(
    '#skF_1'('#skF_4',k1_tarski('#skF_5')) = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_601,c_433])).

tff(c_651,plain,
    ( r2_hidden('#skF_5','#skF_4')
    | r1_xboole_0('#skF_4',k1_tarski('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_640,c_6])).

tff(c_674,plain,(
    r1_xboole_0('#skF_4',k1_tarski('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_651])).

tff(c_679,plain,(
    k4_xboole_0('#skF_4',k1_tarski('#skF_5')) = '#skF_4' ),
    inference(resolution,[status(thm)],[c_674,c_18])).

tff(c_684,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_433,c_679])).

tff(c_685,plain,(
    r2_hidden('#skF_5','#skF_4') ),
    inference(splitRight,[status(thm)],[c_651])).

tff(c_20,plain,(
    ! [A_10,B_11] :
      ( r1_xboole_0(A_10,B_11)
      | k4_xboole_0(A_10,B_11) != A_10 ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_201,plain,(
    ! [A_58,B_59,C_60] :
      ( ~ r1_xboole_0(A_58,B_59)
      | ~ r2_hidden(C_60,B_59)
      | ~ r2_hidden(C_60,A_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_204,plain,(
    ! [C_60,B_11,A_10] :
      ( ~ r2_hidden(C_60,B_11)
      | ~ r2_hidden(C_60,A_10)
      | k4_xboole_0(A_10,B_11) != A_10 ) ),
    inference(resolution,[status(thm)],[c_20,c_201])).

tff(c_708,plain,(
    ! [A_119] :
      ( ~ r2_hidden('#skF_5',A_119)
      | k4_xboole_0(A_119,'#skF_4') != A_119 ) ),
    inference(resolution,[status(thm)],[c_685,c_204])).

tff(c_711,plain,(
    k4_xboole_0('#skF_4','#skF_4') != '#skF_4' ),
    inference(resolution,[status(thm)],[c_685,c_708])).

tff(c_719,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_434,c_711])).

tff(c_720,plain,(
    r1_tarski('#skF_6',k1_tarski('#skF_7')) ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_723,plain,
    ( k1_tarski('#skF_7') = '#skF_6'
    | ~ r1_tarski(k1_tarski('#skF_7'),'#skF_6') ),
    inference(resolution,[status(thm)],[c_720,c_8])).

tff(c_729,plain,(
    ~ r1_tarski(k1_tarski('#skF_7'),'#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_127,c_723])).

tff(c_745,plain,(
    ~ r2_hidden('#skF_7','#skF_6') ),
    inference(resolution,[status(thm)],[c_42,c_729])).

tff(c_770,plain,(
    ! [A_122,B_123] :
      ( r2_hidden('#skF_1'(A_122,B_123),B_123)
      | r1_xboole_0(A_122,B_123) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_865,plain,(
    ! [A_140,A_141] :
      ( '#skF_1'(A_140,k1_tarski(A_141)) = A_141
      | r1_xboole_0(A_140,k1_tarski(A_141)) ) ),
    inference(resolution,[status(thm)],[c_770,c_22])).

tff(c_939,plain,(
    ! [A_152,A_153] :
      ( k4_xboole_0(A_152,k1_tarski(A_153)) = A_152
      | '#skF_1'(A_152,k1_tarski(A_153)) = A_153 ) ),
    inference(resolution,[status(thm)],[c_865,c_18])).

tff(c_730,plain,(
    k4_xboole_0('#skF_6',k1_tarski('#skF_7')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_720,c_16])).

tff(c_956,plain,
    ( k1_xboole_0 = '#skF_6'
    | '#skF_1'('#skF_6',k1_tarski('#skF_7')) = '#skF_7' ),
    inference(superposition,[status(thm),theory(equality)],[c_939,c_730])).

tff(c_984,plain,(
    '#skF_1'('#skF_6',k1_tarski('#skF_7')) = '#skF_7' ),
    inference(negUnitSimplification,[status(thm)],[c_67,c_956])).

tff(c_996,plain,
    ( r2_hidden('#skF_7','#skF_6')
    | r1_xboole_0('#skF_6',k1_tarski('#skF_7')) ),
    inference(superposition,[status(thm),theory(equality)],[c_984,c_6])).

tff(c_1000,plain,(
    r1_xboole_0('#skF_6',k1_tarski('#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_745,c_996])).

tff(c_1008,plain,(
    k4_xboole_0('#skF_6',k1_tarski('#skF_7')) = '#skF_6' ),
    inference(resolution,[status(thm)],[c_1000,c_18])).

tff(c_1010,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1008,c_730])).

tff(c_1012,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_67,c_1010])).

tff(c_1014,plain,(
    k1_tarski('#skF_7') = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_46,plain,
    ( k1_tarski('#skF_5') = '#skF_4'
    | k1_xboole_0 = '#skF_4'
    | k1_tarski('#skF_7') != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_1085,plain,
    ( k1_tarski('#skF_5') = '#skF_4'
    | k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1014,c_46])).

tff(c_1086,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_1085])).

tff(c_1088,plain,(
    ! [B_7] : k4_xboole_0(B_7,B_7) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1086,c_104])).

tff(c_1013,plain,(
    ~ r1_tarski('#skF_4',k1_tarski('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_1034,plain,(
    k4_xboole_0('#skF_4',k1_tarski('#skF_5')) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_14,c_1013])).

tff(c_1087,plain,(
    k4_xboole_0('#skF_4',k1_tarski('#skF_5')) != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1086,c_1034])).

tff(c_1150,plain,(
    ! [A_166,B_167] :
      ( r2_hidden('#skF_1'(A_166,B_167),B_167)
      | r1_xboole_0(A_166,B_167) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_1391,plain,(
    ! [A_190,A_191] :
      ( '#skF_1'(A_190,k1_tarski(A_191)) = A_191
      | r1_xboole_0(A_190,k1_tarski(A_191)) ) ),
    inference(resolution,[status(thm)],[c_1150,c_22])).

tff(c_1647,plain,(
    ! [A_214,A_215] :
      ( k4_xboole_0(A_214,k1_tarski(A_215)) = A_214
      | '#skF_1'(A_214,k1_tarski(A_215)) = A_215 ) ),
    inference(resolution,[status(thm)],[c_1391,c_18])).

tff(c_1707,plain,(
    '#skF_1'('#skF_4',k1_tarski('#skF_5')) = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_1647,c_1087])).

tff(c_1717,plain,
    ( r2_hidden('#skF_5','#skF_4')
    | r1_xboole_0('#skF_4',k1_tarski('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1707,c_6])).

tff(c_1778,plain,(
    r1_xboole_0('#skF_4',k1_tarski('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_1717])).

tff(c_1784,plain,(
    k4_xboole_0('#skF_4',k1_tarski('#skF_5')) = '#skF_4' ),
    inference(resolution,[status(thm)],[c_1778,c_18])).

tff(c_1789,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1087,c_1784])).

tff(c_1790,plain,(
    r2_hidden('#skF_5','#skF_4') ),
    inference(splitRight,[status(thm)],[c_1717])).

tff(c_1209,plain,(
    ! [A_174,B_175,C_176] :
      ( ~ r1_xboole_0(A_174,B_175)
      | ~ r2_hidden(C_176,B_175)
      | ~ r2_hidden(C_176,A_174) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_1218,plain,(
    ! [C_176,B_11,A_10] :
      ( ~ r2_hidden(C_176,B_11)
      | ~ r2_hidden(C_176,A_10)
      | k4_xboole_0(A_10,B_11) != A_10 ) ),
    inference(resolution,[status(thm)],[c_20,c_1209])).

tff(c_1838,plain,(
    ! [A_225] :
      ( ~ r2_hidden('#skF_5',A_225)
      | k4_xboole_0(A_225,'#skF_4') != A_225 ) ),
    inference(resolution,[status(thm)],[c_1790,c_1218])).

tff(c_1841,plain,(
    k4_xboole_0('#skF_4','#skF_4') != '#skF_4' ),
    inference(resolution,[status(thm)],[c_1790,c_1838])).

tff(c_1849,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1088,c_1841])).

tff(c_1850,plain,(
    k1_tarski('#skF_5') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_1085])).

tff(c_1852,plain,(
    k4_xboole_0('#skF_4','#skF_4') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1850,c_1034])).

tff(c_1856,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_1852])).

tff(c_1858,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_50,plain,
    ( k1_tarski('#skF_5') = '#skF_4'
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_1870,plain,
    ( k1_tarski('#skF_5') = '#skF_4'
    | '#skF_6' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1858,c_1858,c_50])).

tff(c_1871,plain,(
    '#skF_6' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_1870])).

tff(c_1872,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1871,c_1858])).

tff(c_1898,plain,(
    ! [A_236,B_237] :
      ( k4_xboole_0(A_236,B_237) = '#skF_4'
      | ~ r1_tarski(A_236,B_237) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1872,c_16])).

tff(c_1906,plain,(
    ! [B_7] : k4_xboole_0(B_7,B_7) = '#skF_4' ),
    inference(resolution,[status(thm)],[c_12,c_1898])).

tff(c_1927,plain,(
    ! [A_241,B_242] :
      ( r1_tarski(A_241,B_242)
      | k4_xboole_0(A_241,B_242) != '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1872,c_14])).

tff(c_1857,plain,(
    ~ r1_tarski('#skF_4',k1_tarski('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_1940,plain,(
    k4_xboole_0('#skF_4',k1_tarski('#skF_5')) != '#skF_4' ),
    inference(resolution,[status(thm)],[c_1927,c_1857])).

tff(c_1941,plain,(
    ! [A_243,B_244] :
      ( r2_hidden('#skF_1'(A_243,B_244),B_244)
      | r1_xboole_0(A_243,B_244) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_2016,plain,(
    ! [A_259,A_260] :
      ( '#skF_1'(A_259,k1_tarski(A_260)) = A_260
      | r1_xboole_0(A_259,k1_tarski(A_260)) ) ),
    inference(resolution,[status(thm)],[c_1941,c_22])).

tff(c_2100,plain,(
    ! [A_277,A_278] :
      ( k4_xboole_0(A_277,k1_tarski(A_278)) = A_277
      | '#skF_1'(A_277,k1_tarski(A_278)) = A_278 ) ),
    inference(resolution,[status(thm)],[c_2016,c_18])).

tff(c_2136,plain,(
    '#skF_1'('#skF_4',k1_tarski('#skF_5')) = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_2100,c_1940])).

tff(c_2144,plain,
    ( r2_hidden('#skF_5','#skF_4')
    | r1_xboole_0('#skF_4',k1_tarski('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_2136,c_6])).

tff(c_2171,plain,(
    r1_xboole_0('#skF_4',k1_tarski('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_2144])).

tff(c_2176,plain,(
    k4_xboole_0('#skF_4',k1_tarski('#skF_5')) = '#skF_4' ),
    inference(resolution,[status(thm)],[c_2171,c_18])).

tff(c_2181,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1940,c_2176])).

tff(c_2182,plain,(
    r2_hidden('#skF_5','#skF_4') ),
    inference(splitRight,[status(thm)],[c_2144])).

tff(c_2003,plain,(
    ! [A_253,B_254,C_255] :
      ( ~ r1_xboole_0(A_253,B_254)
      | ~ r2_hidden(C_255,B_254)
      | ~ r2_hidden(C_255,A_253) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_2006,plain,(
    ! [C_255,B_11,A_10] :
      ( ~ r2_hidden(C_255,B_11)
      | ~ r2_hidden(C_255,A_10)
      | k4_xboole_0(A_10,B_11) != A_10 ) ),
    inference(resolution,[status(thm)],[c_20,c_2003])).

tff(c_2196,plain,(
    ! [A_282] :
      ( ~ r2_hidden('#skF_5',A_282)
      | k4_xboole_0(A_282,'#skF_4') != A_282 ) ),
    inference(resolution,[status(thm)],[c_2182,c_2006])).

tff(c_2199,plain,(
    k4_xboole_0('#skF_4','#skF_4') != '#skF_4' ),
    inference(resolution,[status(thm)],[c_2182,c_2196])).

tff(c_2207,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1906,c_2199])).

tff(c_2208,plain,(
    k1_tarski('#skF_5') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_1870])).

tff(c_2210,plain,(
    ~ r1_tarski('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2208,c_1857])).

tff(c_2213,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_2210])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n021.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 13:27:34 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.18/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.36/1.57  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.36/1.59  
% 3.36/1.59  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.36/1.59  %$ r2_hidden > r1_xboole_0 > r1_tarski > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_2 > #skF_1
% 3.36/1.59  
% 3.36/1.59  %Foreground sorts:
% 3.36/1.59  
% 3.36/1.59  
% 3.36/1.59  %Background operators:
% 3.36/1.59  
% 3.36/1.59  
% 3.36/1.59  %Foreground operators:
% 3.36/1.59  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.36/1.59  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.36/1.59  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.36/1.59  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.36/1.59  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.36/1.59  tff('#skF_7', type, '#skF_7': $i).
% 3.36/1.59  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.36/1.59  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.36/1.59  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.36/1.59  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.36/1.59  tff('#skF_5', type, '#skF_5': $i).
% 3.36/1.59  tff('#skF_6', type, '#skF_6': $i).
% 3.36/1.59  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.36/1.59  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.36/1.59  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.36/1.59  tff('#skF_4', type, '#skF_4': $i).
% 3.36/1.59  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.36/1.59  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.36/1.59  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.36/1.59  
% 3.36/1.61  tff(f_49, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.36/1.61  tff(f_53, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 3.36/1.61  tff(f_81, negated_conjecture, ~(![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_zfmisc_1)).
% 3.36/1.61  tff(f_74, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 3.36/1.61  tff(f_43, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 3.36/1.61  tff(f_64, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 3.36/1.61  tff(f_57, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 3.36/1.61  tff(c_12, plain, (![B_7]: (r1_tarski(B_7, B_7))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.36/1.61  tff(c_92, plain, (![A_36, B_37]: (k4_xboole_0(A_36, B_37)=k1_xboole_0 | ~r1_tarski(A_36, B_37))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.36/1.61  tff(c_104, plain, (![B_7]: (k4_xboole_0(B_7, B_7)=k1_xboole_0)), inference(resolution, [status(thm)], [c_12, c_92])).
% 3.36/1.61  tff(c_48, plain, (~r1_tarski('#skF_4', k1_tarski('#skF_5')) | k1_xboole_0!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.36/1.61  tff(c_67, plain, (k1_xboole_0!='#skF_6'), inference(splitLeft, [status(thm)], [c_48])).
% 3.36/1.61  tff(c_42, plain, (![A_23, B_24]: (r1_tarski(k1_tarski(A_23), B_24) | ~r2_hidden(A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.36/1.61  tff(c_44, plain, (~r1_tarski('#skF_4', k1_tarski('#skF_5')) | k1_tarski('#skF_7')!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.36/1.61  tff(c_127, plain, (k1_tarski('#skF_7')!='#skF_6'), inference(splitLeft, [status(thm)], [c_44])).
% 3.36/1.61  tff(c_54, plain, (k1_tarski('#skF_5')='#skF_4' | k1_xboole_0='#skF_4' | r1_tarski('#skF_6', k1_tarski('#skF_7'))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.36/1.61  tff(c_205, plain, (r1_tarski('#skF_6', k1_tarski('#skF_7'))), inference(splitLeft, [status(thm)], [c_54])).
% 3.36/1.61  tff(c_8, plain, (![B_7, A_6]: (B_7=A_6 | ~r1_tarski(B_7, A_6) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.36/1.61  tff(c_207, plain, (k1_tarski('#skF_7')='#skF_6' | ~r1_tarski(k1_tarski('#skF_7'), '#skF_6')), inference(resolution, [status(thm)], [c_205, c_8])).
% 3.36/1.61  tff(c_213, plain, (~r1_tarski(k1_tarski('#skF_7'), '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_127, c_207])).
% 3.36/1.61  tff(c_222, plain, (~r2_hidden('#skF_7', '#skF_6')), inference(resolution, [status(thm)], [c_42, c_213])).
% 3.36/1.61  tff(c_152, plain, (![A_49, B_50]: (r2_hidden('#skF_1'(A_49, B_50), B_50) | r1_xboole_0(A_49, B_50))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.36/1.61  tff(c_22, plain, (![C_16, A_12]: (C_16=A_12 | ~r2_hidden(C_16, k1_tarski(A_12)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.36/1.61  tff(c_231, plain, (![A_61, A_62]: ('#skF_1'(A_61, k1_tarski(A_62))=A_62 | r1_xboole_0(A_61, k1_tarski(A_62)))), inference(resolution, [status(thm)], [c_152, c_22])).
% 3.36/1.61  tff(c_18, plain, (![A_10, B_11]: (k4_xboole_0(A_10, B_11)=A_10 | ~r1_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.36/1.61  tff(c_334, plain, (![A_81, A_82]: (k4_xboole_0(A_81, k1_tarski(A_82))=A_81 | '#skF_1'(A_81, k1_tarski(A_82))=A_82)), inference(resolution, [status(thm)], [c_231, c_18])).
% 3.36/1.61  tff(c_16, plain, (![A_8, B_9]: (k4_xboole_0(A_8, B_9)=k1_xboole_0 | ~r1_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.36/1.61  tff(c_214, plain, (k4_xboole_0('#skF_6', k1_tarski('#skF_7'))=k1_xboole_0), inference(resolution, [status(thm)], [c_205, c_16])).
% 3.36/1.61  tff(c_345, plain, (k1_xboole_0='#skF_6' | '#skF_1'('#skF_6', k1_tarski('#skF_7'))='#skF_7'), inference(superposition, [status(thm), theory('equality')], [c_334, c_214])).
% 3.36/1.61  tff(c_377, plain, ('#skF_1'('#skF_6', k1_tarski('#skF_7'))='#skF_7'), inference(negUnitSimplification, [status(thm)], [c_67, c_345])).
% 3.36/1.61  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.36/1.61  tff(c_399, plain, (r2_hidden('#skF_7', '#skF_6') | r1_xboole_0('#skF_6', k1_tarski('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_377, c_6])).
% 3.36/1.61  tff(c_403, plain, (r1_xboole_0('#skF_6', k1_tarski('#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_222, c_399])).
% 3.36/1.61  tff(c_411, plain, (k4_xboole_0('#skF_6', k1_tarski('#skF_7'))='#skF_6'), inference(resolution, [status(thm)], [c_403, c_18])).
% 3.36/1.61  tff(c_414, plain, (k1_xboole_0='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_411, c_214])).
% 3.36/1.61  tff(c_416, plain, $false, inference(negUnitSimplification, [status(thm)], [c_67, c_414])).
% 3.36/1.61  tff(c_417, plain, (k1_xboole_0='#skF_4' | k1_tarski('#skF_5')='#skF_4'), inference(splitRight, [status(thm)], [c_54])).
% 3.36/1.61  tff(c_423, plain, (k1_tarski('#skF_5')='#skF_4'), inference(splitLeft, [status(thm)], [c_417])).
% 3.36/1.61  tff(c_14, plain, (![A_8, B_9]: (r1_tarski(A_8, B_9) | k4_xboole_0(A_8, B_9)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.36/1.61  tff(c_52, plain, (~r1_tarski('#skF_4', k1_tarski('#skF_5')) | r1_tarski('#skF_6', k1_tarski('#skF_7'))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.36/1.61  tff(c_141, plain, (~r1_tarski('#skF_4', k1_tarski('#skF_5'))), inference(splitLeft, [status(thm)], [c_52])).
% 3.36/1.61  tff(c_145, plain, (k4_xboole_0('#skF_4', k1_tarski('#skF_5'))!=k1_xboole_0), inference(resolution, [status(thm)], [c_14, c_141])).
% 3.36/1.61  tff(c_424, plain, (k4_xboole_0('#skF_4', '#skF_4')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_423, c_145])).
% 3.36/1.61  tff(c_428, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_104, c_424])).
% 3.36/1.61  tff(c_429, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_417])).
% 3.36/1.61  tff(c_434, plain, (![B_7]: (k4_xboole_0(B_7, B_7)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_429, c_104])).
% 3.36/1.61  tff(c_433, plain, (k4_xboole_0('#skF_4', k1_tarski('#skF_5'))!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_429, c_145])).
% 3.36/1.61  tff(c_516, plain, (![A_96, A_97]: ('#skF_1'(A_96, k1_tarski(A_97))=A_97 | r1_xboole_0(A_96, k1_tarski(A_97)))), inference(resolution, [status(thm)], [c_152, c_22])).
% 3.36/1.61  tff(c_601, plain, (![A_114, A_115]: (k4_xboole_0(A_114, k1_tarski(A_115))=A_114 | '#skF_1'(A_114, k1_tarski(A_115))=A_115)), inference(resolution, [status(thm)], [c_516, c_18])).
% 3.36/1.61  tff(c_640, plain, ('#skF_1'('#skF_4', k1_tarski('#skF_5'))='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_601, c_433])).
% 3.36/1.61  tff(c_651, plain, (r2_hidden('#skF_5', '#skF_4') | r1_xboole_0('#skF_4', k1_tarski('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_640, c_6])).
% 3.36/1.61  tff(c_674, plain, (r1_xboole_0('#skF_4', k1_tarski('#skF_5'))), inference(splitLeft, [status(thm)], [c_651])).
% 3.36/1.61  tff(c_679, plain, (k4_xboole_0('#skF_4', k1_tarski('#skF_5'))='#skF_4'), inference(resolution, [status(thm)], [c_674, c_18])).
% 3.36/1.61  tff(c_684, plain, $false, inference(negUnitSimplification, [status(thm)], [c_433, c_679])).
% 3.36/1.61  tff(c_685, plain, (r2_hidden('#skF_5', '#skF_4')), inference(splitRight, [status(thm)], [c_651])).
% 3.36/1.61  tff(c_20, plain, (![A_10, B_11]: (r1_xboole_0(A_10, B_11) | k4_xboole_0(A_10, B_11)!=A_10)), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.36/1.61  tff(c_201, plain, (![A_58, B_59, C_60]: (~r1_xboole_0(A_58, B_59) | ~r2_hidden(C_60, B_59) | ~r2_hidden(C_60, A_58))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.36/1.61  tff(c_204, plain, (![C_60, B_11, A_10]: (~r2_hidden(C_60, B_11) | ~r2_hidden(C_60, A_10) | k4_xboole_0(A_10, B_11)!=A_10)), inference(resolution, [status(thm)], [c_20, c_201])).
% 3.36/1.61  tff(c_708, plain, (![A_119]: (~r2_hidden('#skF_5', A_119) | k4_xboole_0(A_119, '#skF_4')!=A_119)), inference(resolution, [status(thm)], [c_685, c_204])).
% 3.36/1.61  tff(c_711, plain, (k4_xboole_0('#skF_4', '#skF_4')!='#skF_4'), inference(resolution, [status(thm)], [c_685, c_708])).
% 3.36/1.61  tff(c_719, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_434, c_711])).
% 3.36/1.61  tff(c_720, plain, (r1_tarski('#skF_6', k1_tarski('#skF_7'))), inference(splitRight, [status(thm)], [c_52])).
% 3.36/1.61  tff(c_723, plain, (k1_tarski('#skF_7')='#skF_6' | ~r1_tarski(k1_tarski('#skF_7'), '#skF_6')), inference(resolution, [status(thm)], [c_720, c_8])).
% 3.36/1.61  tff(c_729, plain, (~r1_tarski(k1_tarski('#skF_7'), '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_127, c_723])).
% 3.36/1.61  tff(c_745, plain, (~r2_hidden('#skF_7', '#skF_6')), inference(resolution, [status(thm)], [c_42, c_729])).
% 3.36/1.61  tff(c_770, plain, (![A_122, B_123]: (r2_hidden('#skF_1'(A_122, B_123), B_123) | r1_xboole_0(A_122, B_123))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.36/1.61  tff(c_865, plain, (![A_140, A_141]: ('#skF_1'(A_140, k1_tarski(A_141))=A_141 | r1_xboole_0(A_140, k1_tarski(A_141)))), inference(resolution, [status(thm)], [c_770, c_22])).
% 3.36/1.61  tff(c_939, plain, (![A_152, A_153]: (k4_xboole_0(A_152, k1_tarski(A_153))=A_152 | '#skF_1'(A_152, k1_tarski(A_153))=A_153)), inference(resolution, [status(thm)], [c_865, c_18])).
% 3.36/1.61  tff(c_730, plain, (k4_xboole_0('#skF_6', k1_tarski('#skF_7'))=k1_xboole_0), inference(resolution, [status(thm)], [c_720, c_16])).
% 3.36/1.61  tff(c_956, plain, (k1_xboole_0='#skF_6' | '#skF_1'('#skF_6', k1_tarski('#skF_7'))='#skF_7'), inference(superposition, [status(thm), theory('equality')], [c_939, c_730])).
% 3.36/1.61  tff(c_984, plain, ('#skF_1'('#skF_6', k1_tarski('#skF_7'))='#skF_7'), inference(negUnitSimplification, [status(thm)], [c_67, c_956])).
% 3.36/1.61  tff(c_996, plain, (r2_hidden('#skF_7', '#skF_6') | r1_xboole_0('#skF_6', k1_tarski('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_984, c_6])).
% 3.36/1.61  tff(c_1000, plain, (r1_xboole_0('#skF_6', k1_tarski('#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_745, c_996])).
% 3.36/1.61  tff(c_1008, plain, (k4_xboole_0('#skF_6', k1_tarski('#skF_7'))='#skF_6'), inference(resolution, [status(thm)], [c_1000, c_18])).
% 3.36/1.61  tff(c_1010, plain, (k1_xboole_0='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_1008, c_730])).
% 3.36/1.61  tff(c_1012, plain, $false, inference(negUnitSimplification, [status(thm)], [c_67, c_1010])).
% 3.36/1.61  tff(c_1014, plain, (k1_tarski('#skF_7')='#skF_6'), inference(splitRight, [status(thm)], [c_44])).
% 3.36/1.61  tff(c_46, plain, (k1_tarski('#skF_5')='#skF_4' | k1_xboole_0='#skF_4' | k1_tarski('#skF_7')!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.36/1.61  tff(c_1085, plain, (k1_tarski('#skF_5')='#skF_4' | k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_1014, c_46])).
% 3.36/1.61  tff(c_1086, plain, (k1_xboole_0='#skF_4'), inference(splitLeft, [status(thm)], [c_1085])).
% 3.36/1.61  tff(c_1088, plain, (![B_7]: (k4_xboole_0(B_7, B_7)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1086, c_104])).
% 3.36/1.61  tff(c_1013, plain, (~r1_tarski('#skF_4', k1_tarski('#skF_5'))), inference(splitRight, [status(thm)], [c_44])).
% 3.36/1.61  tff(c_1034, plain, (k4_xboole_0('#skF_4', k1_tarski('#skF_5'))!=k1_xboole_0), inference(resolution, [status(thm)], [c_14, c_1013])).
% 3.36/1.61  tff(c_1087, plain, (k4_xboole_0('#skF_4', k1_tarski('#skF_5'))!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_1086, c_1034])).
% 3.36/1.61  tff(c_1150, plain, (![A_166, B_167]: (r2_hidden('#skF_1'(A_166, B_167), B_167) | r1_xboole_0(A_166, B_167))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.36/1.61  tff(c_1391, plain, (![A_190, A_191]: ('#skF_1'(A_190, k1_tarski(A_191))=A_191 | r1_xboole_0(A_190, k1_tarski(A_191)))), inference(resolution, [status(thm)], [c_1150, c_22])).
% 3.36/1.61  tff(c_1647, plain, (![A_214, A_215]: (k4_xboole_0(A_214, k1_tarski(A_215))=A_214 | '#skF_1'(A_214, k1_tarski(A_215))=A_215)), inference(resolution, [status(thm)], [c_1391, c_18])).
% 3.36/1.61  tff(c_1707, plain, ('#skF_1'('#skF_4', k1_tarski('#skF_5'))='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_1647, c_1087])).
% 3.36/1.61  tff(c_1717, plain, (r2_hidden('#skF_5', '#skF_4') | r1_xboole_0('#skF_4', k1_tarski('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_1707, c_6])).
% 3.36/1.61  tff(c_1778, plain, (r1_xboole_0('#skF_4', k1_tarski('#skF_5'))), inference(splitLeft, [status(thm)], [c_1717])).
% 3.36/1.61  tff(c_1784, plain, (k4_xboole_0('#skF_4', k1_tarski('#skF_5'))='#skF_4'), inference(resolution, [status(thm)], [c_1778, c_18])).
% 3.36/1.61  tff(c_1789, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1087, c_1784])).
% 3.36/1.61  tff(c_1790, plain, (r2_hidden('#skF_5', '#skF_4')), inference(splitRight, [status(thm)], [c_1717])).
% 3.36/1.61  tff(c_1209, plain, (![A_174, B_175, C_176]: (~r1_xboole_0(A_174, B_175) | ~r2_hidden(C_176, B_175) | ~r2_hidden(C_176, A_174))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.36/1.61  tff(c_1218, plain, (![C_176, B_11, A_10]: (~r2_hidden(C_176, B_11) | ~r2_hidden(C_176, A_10) | k4_xboole_0(A_10, B_11)!=A_10)), inference(resolution, [status(thm)], [c_20, c_1209])).
% 3.36/1.61  tff(c_1838, plain, (![A_225]: (~r2_hidden('#skF_5', A_225) | k4_xboole_0(A_225, '#skF_4')!=A_225)), inference(resolution, [status(thm)], [c_1790, c_1218])).
% 3.36/1.61  tff(c_1841, plain, (k4_xboole_0('#skF_4', '#skF_4')!='#skF_4'), inference(resolution, [status(thm)], [c_1790, c_1838])).
% 3.36/1.61  tff(c_1849, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1088, c_1841])).
% 3.36/1.61  tff(c_1850, plain, (k1_tarski('#skF_5')='#skF_4'), inference(splitRight, [status(thm)], [c_1085])).
% 3.36/1.61  tff(c_1852, plain, (k4_xboole_0('#skF_4', '#skF_4')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_1850, c_1034])).
% 3.36/1.61  tff(c_1856, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_104, c_1852])).
% 3.36/1.61  tff(c_1858, plain, (k1_xboole_0='#skF_6'), inference(splitRight, [status(thm)], [c_48])).
% 3.36/1.61  tff(c_50, plain, (k1_tarski('#skF_5')='#skF_4' | k1_xboole_0='#skF_4' | k1_xboole_0!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.36/1.61  tff(c_1870, plain, (k1_tarski('#skF_5')='#skF_4' | '#skF_6'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_1858, c_1858, c_50])).
% 3.36/1.61  tff(c_1871, plain, ('#skF_6'='#skF_4'), inference(splitLeft, [status(thm)], [c_1870])).
% 3.36/1.61  tff(c_1872, plain, (k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_1871, c_1858])).
% 3.36/1.61  tff(c_1898, plain, (![A_236, B_237]: (k4_xboole_0(A_236, B_237)='#skF_4' | ~r1_tarski(A_236, B_237))), inference(demodulation, [status(thm), theory('equality')], [c_1872, c_16])).
% 3.36/1.61  tff(c_1906, plain, (![B_7]: (k4_xboole_0(B_7, B_7)='#skF_4')), inference(resolution, [status(thm)], [c_12, c_1898])).
% 3.36/1.61  tff(c_1927, plain, (![A_241, B_242]: (r1_tarski(A_241, B_242) | k4_xboole_0(A_241, B_242)!='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1872, c_14])).
% 3.36/1.61  tff(c_1857, plain, (~r1_tarski('#skF_4', k1_tarski('#skF_5'))), inference(splitRight, [status(thm)], [c_48])).
% 3.36/1.61  tff(c_1940, plain, (k4_xboole_0('#skF_4', k1_tarski('#skF_5'))!='#skF_4'), inference(resolution, [status(thm)], [c_1927, c_1857])).
% 3.36/1.61  tff(c_1941, plain, (![A_243, B_244]: (r2_hidden('#skF_1'(A_243, B_244), B_244) | r1_xboole_0(A_243, B_244))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.36/1.61  tff(c_2016, plain, (![A_259, A_260]: ('#skF_1'(A_259, k1_tarski(A_260))=A_260 | r1_xboole_0(A_259, k1_tarski(A_260)))), inference(resolution, [status(thm)], [c_1941, c_22])).
% 3.36/1.61  tff(c_2100, plain, (![A_277, A_278]: (k4_xboole_0(A_277, k1_tarski(A_278))=A_277 | '#skF_1'(A_277, k1_tarski(A_278))=A_278)), inference(resolution, [status(thm)], [c_2016, c_18])).
% 3.36/1.61  tff(c_2136, plain, ('#skF_1'('#skF_4', k1_tarski('#skF_5'))='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_2100, c_1940])).
% 3.36/1.61  tff(c_2144, plain, (r2_hidden('#skF_5', '#skF_4') | r1_xboole_0('#skF_4', k1_tarski('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_2136, c_6])).
% 3.36/1.61  tff(c_2171, plain, (r1_xboole_0('#skF_4', k1_tarski('#skF_5'))), inference(splitLeft, [status(thm)], [c_2144])).
% 3.36/1.61  tff(c_2176, plain, (k4_xboole_0('#skF_4', k1_tarski('#skF_5'))='#skF_4'), inference(resolution, [status(thm)], [c_2171, c_18])).
% 3.36/1.61  tff(c_2181, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1940, c_2176])).
% 3.36/1.61  tff(c_2182, plain, (r2_hidden('#skF_5', '#skF_4')), inference(splitRight, [status(thm)], [c_2144])).
% 3.36/1.61  tff(c_2003, plain, (![A_253, B_254, C_255]: (~r1_xboole_0(A_253, B_254) | ~r2_hidden(C_255, B_254) | ~r2_hidden(C_255, A_253))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.36/1.61  tff(c_2006, plain, (![C_255, B_11, A_10]: (~r2_hidden(C_255, B_11) | ~r2_hidden(C_255, A_10) | k4_xboole_0(A_10, B_11)!=A_10)), inference(resolution, [status(thm)], [c_20, c_2003])).
% 3.36/1.61  tff(c_2196, plain, (![A_282]: (~r2_hidden('#skF_5', A_282) | k4_xboole_0(A_282, '#skF_4')!=A_282)), inference(resolution, [status(thm)], [c_2182, c_2006])).
% 3.36/1.61  tff(c_2199, plain, (k4_xboole_0('#skF_4', '#skF_4')!='#skF_4'), inference(resolution, [status(thm)], [c_2182, c_2196])).
% 3.36/1.61  tff(c_2207, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1906, c_2199])).
% 3.36/1.61  tff(c_2208, plain, (k1_tarski('#skF_5')='#skF_4'), inference(splitRight, [status(thm)], [c_1870])).
% 3.36/1.61  tff(c_2210, plain, (~r1_tarski('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2208, c_1857])).
% 3.36/1.61  tff(c_2213, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12, c_2210])).
% 3.36/1.61  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.36/1.61  
% 3.36/1.61  Inference rules
% 3.36/1.61  ----------------------
% 3.36/1.61  #Ref     : 0
% 3.36/1.61  #Sup     : 459
% 3.36/1.61  #Fact    : 0
% 3.36/1.61  #Define  : 0
% 3.36/1.61  #Split   : 13
% 3.36/1.61  #Chain   : 0
% 3.36/1.61  #Close   : 0
% 3.36/1.61  
% 3.36/1.61  Ordering : KBO
% 3.36/1.61  
% 3.36/1.61  Simplification rules
% 3.36/1.61  ----------------------
% 3.36/1.61  #Subsume      : 69
% 3.36/1.61  #Demod        : 165
% 3.36/1.61  #Tautology    : 188
% 3.36/1.61  #SimpNegUnit  : 42
% 3.36/1.61  #BackRed      : 20
% 3.36/1.61  
% 3.36/1.61  #Partial instantiations: 0
% 3.36/1.61  #Strategies tried      : 1
% 3.36/1.61  
% 3.36/1.61  Timing (in seconds)
% 3.36/1.61  ----------------------
% 3.36/1.61  Preprocessing        : 0.32
% 3.36/1.61  Parsing              : 0.16
% 3.36/1.61  CNF conversion       : 0.02
% 3.36/1.61  Main loop            : 0.52
% 3.36/1.61  Inferencing          : 0.20
% 3.36/1.61  Reduction            : 0.15
% 3.36/1.61  Demodulation         : 0.10
% 3.36/1.61  BG Simplification    : 0.03
% 3.36/1.61  Subsumption          : 0.10
% 3.36/1.61  Abstraction          : 0.03
% 3.36/1.61  MUC search           : 0.00
% 3.36/1.61  Cooper               : 0.00
% 3.36/1.61  Total                : 0.88
% 3.36/1.61  Index Insertion      : 0.00
% 3.36/1.61  Index Deletion       : 0.00
% 3.36/1.61  Index Matching       : 0.00
% 3.36/1.61  BG Taut test         : 0.00
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:10:23 EST 2020

% Result     : Theorem 5.39s
% Output     : CNFRefutation 5.54s
% Verified   : 
% Statistics : Number of formulae       :  119 ( 370 expanded)
%              Number of leaves         :   33 ( 125 expanded)
%              Depth                    :   11
%              Number of atoms          :  167 ( 884 expanded)
%              Number of equality atoms :   19 (  96 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k4_zfmisc_1 > k4_mcart_1 > k3_zfmisc_1 > k3_mcart_1 > k4_tarski > k2_zfmisc_1 > #nlpp > #skF_11 > #skF_15 > #skF_7 > #skF_10 > #skF_16 > #skF_14 > #skF_5 > #skF_6 > #skF_13 > #skF_2 > #skF_3 > #skF_1 > #skF_9 > #skF_8 > #skF_4 > #skF_12

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_11',type,(
    '#skF_11': $i )).

tff('#skF_15',type,(
    '#skF_15': $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k3_mcart_1,type,(
    k3_mcart_1: ( $i * $i * $i ) > $i )).

tff(k4_zfmisc_1,type,(
    k4_zfmisc_1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff('#skF_16',type,(
    '#skF_16': $i )).

tff('#skF_14',type,(
    '#skF_14': $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_13',type,(
    '#skF_13': $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k3_zfmisc_1,type,(
    k3_zfmisc_1: ( $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k4_mcart_1,type,(
    k4_mcart_1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_12',type,(
    '#skF_12': $i )).

tff(f_58,negated_conjecture,(
    ~ ! [A,B,C,D,E,F,G,H] :
        ( r2_hidden(k4_mcart_1(A,B,C,D),k4_zfmisc_1(E,F,G,H))
      <=> ( r2_hidden(A,E)
          & r2_hidden(B,F)
          & r2_hidden(C,G)
          & r2_hidden(D,H) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t84_mcart_1)).

tff(f_35,axiom,(
    ! [A,B,C] : k3_zfmisc_1(A,B,C) = k2_zfmisc_1(k2_zfmisc_1(A,B),C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).

tff(f_39,axiom,(
    ! [A,B,C,D] : k4_zfmisc_1(A,B,C,D) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A,B),C),D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t53_mcart_1)).

tff(f_33,axiom,(
    ! [A,B,C] : k3_mcart_1(A,B,C) = k4_tarski(k4_tarski(A,B),C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_mcart_1)).

tff(f_37,axiom,(
    ! [A,B,C,D] : k4_mcart_1(A,B,C,D) = k4_tarski(k4_tarski(k4_tarski(A,B),C),D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_mcart_1)).

tff(f_47,axiom,(
    ! [A,B,C,D,E,F] :
      ( r2_hidden(k3_mcart_1(A,B,C),k3_zfmisc_1(D,E,F))
    <=> ( r2_hidden(A,D)
        & r2_hidden(B,E)
        & r2_hidden(C,F) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_mcart_1)).

tff(f_31,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,D))
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).

tff(c_26,plain,
    ( r2_hidden('#skF_4','#skF_8')
    | ~ r2_hidden('#skF_12','#skF_16')
    | ~ r2_hidden('#skF_11','#skF_15')
    | ~ r2_hidden('#skF_10','#skF_14')
    | ~ r2_hidden('#skF_9','#skF_13') ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_279,plain,(
    ~ r2_hidden('#skF_9','#skF_13') ),
    inference(splitLeft,[status(thm)],[c_26])).

tff(c_38,plain,
    ( r2_hidden('#skF_3','#skF_7')
    | r2_hidden(k4_mcart_1('#skF_9','#skF_10','#skF_11','#skF_12'),k4_zfmisc_1('#skF_13','#skF_14','#skF_15','#skF_16')) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_140,plain,(
    r2_hidden(k4_mcart_1('#skF_9','#skF_10','#skF_11','#skF_12'),k4_zfmisc_1('#skF_13','#skF_14','#skF_15','#skF_16')) ),
    inference(splitLeft,[status(thm)],[c_38])).

tff(c_10,plain,(
    ! [A_8,B_9,C_10] : k2_zfmisc_1(k2_zfmisc_1(A_8,B_9),C_10) = k3_zfmisc_1(A_8,B_9,C_10) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_14,plain,(
    ! [A_15,B_16,C_17,D_18] : k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_15,B_16),C_17),D_18) = k4_zfmisc_1(A_15,B_16,C_17,D_18) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_43,plain,(
    ! [A_15,B_16,C_17,D_18] : k2_zfmisc_1(k3_zfmisc_1(A_15,B_16,C_17),D_18) = k4_zfmisc_1(A_15,B_16,C_17,D_18) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_14])).

tff(c_45,plain,(
    ! [A_25,B_26,C_27] : k2_zfmisc_1(k2_zfmisc_1(A_25,B_26),C_27) = k3_zfmisc_1(A_25,B_26,C_27) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_54,plain,(
    ! [A_8,B_9,C_10,C_27] : k3_zfmisc_1(k2_zfmisc_1(A_8,B_9),C_10,C_27) = k2_zfmisc_1(k3_zfmisc_1(A_8,B_9,C_10),C_27) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_45])).

tff(c_150,plain,(
    ! [A_8,B_9,C_10,C_27] : k3_zfmisc_1(k2_zfmisc_1(A_8,B_9),C_10,C_27) = k4_zfmisc_1(A_8,B_9,C_10,C_27) ),
    inference(demodulation,[status(thm),theory(equality)],[c_43,c_54])).

tff(c_8,plain,(
    ! [A_5,B_6,C_7] : k4_tarski(k4_tarski(A_5,B_6),C_7) = k3_mcart_1(A_5,B_6,C_7) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_12,plain,(
    ! [A_11,B_12,C_13,D_14] : k4_tarski(k4_tarski(k4_tarski(A_11,B_12),C_13),D_14) = k4_mcart_1(A_11,B_12,C_13,D_14) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_44,plain,(
    ! [A_11,B_12,C_13,D_14] : k4_tarski(k3_mcart_1(A_11,B_12,C_13),D_14) = k4_mcart_1(A_11,B_12,C_13,D_14) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_12])).

tff(c_60,plain,(
    ! [A_28,B_29,C_30] : k4_tarski(k4_tarski(A_28,B_29),C_30) = k3_mcart_1(A_28,B_29,C_30) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_63,plain,(
    ! [A_28,B_29,C_30,C_7] : k3_mcart_1(k4_tarski(A_28,B_29),C_30,C_7) = k4_tarski(k3_mcart_1(A_28,B_29,C_30),C_7) ),
    inference(superposition,[status(thm),theory(equality)],[c_60,c_8])).

tff(c_203,plain,(
    ! [A_89,B_90,C_91,C_92] : k3_mcart_1(k4_tarski(A_89,B_90),C_91,C_92) = k4_mcart_1(A_89,B_90,C_91,C_92) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_63])).

tff(c_22,plain,(
    ! [A_19,C_21,D_22,B_20,F_24,E_23] :
      ( r2_hidden(A_19,D_22)
      | ~ r2_hidden(k3_mcart_1(A_19,B_20,C_21),k3_zfmisc_1(D_22,E_23,F_24)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_523,plain,(
    ! [B_209,C_210,E_207,D_213,F_211,C_208,A_212] :
      ( r2_hidden(k4_tarski(A_212,B_209),D_213)
      | ~ r2_hidden(k4_mcart_1(A_212,B_209,C_208,C_210),k3_zfmisc_1(D_213,E_207,F_211)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_203,c_22])).

tff(c_911,plain,(
    ! [A_315,C_322,C_318,C_316,A_317,C_321,B_320,B_319] :
      ( r2_hidden(k4_tarski(A_315,B_319),k2_zfmisc_1(A_317,B_320))
      | ~ r2_hidden(k4_mcart_1(A_315,B_319,C_321,C_316),k4_zfmisc_1(A_317,B_320,C_322,C_318)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_150,c_523])).

tff(c_931,plain,(
    r2_hidden(k4_tarski('#skF_9','#skF_10'),k2_zfmisc_1('#skF_13','#skF_14')) ),
    inference(resolution,[status(thm)],[c_140,c_911])).

tff(c_6,plain,(
    ! [A_1,C_3,B_2,D_4] :
      ( r2_hidden(A_1,C_3)
      | ~ r2_hidden(k4_tarski(A_1,B_2),k2_zfmisc_1(C_3,D_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_937,plain,(
    r2_hidden('#skF_9','#skF_13') ),
    inference(resolution,[status(thm)],[c_931,c_6])).

tff(c_942,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_279,c_937])).

tff(c_944,plain,(
    r2_hidden('#skF_9','#skF_13') ),
    inference(splitRight,[status(thm)],[c_26])).

tff(c_943,plain,
    ( ~ r2_hidden('#skF_10','#skF_14')
    | ~ r2_hidden('#skF_11','#skF_15')
    | ~ r2_hidden('#skF_12','#skF_16')
    | r2_hidden('#skF_4','#skF_8') ),
    inference(splitRight,[status(thm)],[c_26])).

tff(c_945,plain,(
    ~ r2_hidden('#skF_12','#skF_16') ),
    inference(splitLeft,[status(thm)],[c_943])).

tff(c_89,plain,(
    ! [A_39,B_40,C_41,D_42] : k2_zfmisc_1(k3_zfmisc_1(A_39,B_40,C_41),D_42) = k4_zfmisc_1(A_39,B_40,C_41,D_42) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_14])).

tff(c_4,plain,(
    ! [B_2,D_4,A_1,C_3] :
      ( r2_hidden(B_2,D_4)
      | ~ r2_hidden(k4_tarski(A_1,B_2),k2_zfmisc_1(C_3,D_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_234,plain,(
    ! [A_98,D_96,C_95,B_94,B_97,A_93] :
      ( r2_hidden(B_97,D_96)
      | ~ r2_hidden(k4_tarski(A_98,B_97),k4_zfmisc_1(A_93,B_94,C_95,D_96)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_89,c_4])).

tff(c_1100,plain,(
    ! [A_353,D_357,B_350,A_352,B_354,C_351,D_356,C_355] :
      ( r2_hidden(D_356,D_357)
      | ~ r2_hidden(k4_mcart_1(A_352,B_354,C_351,D_356),k4_zfmisc_1(A_353,B_350,C_355,D_357)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_234])).

tff(c_1109,plain,(
    r2_hidden('#skF_12','#skF_16') ),
    inference(resolution,[status(thm)],[c_140,c_1100])).

tff(c_1113,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_945,c_1109])).

tff(c_1114,plain,
    ( ~ r2_hidden('#skF_11','#skF_15')
    | ~ r2_hidden('#skF_10','#skF_14')
    | r2_hidden('#skF_4','#skF_8') ),
    inference(splitRight,[status(thm)],[c_943])).

tff(c_1116,plain,(
    ~ r2_hidden('#skF_10','#skF_14') ),
    inference(splitLeft,[status(thm)],[c_1114])).

tff(c_1375,plain,(
    ! [C_443,F_446,E_442,D_448,A_447,B_444,C_445] :
      ( r2_hidden(k4_tarski(A_447,B_444),D_448)
      | ~ r2_hidden(k4_mcart_1(A_447,B_444,C_443,C_445),k3_zfmisc_1(D_448,E_442,F_446)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_203,c_22])).

tff(c_1719,plain,(
    ! [B_543,C_544,A_540,A_538,C_542,C_537,C_541,B_539] :
      ( r2_hidden(k4_tarski(A_538,B_539),k2_zfmisc_1(A_540,B_543))
      | ~ r2_hidden(k4_mcart_1(A_538,B_539,C_537,C_542),k4_zfmisc_1(A_540,B_543,C_544,C_541)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_150,c_1375])).

tff(c_1739,plain,(
    r2_hidden(k4_tarski('#skF_9','#skF_10'),k2_zfmisc_1('#skF_13','#skF_14')) ),
    inference(resolution,[status(thm)],[c_140,c_1719])).

tff(c_1742,plain,(
    r2_hidden('#skF_10','#skF_14') ),
    inference(resolution,[status(thm)],[c_1739,c_4])).

tff(c_1749,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1116,c_1742])).

tff(c_1751,plain,(
    r2_hidden('#skF_10','#skF_14') ),
    inference(splitRight,[status(thm)],[c_1114])).

tff(c_1115,plain,(
    r2_hidden('#skF_12','#skF_16') ),
    inference(splitRight,[status(thm)],[c_943])).

tff(c_32,plain,
    ( r2_hidden('#skF_1','#skF_5')
    | ~ r2_hidden('#skF_12','#skF_16')
    | ~ r2_hidden('#skF_11','#skF_15')
    | ~ r2_hidden('#skF_10','#skF_14')
    | ~ r2_hidden('#skF_9','#skF_13') ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_1753,plain,
    ( r2_hidden('#skF_1','#skF_5')
    | ~ r2_hidden('#skF_11','#skF_15') ),
    inference(demodulation,[status(thm),theory(equality)],[c_944,c_1751,c_1115,c_32])).

tff(c_1754,plain,(
    ~ r2_hidden('#skF_11','#skF_15') ),
    inference(splitLeft,[status(thm)],[c_1753])).

tff(c_202,plain,(
    ! [A_28,B_29,C_30,C_7] : k3_mcart_1(k4_tarski(A_28,B_29),C_30,C_7) = k4_mcart_1(A_28,B_29,C_30,C_7) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_63])).

tff(c_151,plain,(
    ! [A_81,B_82,C_83,C_84] : k3_zfmisc_1(k2_zfmisc_1(A_81,B_82),C_83,C_84) = k4_zfmisc_1(A_81,B_82,C_83,C_84) ),
    inference(demodulation,[status(thm),theory(equality)],[c_43,c_54])).

tff(c_20,plain,(
    ! [A_19,C_21,D_22,B_20,F_24,E_23] :
      ( r2_hidden(B_20,E_23)
      | ~ r2_hidden(k3_mcart_1(A_19,B_20,C_21),k3_zfmisc_1(D_22,E_23,F_24)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_1755,plain,(
    ! [A_549,C_550,B_551,B_547,A_546,C_548,C_545] :
      ( r2_hidden(B_547,C_550)
      | ~ r2_hidden(k3_mcart_1(A_549,B_547,C_545),k4_zfmisc_1(A_546,B_551,C_550,C_548)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_151,c_20])).

tff(c_1919,plain,(
    ! [C_583,C_587,A_584,C_585,A_580,B_586,C_581,B_582] :
      ( r2_hidden(C_581,C_587)
      | ~ r2_hidden(k4_mcart_1(A_580,B_582,C_581,C_583),k4_zfmisc_1(A_584,B_586,C_587,C_585)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_202,c_1755])).

tff(c_1928,plain,(
    r2_hidden('#skF_11','#skF_15') ),
    inference(resolution,[status(thm)],[c_140,c_1919])).

tff(c_1932,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1754,c_1928])).

tff(c_1933,plain,(
    r2_hidden('#skF_1','#skF_5') ),
    inference(splitRight,[status(thm)],[c_1753])).

tff(c_1934,plain,(
    r2_hidden('#skF_11','#skF_15') ),
    inference(splitRight,[status(thm)],[c_1753])).

tff(c_30,plain,
    ( r2_hidden('#skF_2','#skF_6')
    | ~ r2_hidden('#skF_12','#skF_16')
    | ~ r2_hidden('#skF_11','#skF_15')
    | ~ r2_hidden('#skF_10','#skF_14')
    | ~ r2_hidden('#skF_9','#skF_13') ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_2100,plain,(
    r2_hidden('#skF_2','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_944,c_1751,c_1934,c_1115,c_30])).

tff(c_28,plain,
    ( r2_hidden('#skF_3','#skF_7')
    | ~ r2_hidden('#skF_12','#skF_16')
    | ~ r2_hidden('#skF_11','#skF_15')
    | ~ r2_hidden('#skF_10','#skF_14')
    | ~ r2_hidden('#skF_9','#skF_13') ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_1988,plain,(
    r2_hidden('#skF_3','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_944,c_1751,c_1934,c_1115,c_28])).

tff(c_16,plain,(
    ! [A_19,C_21,D_22,B_20,F_24,E_23] :
      ( r2_hidden(k3_mcart_1(A_19,B_20,C_21),k3_zfmisc_1(D_22,E_23,F_24))
      | ~ r2_hidden(C_21,F_24)
      | ~ r2_hidden(B_20,E_23)
      | ~ r2_hidden(A_19,D_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_1750,plain,
    ( ~ r2_hidden('#skF_11','#skF_15')
    | r2_hidden('#skF_4','#skF_8') ),
    inference(splitRight,[status(thm)],[c_1114])).

tff(c_1936,plain,(
    r2_hidden('#skF_4','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1934,c_1750])).

tff(c_181,plain,(
    ! [A_85,B_86,C_87,D_88] :
      ( r2_hidden(k4_tarski(A_85,B_86),k2_zfmisc_1(C_87,D_88))
      | ~ r2_hidden(B_86,D_88)
      | ~ r2_hidden(A_85,C_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_2435,plain,(
    ! [D_733,A_735,B_734,C_732,B_731,A_736] :
      ( r2_hidden(k4_tarski(A_736,B_731),k4_zfmisc_1(A_735,B_734,C_732,D_733))
      | ~ r2_hidden(B_731,D_733)
      | ~ r2_hidden(A_736,k3_zfmisc_1(A_735,B_734,C_732)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_43,c_181])).

tff(c_2822,plain,(
    ! [B_840,A_839,D_838,D_842,B_843,A_841,C_836,C_837] :
      ( r2_hidden(k4_mcart_1(A_839,B_840,C_837,D_842),k4_zfmisc_1(A_841,B_843,C_836,D_838))
      | ~ r2_hidden(D_842,D_838)
      | ~ r2_hidden(k3_mcart_1(A_839,B_840,C_837),k3_zfmisc_1(A_841,B_843,C_836)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_2435])).

tff(c_24,plain,
    ( ~ r2_hidden(k4_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4'),k4_zfmisc_1('#skF_5','#skF_6','#skF_7','#skF_8'))
    | ~ r2_hidden('#skF_12','#skF_16')
    | ~ r2_hidden('#skF_11','#skF_15')
    | ~ r2_hidden('#skF_10','#skF_14')
    | ~ r2_hidden('#skF_9','#skF_13') ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_2174,plain,(
    ~ r2_hidden(k4_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4'),k4_zfmisc_1('#skF_5','#skF_6','#skF_7','#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_944,c_1751,c_1934,c_1115,c_24])).

tff(c_2831,plain,
    ( ~ r2_hidden('#skF_4','#skF_8')
    | ~ r2_hidden(k3_mcart_1('#skF_1','#skF_2','#skF_3'),k3_zfmisc_1('#skF_5','#skF_6','#skF_7')) ),
    inference(resolution,[status(thm)],[c_2822,c_2174])).

tff(c_2854,plain,(
    ~ r2_hidden(k3_mcart_1('#skF_1','#skF_2','#skF_3'),k3_zfmisc_1('#skF_5','#skF_6','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1936,c_2831])).

tff(c_2866,plain,
    ( ~ r2_hidden('#skF_3','#skF_7')
    | ~ r2_hidden('#skF_2','#skF_6')
    | ~ r2_hidden('#skF_1','#skF_5') ),
    inference(resolution,[status(thm)],[c_16,c_2854])).

tff(c_2873,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1933,c_2100,c_1988,c_2866])).

tff(c_2875,plain,(
    ~ r2_hidden(k4_mcart_1('#skF_9','#skF_10','#skF_11','#skF_12'),k4_zfmisc_1('#skF_13','#skF_14','#skF_15','#skF_16')) ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_42,plain,
    ( r2_hidden('#skF_1','#skF_5')
    | r2_hidden(k4_mcart_1('#skF_9','#skF_10','#skF_11','#skF_12'),k4_zfmisc_1('#skF_13','#skF_14','#skF_15','#skF_16')) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_2990,plain,(
    r2_hidden('#skF_1','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_2875,c_42])).

tff(c_40,plain,
    ( r2_hidden('#skF_2','#skF_6')
    | r2_hidden(k4_mcart_1('#skF_9','#skF_10','#skF_11','#skF_12'),k4_zfmisc_1('#skF_13','#skF_14','#skF_15','#skF_16')) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_2978,plain,(
    r2_hidden('#skF_2','#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_2875,c_40])).

tff(c_2874,plain,(
    r2_hidden('#skF_3','#skF_7') ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_36,plain,
    ( r2_hidden('#skF_4','#skF_8')
    | r2_hidden(k4_mcart_1('#skF_9','#skF_10','#skF_11','#skF_12'),k4_zfmisc_1('#skF_13','#skF_14','#skF_15','#skF_16')) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_2876,plain,(
    r2_hidden('#skF_4','#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_2875,c_36])).

tff(c_2942,plain,(
    ! [A_864,B_865,C_866,D_867] :
      ( r2_hidden(k4_tarski(A_864,B_865),k2_zfmisc_1(C_866,D_867))
      | ~ r2_hidden(B_865,D_867)
      | ~ r2_hidden(A_864,C_866) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_3472,plain,(
    ! [D_1053,C_1049,A_1050,D_1051,C_1048,B_1052] :
      ( r2_hidden(k4_mcart_1(A_1050,B_1052,C_1048,D_1053),k2_zfmisc_1(C_1049,D_1051))
      | ~ r2_hidden(D_1053,D_1051)
      | ~ r2_hidden(k3_mcart_1(A_1050,B_1052,C_1048),C_1049) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_2942])).

tff(c_3872,plain,(
    ! [B_1173,D_1168,C_1169,C_1171,D_1170,B_1172,A_1175,A_1174] :
      ( r2_hidden(k4_mcart_1(A_1174,B_1173,C_1171,D_1168),k4_zfmisc_1(A_1175,B_1172,C_1169,D_1170))
      | ~ r2_hidden(D_1168,D_1170)
      | ~ r2_hidden(k3_mcart_1(A_1174,B_1173,C_1171),k3_zfmisc_1(A_1175,B_1172,C_1169)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_43,c_3472])).

tff(c_34,plain,
    ( ~ r2_hidden(k4_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4'),k4_zfmisc_1('#skF_5','#skF_6','#skF_7','#skF_8'))
    | r2_hidden(k4_mcart_1('#skF_9','#skF_10','#skF_11','#skF_12'),k4_zfmisc_1('#skF_13','#skF_14','#skF_15','#skF_16')) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_3182,plain,(
    ~ r2_hidden(k4_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4'),k4_zfmisc_1('#skF_5','#skF_6','#skF_7','#skF_8')) ),
    inference(negUnitSimplification,[status(thm)],[c_2875,c_34])).

tff(c_3881,plain,
    ( ~ r2_hidden('#skF_4','#skF_8')
    | ~ r2_hidden(k3_mcart_1('#skF_1','#skF_2','#skF_3'),k3_zfmisc_1('#skF_5','#skF_6','#skF_7')) ),
    inference(resolution,[status(thm)],[c_3872,c_3182])).

tff(c_3907,plain,(
    ~ r2_hidden(k3_mcart_1('#skF_1','#skF_2','#skF_3'),k3_zfmisc_1('#skF_5','#skF_6','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2876,c_3881])).

tff(c_3920,plain,
    ( ~ r2_hidden('#skF_3','#skF_7')
    | ~ r2_hidden('#skF_2','#skF_6')
    | ~ r2_hidden('#skF_1','#skF_5') ),
    inference(resolution,[status(thm)],[c_16,c_3907])).

tff(c_3927,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2990,c_2978,c_2874,c_3920])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:59:07 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.39/2.09  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.39/2.10  
% 5.39/2.10  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.39/2.10  %$ r2_hidden > k4_zfmisc_1 > k4_mcart_1 > k3_zfmisc_1 > k3_mcart_1 > k4_tarski > k2_zfmisc_1 > #nlpp > #skF_11 > #skF_15 > #skF_7 > #skF_10 > #skF_16 > #skF_14 > #skF_5 > #skF_6 > #skF_13 > #skF_2 > #skF_3 > #skF_1 > #skF_9 > #skF_8 > #skF_4 > #skF_12
% 5.39/2.10  
% 5.39/2.10  %Foreground sorts:
% 5.39/2.10  
% 5.39/2.10  
% 5.39/2.10  %Background operators:
% 5.39/2.10  
% 5.39/2.10  
% 5.39/2.10  %Foreground operators:
% 5.39/2.10  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.39/2.10  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.39/2.10  tff('#skF_11', type, '#skF_11': $i).
% 5.39/2.10  tff('#skF_15', type, '#skF_15': $i).
% 5.39/2.10  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 5.39/2.10  tff(k3_mcart_1, type, k3_mcart_1: ($i * $i * $i) > $i).
% 5.39/2.10  tff(k4_zfmisc_1, type, k4_zfmisc_1: ($i * $i * $i * $i) > $i).
% 5.39/2.10  tff('#skF_7', type, '#skF_7': $i).
% 5.39/2.10  tff('#skF_10', type, '#skF_10': $i).
% 5.39/2.10  tff('#skF_16', type, '#skF_16': $i).
% 5.39/2.10  tff('#skF_14', type, '#skF_14': $i).
% 5.39/2.10  tff('#skF_5', type, '#skF_5': $i).
% 5.39/2.10  tff('#skF_6', type, '#skF_6': $i).
% 5.39/2.10  tff('#skF_13', type, '#skF_13': $i).
% 5.39/2.10  tff('#skF_2', type, '#skF_2': $i).
% 5.39/2.10  tff('#skF_3', type, '#skF_3': $i).
% 5.39/2.10  tff('#skF_1', type, '#skF_1': $i).
% 5.39/2.10  tff('#skF_9', type, '#skF_9': $i).
% 5.39/2.10  tff(k3_zfmisc_1, type, k3_zfmisc_1: ($i * $i * $i) > $i).
% 5.39/2.10  tff('#skF_8', type, '#skF_8': $i).
% 5.39/2.10  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.39/2.10  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.39/2.10  tff('#skF_4', type, '#skF_4': $i).
% 5.39/2.10  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.39/2.10  tff(k4_mcart_1, type, k4_mcart_1: ($i * $i * $i * $i) > $i).
% 5.39/2.10  tff('#skF_12', type, '#skF_12': $i).
% 5.39/2.10  
% 5.54/2.12  tff(f_58, negated_conjecture, ~(![A, B, C, D, E, F, G, H]: (r2_hidden(k4_mcart_1(A, B, C, D), k4_zfmisc_1(E, F, G, H)) <=> (((r2_hidden(A, E) & r2_hidden(B, F)) & r2_hidden(C, G)) & r2_hidden(D, H)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t84_mcart_1)).
% 5.54/2.12  tff(f_35, axiom, (![A, B, C]: (k3_zfmisc_1(A, B, C) = k2_zfmisc_1(k2_zfmisc_1(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_zfmisc_1)).
% 5.54/2.12  tff(f_39, axiom, (![A, B, C, D]: (k4_zfmisc_1(A, B, C, D) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A, B), C), D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t53_mcart_1)).
% 5.54/2.12  tff(f_33, axiom, (![A, B, C]: (k3_mcart_1(A, B, C) = k4_tarski(k4_tarski(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_mcart_1)).
% 5.54/2.12  tff(f_37, axiom, (![A, B, C, D]: (k4_mcart_1(A, B, C, D) = k4_tarski(k4_tarski(k4_tarski(A, B), C), D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_mcart_1)).
% 5.54/2.12  tff(f_47, axiom, (![A, B, C, D, E, F]: (r2_hidden(k3_mcart_1(A, B, C), k3_zfmisc_1(D, E, F)) <=> ((r2_hidden(A, D) & r2_hidden(B, E)) & r2_hidden(C, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_mcart_1)).
% 5.54/2.12  tff(f_31, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, D)) <=> (r2_hidden(A, C) & r2_hidden(B, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 5.54/2.12  tff(c_26, plain, (r2_hidden('#skF_4', '#skF_8') | ~r2_hidden('#skF_12', '#skF_16') | ~r2_hidden('#skF_11', '#skF_15') | ~r2_hidden('#skF_10', '#skF_14') | ~r2_hidden('#skF_9', '#skF_13')), inference(cnfTransformation, [status(thm)], [f_58])).
% 5.54/2.12  tff(c_279, plain, (~r2_hidden('#skF_9', '#skF_13')), inference(splitLeft, [status(thm)], [c_26])).
% 5.54/2.12  tff(c_38, plain, (r2_hidden('#skF_3', '#skF_7') | r2_hidden(k4_mcart_1('#skF_9', '#skF_10', '#skF_11', '#skF_12'), k4_zfmisc_1('#skF_13', '#skF_14', '#skF_15', '#skF_16'))), inference(cnfTransformation, [status(thm)], [f_58])).
% 5.54/2.12  tff(c_140, plain, (r2_hidden(k4_mcart_1('#skF_9', '#skF_10', '#skF_11', '#skF_12'), k4_zfmisc_1('#skF_13', '#skF_14', '#skF_15', '#skF_16'))), inference(splitLeft, [status(thm)], [c_38])).
% 5.54/2.12  tff(c_10, plain, (![A_8, B_9, C_10]: (k2_zfmisc_1(k2_zfmisc_1(A_8, B_9), C_10)=k3_zfmisc_1(A_8, B_9, C_10))), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.54/2.12  tff(c_14, plain, (![A_15, B_16, C_17, D_18]: (k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_15, B_16), C_17), D_18)=k4_zfmisc_1(A_15, B_16, C_17, D_18))), inference(cnfTransformation, [status(thm)], [f_39])).
% 5.54/2.12  tff(c_43, plain, (![A_15, B_16, C_17, D_18]: (k2_zfmisc_1(k3_zfmisc_1(A_15, B_16, C_17), D_18)=k4_zfmisc_1(A_15, B_16, C_17, D_18))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_14])).
% 5.54/2.12  tff(c_45, plain, (![A_25, B_26, C_27]: (k2_zfmisc_1(k2_zfmisc_1(A_25, B_26), C_27)=k3_zfmisc_1(A_25, B_26, C_27))), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.54/2.12  tff(c_54, plain, (![A_8, B_9, C_10, C_27]: (k3_zfmisc_1(k2_zfmisc_1(A_8, B_9), C_10, C_27)=k2_zfmisc_1(k3_zfmisc_1(A_8, B_9, C_10), C_27))), inference(superposition, [status(thm), theory('equality')], [c_10, c_45])).
% 5.54/2.12  tff(c_150, plain, (![A_8, B_9, C_10, C_27]: (k3_zfmisc_1(k2_zfmisc_1(A_8, B_9), C_10, C_27)=k4_zfmisc_1(A_8, B_9, C_10, C_27))), inference(demodulation, [status(thm), theory('equality')], [c_43, c_54])).
% 5.54/2.12  tff(c_8, plain, (![A_5, B_6, C_7]: (k4_tarski(k4_tarski(A_5, B_6), C_7)=k3_mcart_1(A_5, B_6, C_7))), inference(cnfTransformation, [status(thm)], [f_33])).
% 5.54/2.12  tff(c_12, plain, (![A_11, B_12, C_13, D_14]: (k4_tarski(k4_tarski(k4_tarski(A_11, B_12), C_13), D_14)=k4_mcart_1(A_11, B_12, C_13, D_14))), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.54/2.12  tff(c_44, plain, (![A_11, B_12, C_13, D_14]: (k4_tarski(k3_mcart_1(A_11, B_12, C_13), D_14)=k4_mcart_1(A_11, B_12, C_13, D_14))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_12])).
% 5.54/2.12  tff(c_60, plain, (![A_28, B_29, C_30]: (k4_tarski(k4_tarski(A_28, B_29), C_30)=k3_mcart_1(A_28, B_29, C_30))), inference(cnfTransformation, [status(thm)], [f_33])).
% 5.54/2.12  tff(c_63, plain, (![A_28, B_29, C_30, C_7]: (k3_mcart_1(k4_tarski(A_28, B_29), C_30, C_7)=k4_tarski(k3_mcart_1(A_28, B_29, C_30), C_7))), inference(superposition, [status(thm), theory('equality')], [c_60, c_8])).
% 5.54/2.12  tff(c_203, plain, (![A_89, B_90, C_91, C_92]: (k3_mcart_1(k4_tarski(A_89, B_90), C_91, C_92)=k4_mcart_1(A_89, B_90, C_91, C_92))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_63])).
% 5.54/2.12  tff(c_22, plain, (![A_19, C_21, D_22, B_20, F_24, E_23]: (r2_hidden(A_19, D_22) | ~r2_hidden(k3_mcart_1(A_19, B_20, C_21), k3_zfmisc_1(D_22, E_23, F_24)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 5.54/2.12  tff(c_523, plain, (![B_209, C_210, E_207, D_213, F_211, C_208, A_212]: (r2_hidden(k4_tarski(A_212, B_209), D_213) | ~r2_hidden(k4_mcart_1(A_212, B_209, C_208, C_210), k3_zfmisc_1(D_213, E_207, F_211)))), inference(superposition, [status(thm), theory('equality')], [c_203, c_22])).
% 5.54/2.12  tff(c_911, plain, (![A_315, C_322, C_318, C_316, A_317, C_321, B_320, B_319]: (r2_hidden(k4_tarski(A_315, B_319), k2_zfmisc_1(A_317, B_320)) | ~r2_hidden(k4_mcart_1(A_315, B_319, C_321, C_316), k4_zfmisc_1(A_317, B_320, C_322, C_318)))), inference(superposition, [status(thm), theory('equality')], [c_150, c_523])).
% 5.54/2.12  tff(c_931, plain, (r2_hidden(k4_tarski('#skF_9', '#skF_10'), k2_zfmisc_1('#skF_13', '#skF_14'))), inference(resolution, [status(thm)], [c_140, c_911])).
% 5.54/2.12  tff(c_6, plain, (![A_1, C_3, B_2, D_4]: (r2_hidden(A_1, C_3) | ~r2_hidden(k4_tarski(A_1, B_2), k2_zfmisc_1(C_3, D_4)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.54/2.12  tff(c_937, plain, (r2_hidden('#skF_9', '#skF_13')), inference(resolution, [status(thm)], [c_931, c_6])).
% 5.54/2.12  tff(c_942, plain, $false, inference(negUnitSimplification, [status(thm)], [c_279, c_937])).
% 5.54/2.12  tff(c_944, plain, (r2_hidden('#skF_9', '#skF_13')), inference(splitRight, [status(thm)], [c_26])).
% 5.54/2.12  tff(c_943, plain, (~r2_hidden('#skF_10', '#skF_14') | ~r2_hidden('#skF_11', '#skF_15') | ~r2_hidden('#skF_12', '#skF_16') | r2_hidden('#skF_4', '#skF_8')), inference(splitRight, [status(thm)], [c_26])).
% 5.54/2.12  tff(c_945, plain, (~r2_hidden('#skF_12', '#skF_16')), inference(splitLeft, [status(thm)], [c_943])).
% 5.54/2.12  tff(c_89, plain, (![A_39, B_40, C_41, D_42]: (k2_zfmisc_1(k3_zfmisc_1(A_39, B_40, C_41), D_42)=k4_zfmisc_1(A_39, B_40, C_41, D_42))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_14])).
% 5.54/2.12  tff(c_4, plain, (![B_2, D_4, A_1, C_3]: (r2_hidden(B_2, D_4) | ~r2_hidden(k4_tarski(A_1, B_2), k2_zfmisc_1(C_3, D_4)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.54/2.12  tff(c_234, plain, (![A_98, D_96, C_95, B_94, B_97, A_93]: (r2_hidden(B_97, D_96) | ~r2_hidden(k4_tarski(A_98, B_97), k4_zfmisc_1(A_93, B_94, C_95, D_96)))), inference(superposition, [status(thm), theory('equality')], [c_89, c_4])).
% 5.54/2.12  tff(c_1100, plain, (![A_353, D_357, B_350, A_352, B_354, C_351, D_356, C_355]: (r2_hidden(D_356, D_357) | ~r2_hidden(k4_mcart_1(A_352, B_354, C_351, D_356), k4_zfmisc_1(A_353, B_350, C_355, D_357)))), inference(superposition, [status(thm), theory('equality')], [c_44, c_234])).
% 5.54/2.12  tff(c_1109, plain, (r2_hidden('#skF_12', '#skF_16')), inference(resolution, [status(thm)], [c_140, c_1100])).
% 5.54/2.12  tff(c_1113, plain, $false, inference(negUnitSimplification, [status(thm)], [c_945, c_1109])).
% 5.54/2.12  tff(c_1114, plain, (~r2_hidden('#skF_11', '#skF_15') | ~r2_hidden('#skF_10', '#skF_14') | r2_hidden('#skF_4', '#skF_8')), inference(splitRight, [status(thm)], [c_943])).
% 5.54/2.12  tff(c_1116, plain, (~r2_hidden('#skF_10', '#skF_14')), inference(splitLeft, [status(thm)], [c_1114])).
% 5.54/2.12  tff(c_1375, plain, (![C_443, F_446, E_442, D_448, A_447, B_444, C_445]: (r2_hidden(k4_tarski(A_447, B_444), D_448) | ~r2_hidden(k4_mcart_1(A_447, B_444, C_443, C_445), k3_zfmisc_1(D_448, E_442, F_446)))), inference(superposition, [status(thm), theory('equality')], [c_203, c_22])).
% 5.54/2.12  tff(c_1719, plain, (![B_543, C_544, A_540, A_538, C_542, C_537, C_541, B_539]: (r2_hidden(k4_tarski(A_538, B_539), k2_zfmisc_1(A_540, B_543)) | ~r2_hidden(k4_mcart_1(A_538, B_539, C_537, C_542), k4_zfmisc_1(A_540, B_543, C_544, C_541)))), inference(superposition, [status(thm), theory('equality')], [c_150, c_1375])).
% 5.54/2.12  tff(c_1739, plain, (r2_hidden(k4_tarski('#skF_9', '#skF_10'), k2_zfmisc_1('#skF_13', '#skF_14'))), inference(resolution, [status(thm)], [c_140, c_1719])).
% 5.54/2.12  tff(c_1742, plain, (r2_hidden('#skF_10', '#skF_14')), inference(resolution, [status(thm)], [c_1739, c_4])).
% 5.54/2.12  tff(c_1749, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1116, c_1742])).
% 5.54/2.12  tff(c_1751, plain, (r2_hidden('#skF_10', '#skF_14')), inference(splitRight, [status(thm)], [c_1114])).
% 5.54/2.12  tff(c_1115, plain, (r2_hidden('#skF_12', '#skF_16')), inference(splitRight, [status(thm)], [c_943])).
% 5.54/2.12  tff(c_32, plain, (r2_hidden('#skF_1', '#skF_5') | ~r2_hidden('#skF_12', '#skF_16') | ~r2_hidden('#skF_11', '#skF_15') | ~r2_hidden('#skF_10', '#skF_14') | ~r2_hidden('#skF_9', '#skF_13')), inference(cnfTransformation, [status(thm)], [f_58])).
% 5.54/2.12  tff(c_1753, plain, (r2_hidden('#skF_1', '#skF_5') | ~r2_hidden('#skF_11', '#skF_15')), inference(demodulation, [status(thm), theory('equality')], [c_944, c_1751, c_1115, c_32])).
% 5.54/2.12  tff(c_1754, plain, (~r2_hidden('#skF_11', '#skF_15')), inference(splitLeft, [status(thm)], [c_1753])).
% 5.54/2.12  tff(c_202, plain, (![A_28, B_29, C_30, C_7]: (k3_mcart_1(k4_tarski(A_28, B_29), C_30, C_7)=k4_mcart_1(A_28, B_29, C_30, C_7))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_63])).
% 5.54/2.12  tff(c_151, plain, (![A_81, B_82, C_83, C_84]: (k3_zfmisc_1(k2_zfmisc_1(A_81, B_82), C_83, C_84)=k4_zfmisc_1(A_81, B_82, C_83, C_84))), inference(demodulation, [status(thm), theory('equality')], [c_43, c_54])).
% 5.54/2.12  tff(c_20, plain, (![A_19, C_21, D_22, B_20, F_24, E_23]: (r2_hidden(B_20, E_23) | ~r2_hidden(k3_mcart_1(A_19, B_20, C_21), k3_zfmisc_1(D_22, E_23, F_24)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 5.54/2.12  tff(c_1755, plain, (![A_549, C_550, B_551, B_547, A_546, C_548, C_545]: (r2_hidden(B_547, C_550) | ~r2_hidden(k3_mcart_1(A_549, B_547, C_545), k4_zfmisc_1(A_546, B_551, C_550, C_548)))), inference(superposition, [status(thm), theory('equality')], [c_151, c_20])).
% 5.54/2.12  tff(c_1919, plain, (![C_583, C_587, A_584, C_585, A_580, B_586, C_581, B_582]: (r2_hidden(C_581, C_587) | ~r2_hidden(k4_mcart_1(A_580, B_582, C_581, C_583), k4_zfmisc_1(A_584, B_586, C_587, C_585)))), inference(superposition, [status(thm), theory('equality')], [c_202, c_1755])).
% 5.54/2.12  tff(c_1928, plain, (r2_hidden('#skF_11', '#skF_15')), inference(resolution, [status(thm)], [c_140, c_1919])).
% 5.54/2.12  tff(c_1932, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1754, c_1928])).
% 5.54/2.12  tff(c_1933, plain, (r2_hidden('#skF_1', '#skF_5')), inference(splitRight, [status(thm)], [c_1753])).
% 5.54/2.12  tff(c_1934, plain, (r2_hidden('#skF_11', '#skF_15')), inference(splitRight, [status(thm)], [c_1753])).
% 5.54/2.12  tff(c_30, plain, (r2_hidden('#skF_2', '#skF_6') | ~r2_hidden('#skF_12', '#skF_16') | ~r2_hidden('#skF_11', '#skF_15') | ~r2_hidden('#skF_10', '#skF_14') | ~r2_hidden('#skF_9', '#skF_13')), inference(cnfTransformation, [status(thm)], [f_58])).
% 5.54/2.12  tff(c_2100, plain, (r2_hidden('#skF_2', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_944, c_1751, c_1934, c_1115, c_30])).
% 5.54/2.12  tff(c_28, plain, (r2_hidden('#skF_3', '#skF_7') | ~r2_hidden('#skF_12', '#skF_16') | ~r2_hidden('#skF_11', '#skF_15') | ~r2_hidden('#skF_10', '#skF_14') | ~r2_hidden('#skF_9', '#skF_13')), inference(cnfTransformation, [status(thm)], [f_58])).
% 5.54/2.12  tff(c_1988, plain, (r2_hidden('#skF_3', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_944, c_1751, c_1934, c_1115, c_28])).
% 5.54/2.12  tff(c_16, plain, (![A_19, C_21, D_22, B_20, F_24, E_23]: (r2_hidden(k3_mcart_1(A_19, B_20, C_21), k3_zfmisc_1(D_22, E_23, F_24)) | ~r2_hidden(C_21, F_24) | ~r2_hidden(B_20, E_23) | ~r2_hidden(A_19, D_22))), inference(cnfTransformation, [status(thm)], [f_47])).
% 5.54/2.12  tff(c_1750, plain, (~r2_hidden('#skF_11', '#skF_15') | r2_hidden('#skF_4', '#skF_8')), inference(splitRight, [status(thm)], [c_1114])).
% 5.54/2.12  tff(c_1936, plain, (r2_hidden('#skF_4', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_1934, c_1750])).
% 5.54/2.12  tff(c_181, plain, (![A_85, B_86, C_87, D_88]: (r2_hidden(k4_tarski(A_85, B_86), k2_zfmisc_1(C_87, D_88)) | ~r2_hidden(B_86, D_88) | ~r2_hidden(A_85, C_87))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.54/2.12  tff(c_2435, plain, (![D_733, A_735, B_734, C_732, B_731, A_736]: (r2_hidden(k4_tarski(A_736, B_731), k4_zfmisc_1(A_735, B_734, C_732, D_733)) | ~r2_hidden(B_731, D_733) | ~r2_hidden(A_736, k3_zfmisc_1(A_735, B_734, C_732)))), inference(superposition, [status(thm), theory('equality')], [c_43, c_181])).
% 5.54/2.12  tff(c_2822, plain, (![B_840, A_839, D_838, D_842, B_843, A_841, C_836, C_837]: (r2_hidden(k4_mcart_1(A_839, B_840, C_837, D_842), k4_zfmisc_1(A_841, B_843, C_836, D_838)) | ~r2_hidden(D_842, D_838) | ~r2_hidden(k3_mcart_1(A_839, B_840, C_837), k3_zfmisc_1(A_841, B_843, C_836)))), inference(superposition, [status(thm), theory('equality')], [c_44, c_2435])).
% 5.54/2.12  tff(c_24, plain, (~r2_hidden(k4_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), k4_zfmisc_1('#skF_5', '#skF_6', '#skF_7', '#skF_8')) | ~r2_hidden('#skF_12', '#skF_16') | ~r2_hidden('#skF_11', '#skF_15') | ~r2_hidden('#skF_10', '#skF_14') | ~r2_hidden('#skF_9', '#skF_13')), inference(cnfTransformation, [status(thm)], [f_58])).
% 5.54/2.12  tff(c_2174, plain, (~r2_hidden(k4_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), k4_zfmisc_1('#skF_5', '#skF_6', '#skF_7', '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_944, c_1751, c_1934, c_1115, c_24])).
% 5.54/2.12  tff(c_2831, plain, (~r2_hidden('#skF_4', '#skF_8') | ~r2_hidden(k3_mcart_1('#skF_1', '#skF_2', '#skF_3'), k3_zfmisc_1('#skF_5', '#skF_6', '#skF_7'))), inference(resolution, [status(thm)], [c_2822, c_2174])).
% 5.54/2.12  tff(c_2854, plain, (~r2_hidden(k3_mcart_1('#skF_1', '#skF_2', '#skF_3'), k3_zfmisc_1('#skF_5', '#skF_6', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_1936, c_2831])).
% 5.54/2.12  tff(c_2866, plain, (~r2_hidden('#skF_3', '#skF_7') | ~r2_hidden('#skF_2', '#skF_6') | ~r2_hidden('#skF_1', '#skF_5')), inference(resolution, [status(thm)], [c_16, c_2854])).
% 5.54/2.12  tff(c_2873, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1933, c_2100, c_1988, c_2866])).
% 5.54/2.12  tff(c_2875, plain, (~r2_hidden(k4_mcart_1('#skF_9', '#skF_10', '#skF_11', '#skF_12'), k4_zfmisc_1('#skF_13', '#skF_14', '#skF_15', '#skF_16'))), inference(splitRight, [status(thm)], [c_38])).
% 5.54/2.12  tff(c_42, plain, (r2_hidden('#skF_1', '#skF_5') | r2_hidden(k4_mcart_1('#skF_9', '#skF_10', '#skF_11', '#skF_12'), k4_zfmisc_1('#skF_13', '#skF_14', '#skF_15', '#skF_16'))), inference(cnfTransformation, [status(thm)], [f_58])).
% 5.54/2.12  tff(c_2990, plain, (r2_hidden('#skF_1', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_2875, c_42])).
% 5.54/2.12  tff(c_40, plain, (r2_hidden('#skF_2', '#skF_6') | r2_hidden(k4_mcart_1('#skF_9', '#skF_10', '#skF_11', '#skF_12'), k4_zfmisc_1('#skF_13', '#skF_14', '#skF_15', '#skF_16'))), inference(cnfTransformation, [status(thm)], [f_58])).
% 5.54/2.12  tff(c_2978, plain, (r2_hidden('#skF_2', '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_2875, c_40])).
% 5.54/2.12  tff(c_2874, plain, (r2_hidden('#skF_3', '#skF_7')), inference(splitRight, [status(thm)], [c_38])).
% 5.54/2.12  tff(c_36, plain, (r2_hidden('#skF_4', '#skF_8') | r2_hidden(k4_mcart_1('#skF_9', '#skF_10', '#skF_11', '#skF_12'), k4_zfmisc_1('#skF_13', '#skF_14', '#skF_15', '#skF_16'))), inference(cnfTransformation, [status(thm)], [f_58])).
% 5.54/2.12  tff(c_2876, plain, (r2_hidden('#skF_4', '#skF_8')), inference(negUnitSimplification, [status(thm)], [c_2875, c_36])).
% 5.54/2.12  tff(c_2942, plain, (![A_864, B_865, C_866, D_867]: (r2_hidden(k4_tarski(A_864, B_865), k2_zfmisc_1(C_866, D_867)) | ~r2_hidden(B_865, D_867) | ~r2_hidden(A_864, C_866))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.54/2.12  tff(c_3472, plain, (![D_1053, C_1049, A_1050, D_1051, C_1048, B_1052]: (r2_hidden(k4_mcart_1(A_1050, B_1052, C_1048, D_1053), k2_zfmisc_1(C_1049, D_1051)) | ~r2_hidden(D_1053, D_1051) | ~r2_hidden(k3_mcart_1(A_1050, B_1052, C_1048), C_1049))), inference(superposition, [status(thm), theory('equality')], [c_44, c_2942])).
% 5.54/2.12  tff(c_3872, plain, (![B_1173, D_1168, C_1169, C_1171, D_1170, B_1172, A_1175, A_1174]: (r2_hidden(k4_mcart_1(A_1174, B_1173, C_1171, D_1168), k4_zfmisc_1(A_1175, B_1172, C_1169, D_1170)) | ~r2_hidden(D_1168, D_1170) | ~r2_hidden(k3_mcart_1(A_1174, B_1173, C_1171), k3_zfmisc_1(A_1175, B_1172, C_1169)))), inference(superposition, [status(thm), theory('equality')], [c_43, c_3472])).
% 5.54/2.12  tff(c_34, plain, (~r2_hidden(k4_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), k4_zfmisc_1('#skF_5', '#skF_6', '#skF_7', '#skF_8')) | r2_hidden(k4_mcart_1('#skF_9', '#skF_10', '#skF_11', '#skF_12'), k4_zfmisc_1('#skF_13', '#skF_14', '#skF_15', '#skF_16'))), inference(cnfTransformation, [status(thm)], [f_58])).
% 5.54/2.12  tff(c_3182, plain, (~r2_hidden(k4_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), k4_zfmisc_1('#skF_5', '#skF_6', '#skF_7', '#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_2875, c_34])).
% 5.54/2.12  tff(c_3881, plain, (~r2_hidden('#skF_4', '#skF_8') | ~r2_hidden(k3_mcart_1('#skF_1', '#skF_2', '#skF_3'), k3_zfmisc_1('#skF_5', '#skF_6', '#skF_7'))), inference(resolution, [status(thm)], [c_3872, c_3182])).
% 5.54/2.12  tff(c_3907, plain, (~r2_hidden(k3_mcart_1('#skF_1', '#skF_2', '#skF_3'), k3_zfmisc_1('#skF_5', '#skF_6', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_2876, c_3881])).
% 5.54/2.12  tff(c_3920, plain, (~r2_hidden('#skF_3', '#skF_7') | ~r2_hidden('#skF_2', '#skF_6') | ~r2_hidden('#skF_1', '#skF_5')), inference(resolution, [status(thm)], [c_16, c_3907])).
% 5.54/2.12  tff(c_3927, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2990, c_2978, c_2874, c_3920])).
% 5.54/2.12  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.54/2.12  
% 5.54/2.12  Inference rules
% 5.54/2.12  ----------------------
% 5.54/2.12  #Ref     : 0
% 5.54/2.12  #Sup     : 983
% 5.54/2.12  #Fact    : 0
% 5.54/2.12  #Define  : 0
% 5.54/2.12  #Split   : 5
% 5.54/2.12  #Chain   : 0
% 5.54/2.12  #Close   : 0
% 5.54/2.12  
% 5.54/2.12  Ordering : KBO
% 5.54/2.12  
% 5.54/2.12  Simplification rules
% 5.54/2.12  ----------------------
% 5.54/2.12  #Subsume      : 512
% 5.54/2.12  #Demod        : 546
% 5.54/2.12  #Tautology    : 246
% 5.54/2.12  #SimpNegUnit  : 8
% 5.54/2.12  #BackRed      : 0
% 5.54/2.12  
% 5.54/2.12  #Partial instantiations: 0
% 5.54/2.12  #Strategies tried      : 1
% 5.54/2.12  
% 5.54/2.12  Timing (in seconds)
% 5.54/2.12  ----------------------
% 5.54/2.13  Preprocessing        : 0.31
% 5.54/2.13  Parsing              : 0.17
% 5.54/2.13  CNF conversion       : 0.03
% 5.54/2.13  Main loop            : 0.96
% 5.54/2.13  Inferencing          : 0.39
% 5.54/2.13  Reduction            : 0.29
% 5.54/2.13  Demodulation         : 0.21
% 5.54/2.13  BG Simplification    : 0.04
% 5.54/2.13  Subsumption          : 0.18
% 5.54/2.13  Abstraction          : 0.05
% 5.54/2.13  MUC search           : 0.00
% 5.54/2.13  Cooper               : 0.00
% 5.54/2.13  Total                : 1.31
% 5.54/2.13  Index Insertion      : 0.00
% 5.54/2.13  Index Deletion       : 0.00
% 5.54/2.13  Index Matching       : 0.00
% 5.54/2.13  BG Taut test         : 0.00
%------------------------------------------------------------------------------

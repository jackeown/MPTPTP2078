%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0924+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:37:05 EST 2020

% Result     : Theorem 3.43s
% Output     : CNFRefutation 3.68s
% Verified   : 
% Statistics : Number of formulae       :  112 ( 330 expanded)
%              Number of leaves         :   32 ( 113 expanded)
%              Depth                    :   11
%              Number of atoms          :  170 ( 843 expanded)
%              Number of equality atoms :   10 (  60 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    3 (   1 average)

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

tff(f_55,negated_conjecture,(
    ~ ! [A,B,C,D,E,F,G,H] :
        ( r2_hidden(k4_mcart_1(A,B,C,D),k4_zfmisc_1(E,F,G,H))
      <=> ( r2_hidden(A,E)
          & r2_hidden(B,F)
          & r2_hidden(C,G)
          & r2_hidden(D,H) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t84_mcart_1)).

tff(f_28,axiom,(
    ! [A,B,C,D] : k4_mcart_1(A,B,C,D) = k4_tarski(k3_mcart_1(A,B,C),D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_mcart_1)).

tff(f_26,axiom,(
    ! [A,B,C] : k3_mcart_1(A,B,C) = k4_tarski(k4_tarski(A,B),C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_mcart_1)).

tff(f_36,axiom,(
    ! [A,B,C,D] : k3_zfmisc_1(k2_zfmisc_1(A,B),C,D) = k4_zfmisc_1(A,B,C,D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_mcart_1)).

tff(f_44,axiom,(
    ! [A,B,C,D,E,F] :
      ( r2_hidden(k3_mcart_1(A,B,C),k3_zfmisc_1(D,E,F))
    <=> ( r2_hidden(A,D)
        & r2_hidden(B,E)
        & r2_hidden(C,F) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_mcart_1)).

tff(f_34,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,D))
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_zfmisc_1)).

tff(c_24,plain,
    ( r2_hidden('#skF_4','#skF_8')
    | ~ r2_hidden('#skF_12','#skF_16')
    | ~ r2_hidden('#skF_11','#skF_15')
    | ~ r2_hidden('#skF_10','#skF_14')
    | ~ r2_hidden('#skF_9','#skF_13') ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_223,plain,(
    ~ r2_hidden('#skF_9','#skF_13') ),
    inference(splitLeft,[status(thm)],[c_24])).

tff(c_34,plain,
    ( r2_hidden('#skF_4','#skF_8')
    | r2_hidden(k4_mcart_1('#skF_9','#skF_10','#skF_11','#skF_12'),k4_zfmisc_1('#skF_13','#skF_14','#skF_15','#skF_16')) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_104,plain,(
    r2_hidden(k4_mcart_1('#skF_9','#skF_10','#skF_11','#skF_12'),k4_zfmisc_1('#skF_13','#skF_14','#skF_15','#skF_16')) ),
    inference(splitLeft,[status(thm)],[c_34])).

tff(c_4,plain,(
    ! [A_4,B_5,C_6,D_7] : k4_tarski(k3_mcart_1(A_4,B_5,C_6),D_7) = k4_mcart_1(A_4,B_5,C_6,D_7) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_41,plain,(
    ! [A_22,B_23,C_24] : k4_tarski(k4_tarski(A_22,B_23),C_24) = k3_mcart_1(A_22,B_23,C_24) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_2,plain,(
    ! [A_1,B_2,C_3] : k4_tarski(k4_tarski(A_1,B_2),C_3) = k3_mcart_1(A_1,B_2,C_3) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_44,plain,(
    ! [A_22,B_23,C_24,C_3] : k3_mcart_1(k4_tarski(A_22,B_23),C_24,C_3) = k4_tarski(k3_mcart_1(A_22,B_23,C_24),C_3) ),
    inference(superposition,[status(thm),theory(equality)],[c_41,c_2])).

tff(c_105,plain,(
    ! [A_22,B_23,C_24,C_3] : k3_mcart_1(k4_tarski(A_22,B_23),C_24,C_3) = k4_mcart_1(A_22,B_23,C_24,C_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_44])).

tff(c_12,plain,(
    ! [A_12,B_13,C_14,D_15] : k3_zfmisc_1(k2_zfmisc_1(A_12,B_13),C_14,D_15) = k4_zfmisc_1(A_12,B_13,C_14,D_15) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_91,plain,(
    ! [C_46,F_41,E_43,D_45,A_44,B_42] :
      ( r2_hidden(A_44,D_45)
      | ~ r2_hidden(k3_mcart_1(A_44,B_42,C_46),k3_zfmisc_1(D_45,E_43,F_41)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_277,plain,(
    ! [C_147,B_143,A_144,B_149,C_145,A_148,D_146] :
      ( r2_hidden(A_148,k2_zfmisc_1(A_144,B_143))
      | ~ r2_hidden(k3_mcart_1(A_148,B_149,C_145),k4_zfmisc_1(A_144,B_143,C_147,D_146)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_91])).

tff(c_443,plain,(
    ! [C_226,C_227,A_224,B_225,B_228,C_223,D_229,A_222] :
      ( r2_hidden(k4_tarski(A_222,B_228),k2_zfmisc_1(A_224,B_225))
      | ~ r2_hidden(k4_mcart_1(A_222,B_228,C_223,C_227),k4_zfmisc_1(A_224,B_225,C_226,D_229)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_105,c_277])).

tff(c_455,plain,(
    r2_hidden(k4_tarski('#skF_9','#skF_10'),k2_zfmisc_1('#skF_13','#skF_14')) ),
    inference(resolution,[status(thm)],[c_104,c_443])).

tff(c_10,plain,(
    ! [A_8,C_10,B_9,D_11] :
      ( r2_hidden(A_8,C_10)
      | ~ r2_hidden(k4_tarski(A_8,B_9),k2_zfmisc_1(C_10,D_11)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_461,plain,(
    r2_hidden('#skF_9','#skF_13') ),
    inference(resolution,[status(thm)],[c_455,c_10])).

tff(c_466,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_223,c_461])).

tff(c_468,plain,(
    r2_hidden('#skF_9','#skF_13') ),
    inference(splitRight,[status(thm)],[c_24])).

tff(c_28,plain,
    ( r2_hidden('#skF_2','#skF_6')
    | ~ r2_hidden('#skF_12','#skF_16')
    | ~ r2_hidden('#skF_11','#skF_15')
    | ~ r2_hidden('#skF_10','#skF_14')
    | ~ r2_hidden('#skF_9','#skF_13') ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_481,plain,
    ( r2_hidden('#skF_2','#skF_6')
    | ~ r2_hidden('#skF_12','#skF_16')
    | ~ r2_hidden('#skF_11','#skF_15')
    | ~ r2_hidden('#skF_10','#skF_14') ),
    inference(demodulation,[status(thm),theory(equality)],[c_468,c_28])).

tff(c_482,plain,(
    ~ r2_hidden('#skF_10','#skF_14') ),
    inference(splitLeft,[status(thm)],[c_481])).

tff(c_530,plain,(
    ! [C_263,B_259,A_260,B_265,C_261,D_262,A_264] :
      ( r2_hidden(A_264,k2_zfmisc_1(A_260,B_259))
      | ~ r2_hidden(k3_mcart_1(A_264,B_265,C_261),k4_zfmisc_1(A_260,B_259,C_263,D_262)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_91])).

tff(c_721,plain,(
    ! [C_353,C_357,C_354,B_356,A_352,D_355,B_358,A_351] :
      ( r2_hidden(k4_tarski(A_352,B_358),k2_zfmisc_1(A_351,B_356))
      | ~ r2_hidden(k4_mcart_1(A_352,B_358,C_354,C_357),k4_zfmisc_1(A_351,B_356,C_353,D_355)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_105,c_530])).

tff(c_733,plain,(
    r2_hidden(k4_tarski('#skF_9','#skF_10'),k2_zfmisc_1('#skF_13','#skF_14')) ),
    inference(resolution,[status(thm)],[c_104,c_721])).

tff(c_8,plain,(
    ! [B_9,D_11,A_8,C_10] :
      ( r2_hidden(B_9,D_11)
      | ~ r2_hidden(k4_tarski(A_8,B_9),k2_zfmisc_1(C_10,D_11)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_736,plain,(
    r2_hidden('#skF_10','#skF_14') ),
    inference(resolution,[status(thm)],[c_733,c_8])).

tff(c_743,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_482,c_736])).

tff(c_745,plain,(
    r2_hidden('#skF_10','#skF_14') ),
    inference(splitRight,[status(thm)],[c_481])).

tff(c_467,plain,
    ( ~ r2_hidden('#skF_10','#skF_14')
    | ~ r2_hidden('#skF_11','#skF_15')
    | ~ r2_hidden('#skF_12','#skF_16')
    | r2_hidden('#skF_4','#skF_8') ),
    inference(splitRight,[status(thm)],[c_24])).

tff(c_469,plain,(
    ~ r2_hidden('#skF_12','#skF_16') ),
    inference(splitLeft,[status(thm)],[c_467])).

tff(c_100,plain,(
    ! [B_59,A_61,D_62,C_63,E_60,F_58] :
      ( r2_hidden(C_63,F_58)
      | ~ r2_hidden(k3_mcart_1(A_61,B_59,C_63),k3_zfmisc_1(D_62,E_60,F_58)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_158,plain,(
    ! [A_85,B_83,C_86,B_84,A_89,D_87,C_88] :
      ( r2_hidden(C_86,D_87)
      | ~ r2_hidden(k3_mcart_1(A_89,B_83,C_86),k4_zfmisc_1(A_85,B_84,C_88,D_87)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_100])).

tff(c_470,plain,(
    ! [A_230,B_234,C_231,D_233,C_235,B_236,C_232,A_237] :
      ( r2_hidden(C_235,D_233)
      | ~ r2_hidden(k4_mcart_1(A_230,B_236,C_231,C_235),k4_zfmisc_1(A_237,B_234,C_232,D_233)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_105,c_158])).

tff(c_473,plain,(
    r2_hidden('#skF_12','#skF_16') ),
    inference(resolution,[status(thm)],[c_104,c_470])).

tff(c_477,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_469,c_473])).

tff(c_478,plain,
    ( ~ r2_hidden('#skF_11','#skF_15')
    | ~ r2_hidden('#skF_10','#skF_14')
    | r2_hidden('#skF_4','#skF_8') ),
    inference(splitRight,[status(thm)],[c_467])).

tff(c_747,plain,
    ( ~ r2_hidden('#skF_11','#skF_15')
    | r2_hidden('#skF_4','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_745,c_478])).

tff(c_748,plain,(
    ~ r2_hidden('#skF_11','#skF_15') ),
    inference(splitLeft,[status(thm)],[c_747])).

tff(c_96,plain,(
    ! [F_52,D_56,E_54,B_53,C_57,A_55] :
      ( r2_hidden(B_53,E_54)
      | ~ r2_hidden(k3_mcart_1(A_55,B_53,C_57),k3_zfmisc_1(D_56,E_54,F_52)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_162,plain,(
    ! [C_96,C_95,A_92,D_94,B_91,B_90,A_93] :
      ( r2_hidden(B_91,C_95)
      | ~ r2_hidden(k3_mcart_1(A_93,B_91,C_96),k4_zfmisc_1(A_92,B_90,C_95,D_94)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_96])).

tff(c_753,plain,(
    ! [C_364,C_365,A_363,C_361,A_359,B_366,D_360,B_362] :
      ( r2_hidden(C_361,C_364)
      | ~ r2_hidden(k4_mcart_1(A_359,B_366,C_361,C_365),k4_zfmisc_1(A_363,B_362,C_364,D_360)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_105,c_162])).

tff(c_756,plain,(
    r2_hidden('#skF_11','#skF_15') ),
    inference(resolution,[status(thm)],[c_104,c_753])).

tff(c_760,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_748,c_756])).

tff(c_762,plain,(
    r2_hidden('#skF_11','#skF_15') ),
    inference(splitRight,[status(thm)],[c_747])).

tff(c_479,plain,(
    r2_hidden('#skF_12','#skF_16') ),
    inference(splitRight,[status(thm)],[c_467])).

tff(c_30,plain,
    ( r2_hidden('#skF_1','#skF_5')
    | ~ r2_hidden('#skF_12','#skF_16')
    | ~ r2_hidden('#skF_11','#skF_15')
    | ~ r2_hidden('#skF_10','#skF_14')
    | ~ r2_hidden('#skF_9','#skF_13') ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_812,plain,(
    r2_hidden('#skF_1','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_468,c_745,c_762,c_479,c_30])).

tff(c_744,plain,
    ( ~ r2_hidden('#skF_11','#skF_15')
    | ~ r2_hidden('#skF_12','#skF_16')
    | r2_hidden('#skF_2','#skF_6') ),
    inference(splitRight,[status(thm)],[c_481])).

tff(c_766,plain,(
    r2_hidden('#skF_2','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_479,c_762,c_744])).

tff(c_6,plain,(
    ! [A_8,B_9,C_10,D_11] :
      ( r2_hidden(k4_tarski(A_8,B_9),k2_zfmisc_1(C_10,D_11))
      | ~ r2_hidden(B_9,D_11)
      | ~ r2_hidden(A_8,C_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_26,plain,
    ( r2_hidden('#skF_3','#skF_7')
    | ~ r2_hidden('#skF_12','#skF_16')
    | ~ r2_hidden('#skF_11','#skF_15')
    | ~ r2_hidden('#skF_10','#skF_14')
    | ~ r2_hidden('#skF_9','#skF_13') ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_764,plain,(
    r2_hidden('#skF_3','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_468,c_745,c_762,c_479,c_26])).

tff(c_761,plain,(
    r2_hidden('#skF_4','#skF_8') ),
    inference(splitRight,[status(thm)],[c_747])).

tff(c_849,plain,(
    ! [A_427,B_425,F_424,E_426,C_429,D_428] :
      ( r2_hidden(k3_mcart_1(A_427,B_425,C_429),k3_zfmisc_1(D_428,E_426,F_424))
      | ~ r2_hidden(C_429,F_424)
      | ~ r2_hidden(B_425,E_426)
      | ~ r2_hidden(A_427,D_428) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_1008,plain,(
    ! [C_487,A_483,D_485,B_481,B_482,C_486,A_484] :
      ( r2_hidden(k3_mcart_1(A_483,B_482,C_487),k4_zfmisc_1(A_484,B_481,C_486,D_485))
      | ~ r2_hidden(C_487,D_485)
      | ~ r2_hidden(B_482,C_486)
      | ~ r2_hidden(A_483,k2_zfmisc_1(A_484,B_481)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_849])).

tff(c_1063,plain,(
    ! [B_511,A_506,C_510,B_507,C_505,A_504,D_508,C_509] :
      ( r2_hidden(k4_mcart_1(A_504,B_511,C_505,C_510),k4_zfmisc_1(A_506,B_507,C_509,D_508))
      | ~ r2_hidden(C_510,D_508)
      | ~ r2_hidden(C_505,C_509)
      | ~ r2_hidden(k4_tarski(A_504,B_511),k2_zfmisc_1(A_506,B_507)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_105,c_1008])).

tff(c_22,plain,
    ( ~ r2_hidden(k4_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4'),k4_zfmisc_1('#skF_5','#skF_6','#skF_7','#skF_8'))
    | ~ r2_hidden('#skF_12','#skF_16')
    | ~ r2_hidden('#skF_11','#skF_15')
    | ~ r2_hidden('#skF_10','#skF_14')
    | ~ r2_hidden('#skF_9','#skF_13') ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_889,plain,(
    ~ r2_hidden(k4_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4'),k4_zfmisc_1('#skF_5','#skF_6','#skF_7','#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_468,c_745,c_762,c_479,c_22])).

tff(c_1069,plain,
    ( ~ r2_hidden('#skF_4','#skF_8')
    | ~ r2_hidden('#skF_3','#skF_7')
    | ~ r2_hidden(k4_tarski('#skF_1','#skF_2'),k2_zfmisc_1('#skF_5','#skF_6')) ),
    inference(resolution,[status(thm)],[c_1063,c_889])).

tff(c_1085,plain,(
    ~ r2_hidden(k4_tarski('#skF_1','#skF_2'),k2_zfmisc_1('#skF_5','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_764,c_761,c_1069])).

tff(c_1092,plain,
    ( ~ r2_hidden('#skF_2','#skF_6')
    | ~ r2_hidden('#skF_1','#skF_5') ),
    inference(resolution,[status(thm)],[c_6,c_1085])).

tff(c_1096,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_812,c_766,c_1092])).

tff(c_1098,plain,(
    ~ r2_hidden(k4_mcart_1('#skF_9','#skF_10','#skF_11','#skF_12'),k4_zfmisc_1('#skF_13','#skF_14','#skF_15','#skF_16')) ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_40,plain,
    ( r2_hidden('#skF_1','#skF_5')
    | r2_hidden(k4_mcart_1('#skF_9','#skF_10','#skF_11','#skF_12'),k4_zfmisc_1('#skF_13','#skF_14','#skF_15','#skF_16')) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_1099,plain,(
    r2_hidden('#skF_1','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_1098,c_40])).

tff(c_38,plain,
    ( r2_hidden('#skF_2','#skF_6')
    | r2_hidden(k4_mcart_1('#skF_9','#skF_10','#skF_11','#skF_12'),k4_zfmisc_1('#skF_13','#skF_14','#skF_15','#skF_16')) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_1148,plain,(
    r2_hidden('#skF_2','#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_1098,c_38])).

tff(c_36,plain,
    ( r2_hidden('#skF_3','#skF_7')
    | r2_hidden(k4_mcart_1('#skF_9','#skF_10','#skF_11','#skF_12'),k4_zfmisc_1('#skF_13','#skF_14','#skF_15','#skF_16')) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_1162,plain,(
    r2_hidden('#skF_3','#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_1098,c_36])).

tff(c_1097,plain,(
    r2_hidden('#skF_4','#skF_8') ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_1100,plain,(
    ! [A_22,B_23,C_24,C_3] : k3_mcart_1(k4_tarski(A_22,B_23),C_24,C_3) = k4_mcart_1(A_22,B_23,C_24,C_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_44])).

tff(c_1268,plain,(
    ! [F_598,C_603,E_600,A_601,B_599,D_602] :
      ( r2_hidden(k3_mcart_1(A_601,B_599,C_603),k3_zfmisc_1(D_602,E_600,F_598))
      | ~ r2_hidden(C_603,F_598)
      | ~ r2_hidden(B_599,E_600)
      | ~ r2_hidden(A_601,D_602) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_1438,plain,(
    ! [B_681,A_679,D_680,C_684,B_678,A_683,C_682] :
      ( r2_hidden(k3_mcart_1(A_683,B_681,C_684),k4_zfmisc_1(A_679,B_678,C_682,D_680))
      | ~ r2_hidden(C_684,D_680)
      | ~ r2_hidden(B_681,C_682)
      | ~ r2_hidden(A_683,k2_zfmisc_1(A_679,B_678)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_1268])).

tff(c_1514,plain,(
    ! [A_716,A_709,B_713,C_712,C_714,D_711,C_710,B_715] :
      ( r2_hidden(k4_mcart_1(A_709,B_715,C_710,C_714),k4_zfmisc_1(A_716,B_713,C_712,D_711))
      | ~ r2_hidden(C_714,D_711)
      | ~ r2_hidden(C_710,C_712)
      | ~ r2_hidden(k4_tarski(A_709,B_715),k2_zfmisc_1(A_716,B_713)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1100,c_1438])).

tff(c_32,plain,
    ( ~ r2_hidden(k4_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4'),k4_zfmisc_1('#skF_5','#skF_6','#skF_7','#skF_8'))
    | r2_hidden(k4_mcart_1('#skF_9','#skF_10','#skF_11','#skF_12'),k4_zfmisc_1('#skF_13','#skF_14','#skF_15','#skF_16')) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_1305,plain,(
    ~ r2_hidden(k4_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4'),k4_zfmisc_1('#skF_5','#skF_6','#skF_7','#skF_8')) ),
    inference(negUnitSimplification,[status(thm)],[c_1098,c_32])).

tff(c_1520,plain,
    ( ~ r2_hidden('#skF_4','#skF_8')
    | ~ r2_hidden('#skF_3','#skF_7')
    | ~ r2_hidden(k4_tarski('#skF_1','#skF_2'),k2_zfmisc_1('#skF_5','#skF_6')) ),
    inference(resolution,[status(thm)],[c_1514,c_1305])).

tff(c_1539,plain,(
    ~ r2_hidden(k4_tarski('#skF_1','#skF_2'),k2_zfmisc_1('#skF_5','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1162,c_1097,c_1520])).

tff(c_1547,plain,
    ( ~ r2_hidden('#skF_2','#skF_6')
    | ~ r2_hidden('#skF_1','#skF_5') ),
    inference(resolution,[status(thm)],[c_6,c_1539])).

tff(c_1551,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1099,c_1148,c_1547])).

%------------------------------------------------------------------------------

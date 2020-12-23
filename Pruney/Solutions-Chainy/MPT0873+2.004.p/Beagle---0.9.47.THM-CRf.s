%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:09:27 EST 2020

% Result     : Theorem 3.56s
% Output     : CNFRefutation 3.56s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 223 expanded)
%              Number of leaves         :   19 (  76 expanded)
%              Depth                    :   13
%              Number of atoms          :  120 ( 393 expanded)
%              Number of equality atoms :  116 ( 389 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k4_mcart_1 > k3_mcart_1 > k4_tarski > #nlpp > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_8 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k3_mcart_1,type,(
    k3_mcart_1: ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k4_mcart_1,type,(
    k4_mcart_1: ( $i * $i * $i * $i ) > $i )).

tff(f_54,negated_conjecture,(
    ~ ! [A,B,C,D,E,F,G,H] :
        ( k4_mcart_1(A,B,C,D) = k4_mcart_1(E,F,G,H)
       => ( A = E
          & B = F
          & C = G
          & D = H ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_mcart_1)).

tff(f_35,axiom,(
    ! [A,B,C,D] : k4_mcart_1(A,B,C,D) = k4_tarski(k3_mcart_1(A,B,C),D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_mcart_1)).

tff(f_33,axiom,(
    ! [A,B,C] : k3_mcart_1(A,B,C) = k4_tarski(k4_tarski(A,B),C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_mcart_1)).

tff(f_43,axiom,(
    ! [A,B,C,D,E,F] :
      ( k3_mcart_1(A,B,C) = k3_mcart_1(D,E,F)
     => ( A = D
        & B = E
        & C = F ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_mcart_1)).

tff(f_31,axiom,(
    ! [A,B,C,D] :
      ( k4_tarski(A,B) = k4_tarski(C,D)
     => ( A = C
        & B = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_zfmisc_1)).

tff(c_16,plain,
    ( '#skF_8' != '#skF_4'
    | '#skF_7' != '#skF_3'
    | '#skF_6' != '#skF_2'
    | '#skF_5' != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_19,plain,(
    '#skF_5' != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_16])).

tff(c_8,plain,(
    ! [A_8,B_9,C_10,D_11] : k4_tarski(k3_mcart_1(A_8,B_9,C_10),D_11) = k4_mcart_1(A_8,B_9,C_10,D_11) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_6,plain,(
    ! [A_5,B_6,C_7] : k4_tarski(k4_tarski(A_5,B_6),C_7) = k3_mcart_1(A_5,B_6,C_7) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_30,plain,(
    ! [A_26,B_27,C_28] : k4_tarski(k4_tarski(A_26,B_27),C_28) = k3_mcart_1(A_26,B_27,C_28) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_51,plain,(
    ! [A_5,B_6,C_7,C_28] : k3_mcart_1(k4_tarski(A_5,B_6),C_7,C_28) = k4_tarski(k3_mcart_1(A_5,B_6,C_7),C_28) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_30])).

tff(c_136,plain,(
    ! [A_5,B_6,C_7,C_28] : k3_mcart_1(k4_tarski(A_5,B_6),C_7,C_28) = k4_mcart_1(A_5,B_6,C_7,C_28) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_51])).

tff(c_18,plain,(
    k4_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8') = k4_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_137,plain,(
    ! [A_79,B_80,C_81,C_82] : k3_mcart_1(k4_tarski(A_79,B_80),C_81,C_82) = k4_mcart_1(A_79,B_80,C_81,C_82) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_51])).

tff(c_12,plain,(
    ! [E_16,D_15,F_17,C_14,A_12,B_13] :
      ( E_16 = B_13
      | k3_mcart_1(D_15,E_16,F_17) != k3_mcart_1(A_12,B_13,C_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_186,plain,(
    ! [C_85,B_83,B_89,C_87,A_84,C_88,A_86] :
      ( C_87 = B_83
      | k4_mcart_1(A_86,B_89,C_87,C_85) != k3_mcart_1(A_84,B_83,C_88) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_137,c_12])).

tff(c_194,plain,(
    ! [B_90,A_91,C_92] :
      ( B_90 = '#skF_7'
      | k4_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4') != k3_mcart_1(A_91,B_90,C_92) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_186])).

tff(c_197,plain,(
    ! [C_7,A_5,B_6,C_28] :
      ( C_7 = '#skF_7'
      | k4_mcart_1(A_5,B_6,C_7,C_28) != k4_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_136,c_194])).

tff(c_270,plain,(
    '#skF_7' = '#skF_3' ),
    inference(reflexivity,[status(thm),theory(equality)],[c_197])).

tff(c_80,plain,(
    ! [A_52,B_53,C_54,D_55] : k4_tarski(k3_mcart_1(A_52,B_53,C_54),D_55) = k4_mcart_1(A_52,B_53,C_54,D_55) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_2,plain,(
    ! [D_4,B_2,C_3,A_1] :
      ( D_4 = B_2
      | k4_tarski(C_3,D_4) != k4_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_107,plain,(
    ! [A_60,D_59,A_56,B_57,C_61,B_58] :
      ( D_59 = B_58
      | k4_tarski(A_60,B_58) != k4_mcart_1(A_56,B_57,C_61,D_59) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_80,c_2])).

tff(c_124,plain,(
    ! [B_67,A_68] :
      ( B_67 = '#skF_8'
      | k4_tarski(A_68,B_67) != k4_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_107])).

tff(c_127,plain,(
    ! [D_11,A_8,B_9,C_10] :
      ( D_11 = '#skF_8'
      | k4_mcart_1(A_8,B_9,C_10,D_11) != k4_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_124])).

tff(c_211,plain,(
    '#skF_8' = '#skF_4' ),
    inference(reflexivity,[status(thm),theory(equality)],[c_127])).

tff(c_221,plain,(
    k4_mcart_1('#skF_5','#skF_6','#skF_7','#skF_4') = k4_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_211,c_18])).

tff(c_278,plain,(
    k4_mcart_1('#skF_5','#skF_6','#skF_3','#skF_4') = k4_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_270,c_221])).

tff(c_14,plain,(
    ! [E_16,D_15,F_17,C_14,A_12,B_13] :
      ( D_15 = A_12
      | k3_mcart_1(D_15,E_16,F_17) != k3_mcart_1(A_12,B_13,C_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_314,plain,(
    ! [A_124,C_128,B_129,C_125,A_126,C_127,B_123] :
      ( k4_tarski(A_126,B_129) = A_124
      | k4_mcart_1(A_126,B_129,C_127,C_125) != k3_mcart_1(A_124,B_123,C_128) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_137,c_14])).

tff(c_595,plain,(
    ! [C_193,C_199,C_194,B_196,C_197,A_192,A_198,B_195] :
      ( k4_tarski(A_198,B_196) = k4_tarski(A_192,B_195)
      | k4_mcart_1(A_198,B_196,C_197,C_199) != k4_mcart_1(A_192,B_195,C_194,C_193) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_136,c_314])).

tff(c_610,plain,(
    ! [A_192,B_195,C_194,C_193] :
      ( k4_tarski(A_192,B_195) = k4_tarski('#skF_5','#skF_6')
      | k4_mcart_1(A_192,B_195,C_194,C_193) != k4_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_278,c_595])).

tff(c_655,plain,(
    k4_tarski('#skF_5','#skF_6') = k4_tarski('#skF_1','#skF_2') ),
    inference(reflexivity,[status(thm),theory(equality)],[c_610])).

tff(c_4,plain,(
    ! [C_3,A_1,D_4,B_2] :
      ( C_3 = A_1
      | k4_tarski(C_3,D_4) != k4_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_694,plain,(
    ! [C_3,D_4] :
      ( C_3 = '#skF_5'
      | k4_tarski(C_3,D_4) != k4_tarski('#skF_1','#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_655,c_4])).

tff(c_832,plain,(
    '#skF_5' = '#skF_1' ),
    inference(reflexivity,[status(thm),theory(equality)],[c_694])).

tff(c_834,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_19,c_832])).

tff(c_835,plain,
    ( '#skF_6' != '#skF_2'
    | '#skF_7' != '#skF_3'
    | '#skF_8' != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_16])).

tff(c_841,plain,(
    '#skF_8' != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_835])).

tff(c_836,plain,(
    '#skF_5' = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_16])).

tff(c_852,plain,(
    k4_mcart_1('#skF_1','#skF_6','#skF_7','#skF_8') = k4_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_836,c_18])).

tff(c_903,plain,(
    ! [A_255,B_256,C_257,D_258] : k4_tarski(k3_mcart_1(A_255,B_256,C_257),D_258) = k4_mcart_1(A_255,B_256,C_257,D_258) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_930,plain,(
    ! [B_259,A_261,C_260,D_262,A_264,B_263] :
      ( D_262 = B_263
      | k4_tarski(A_264,B_263) != k4_mcart_1(A_261,B_259,C_260,D_262) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_903,c_2])).

tff(c_940,plain,(
    ! [B_265,A_266] :
      ( B_265 = '#skF_8'
      | k4_tarski(A_266,B_265) != k4_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_852,c_930])).

tff(c_943,plain,(
    ! [D_11,A_8,B_9,C_10] :
      ( D_11 = '#skF_8'
      | k4_mcart_1(A_8,B_9,C_10,D_11) != k4_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_940])).

tff(c_1034,plain,(
    '#skF_8' = '#skF_4' ),
    inference(reflexivity,[status(thm),theory(equality)],[c_943])).

tff(c_1036,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_841,c_1034])).

tff(c_1037,plain,
    ( '#skF_7' != '#skF_3'
    | '#skF_6' != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_835])).

tff(c_1043,plain,(
    '#skF_6' != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_1037])).

tff(c_1059,plain,(
    ! [A_312,B_313,C_314] : k4_tarski(k4_tarski(A_312,B_313),C_314) = k3_mcart_1(A_312,B_313,C_314) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_1062,plain,(
    ! [A_312,B_313,C_314,C_7] : k3_mcart_1(k4_tarski(A_312,B_313),C_314,C_7) = k4_tarski(k3_mcart_1(A_312,B_313,C_314),C_7) ),
    inference(superposition,[status(thm),theory(equality)],[c_1059,c_6])).

tff(c_1153,plain,(
    ! [A_312,B_313,C_314,C_7] : k3_mcart_1(k4_tarski(A_312,B_313),C_314,C_7) = k4_mcart_1(A_312,B_313,C_314,C_7) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_1062])).

tff(c_1038,plain,(
    '#skF_8' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_835])).

tff(c_1054,plain,(
    k4_mcart_1('#skF_1','#skF_6','#skF_7','#skF_4') = k4_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1038,c_836,c_18])).

tff(c_1154,plain,(
    ! [A_360,B_361,C_362,C_363] : k3_mcart_1(k4_tarski(A_360,B_361),C_362,C_363) = k4_mcart_1(A_360,B_361,C_362,C_363) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_1062])).

tff(c_1201,plain,(
    ! [C_367,C_368,A_369,A_366,C_370,B_364,B_365] :
      ( C_367 = B_364
      | k4_mcart_1(A_369,B_365,C_367,C_368) != k3_mcart_1(A_366,B_364,C_370) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1154,c_12])).

tff(c_1208,plain,(
    ! [B_371,A_372,C_373] :
      ( B_371 = '#skF_7'
      | k4_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4') != k3_mcart_1(A_372,B_371,C_373) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1054,c_1201])).

tff(c_1211,plain,(
    ! [C_314,A_312,B_313,C_7] :
      ( C_314 = '#skF_7'
      | k4_mcart_1(A_312,B_313,C_314,C_7) != k4_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1153,c_1208])).

tff(c_1214,plain,(
    '#skF_7' = '#skF_3' ),
    inference(reflexivity,[status(thm),theory(equality)],[c_1211])).

tff(c_1223,plain,(
    k4_mcart_1('#skF_1','#skF_6','#skF_3','#skF_4') = k4_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1214,c_1054])).

tff(c_1280,plain,(
    ! [C_405,E_403,B_402,A_407,F_408,D_406,C_404] :
      ( k4_tarski(A_407,B_402) = D_406
      | k4_mcart_1(A_407,B_402,C_404,C_405) != k3_mcart_1(D_406,E_403,F_408) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1154,c_14])).

tff(c_1560,plain,(
    ! [C_479,C_473,C_478,A_474,B_477,C_475,A_480,B_476] :
      ( k4_tarski(A_480,B_477) = k4_tarski(A_474,B_476)
      | k4_mcart_1(A_480,B_477,C_475,C_479) != k4_mcart_1(A_474,B_476,C_473,C_478) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1153,c_1280])).

tff(c_1575,plain,(
    ! [A_474,B_476,C_473,C_478] :
      ( k4_tarski(A_474,B_476) = k4_tarski('#skF_1','#skF_6')
      | k4_mcart_1(A_474,B_476,C_473,C_478) != k4_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1223,c_1560])).

tff(c_1614,plain,(
    k4_tarski('#skF_1','#skF_6') = k4_tarski('#skF_1','#skF_2') ),
    inference(reflexivity,[status(thm),theory(equality)],[c_1575])).

tff(c_1643,plain,(
    ! [B_2,A_1] :
      ( B_2 = '#skF_6'
      | k4_tarski(A_1,B_2) != k4_tarski('#skF_1','#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1614,c_2])).

tff(c_1737,plain,(
    '#skF_6' = '#skF_2' ),
    inference(reflexivity,[status(thm),theory(equality)],[c_1643])).

tff(c_1739,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1043,c_1737])).

tff(c_1740,plain,(
    '#skF_7' != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_1037])).

tff(c_1741,plain,(
    '#skF_6' = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_1037])).

tff(c_1787,plain,(
    k4_mcart_1('#skF_1','#skF_2','#skF_7','#skF_4') = k4_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1741,c_836,c_1038,c_18])).

tff(c_1756,plain,(
    ! [A_504,B_505,C_506] : k4_tarski(k4_tarski(A_504,B_505),C_506) = k3_mcart_1(A_504,B_505,C_506) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_1777,plain,(
    ! [A_5,B_6,C_7,C_506] : k3_mcart_1(k4_tarski(A_5,B_6),C_7,C_506) = k4_tarski(k3_mcart_1(A_5,B_6,C_7),C_506) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_1756])).

tff(c_1855,plain,(
    ! [A_5,B_6,C_7,C_506] : k3_mcart_1(k4_tarski(A_5,B_6),C_7,C_506) = k4_mcart_1(A_5,B_6,C_7,C_506) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_1777])).

tff(c_1856,plain,(
    ! [A_552,B_553,C_554,C_555] : k3_mcart_1(k4_tarski(A_552,B_553),C_554,C_555) = k4_mcart_1(A_552,B_553,C_554,C_555) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_1777])).

tff(c_1902,plain,(
    ! [C_562,A_558,A_559,C_560,B_561,C_557,B_556] :
      ( C_557 = B_556
      | k4_mcart_1(A_558,B_561,C_557,C_560) != k3_mcart_1(A_559,B_556,C_562) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1856,c_12])).

tff(c_1929,plain,(
    ! [B_576,C_579,A_578,C_577,C_575,C_574,A_580,B_581] :
      ( C_579 = C_577
      | k4_mcart_1(A_580,B_576,C_579,C_575) != k4_mcart_1(A_578,B_581,C_577,C_574) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1855,c_1902])).

tff(c_1935,plain,(
    ! [C_579,A_580,B_576,C_575] :
      ( C_579 = '#skF_7'
      | k4_mcart_1(A_580,B_576,C_579,C_575) != k4_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1787,c_1929])).

tff(c_1938,plain,(
    '#skF_7' = '#skF_3' ),
    inference(reflexivity,[status(thm),theory(equality)],[c_1935])).

tff(c_1940,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1740,c_1938])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:30:29 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.56/1.59  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.56/1.59  
% 3.56/1.59  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.56/1.60  %$ k4_mcart_1 > k3_mcart_1 > k4_tarski > #nlpp > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_8 > #skF_4
% 3.56/1.60  
% 3.56/1.60  %Foreground sorts:
% 3.56/1.60  
% 3.56/1.60  
% 3.56/1.60  %Background operators:
% 3.56/1.60  
% 3.56/1.60  
% 3.56/1.60  %Foreground operators:
% 3.56/1.60  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.56/1.60  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.56/1.60  tff(k3_mcart_1, type, k3_mcart_1: ($i * $i * $i) > $i).
% 3.56/1.60  tff('#skF_7', type, '#skF_7': $i).
% 3.56/1.60  tff('#skF_5', type, '#skF_5': $i).
% 3.56/1.60  tff('#skF_6', type, '#skF_6': $i).
% 3.56/1.60  tff('#skF_2', type, '#skF_2': $i).
% 3.56/1.60  tff('#skF_3', type, '#skF_3': $i).
% 3.56/1.60  tff('#skF_1', type, '#skF_1': $i).
% 3.56/1.60  tff('#skF_8', type, '#skF_8': $i).
% 3.56/1.60  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.56/1.60  tff('#skF_4', type, '#skF_4': $i).
% 3.56/1.60  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.56/1.60  tff(k4_mcart_1, type, k4_mcart_1: ($i * $i * $i * $i) > $i).
% 3.56/1.60  
% 3.56/1.61  tff(f_54, negated_conjecture, ~(![A, B, C, D, E, F, G, H]: ((k4_mcart_1(A, B, C, D) = k4_mcart_1(E, F, G, H)) => ((((A = E) & (B = F)) & (C = G)) & (D = H)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t33_mcart_1)).
% 3.56/1.61  tff(f_35, axiom, (![A, B, C, D]: (k4_mcart_1(A, B, C, D) = k4_tarski(k3_mcart_1(A, B, C), D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_mcart_1)).
% 3.56/1.61  tff(f_33, axiom, (![A, B, C]: (k3_mcart_1(A, B, C) = k4_tarski(k4_tarski(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_mcart_1)).
% 3.56/1.61  tff(f_43, axiom, (![A, B, C, D, E, F]: ((k3_mcart_1(A, B, C) = k3_mcart_1(D, E, F)) => (((A = D) & (B = E)) & (C = F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_mcart_1)).
% 3.56/1.61  tff(f_31, axiom, (![A, B, C, D]: ((k4_tarski(A, B) = k4_tarski(C, D)) => ((A = C) & (B = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t33_zfmisc_1)).
% 3.56/1.61  tff(c_16, plain, ('#skF_8'!='#skF_4' | '#skF_7'!='#skF_3' | '#skF_6'!='#skF_2' | '#skF_5'!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.56/1.61  tff(c_19, plain, ('#skF_5'!='#skF_1'), inference(splitLeft, [status(thm)], [c_16])).
% 3.56/1.61  tff(c_8, plain, (![A_8, B_9, C_10, D_11]: (k4_tarski(k3_mcart_1(A_8, B_9, C_10), D_11)=k4_mcart_1(A_8, B_9, C_10, D_11))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.56/1.61  tff(c_6, plain, (![A_5, B_6, C_7]: (k4_tarski(k4_tarski(A_5, B_6), C_7)=k3_mcart_1(A_5, B_6, C_7))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.56/1.61  tff(c_30, plain, (![A_26, B_27, C_28]: (k4_tarski(k4_tarski(A_26, B_27), C_28)=k3_mcart_1(A_26, B_27, C_28))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.56/1.61  tff(c_51, plain, (![A_5, B_6, C_7, C_28]: (k3_mcart_1(k4_tarski(A_5, B_6), C_7, C_28)=k4_tarski(k3_mcart_1(A_5, B_6, C_7), C_28))), inference(superposition, [status(thm), theory('equality')], [c_6, c_30])).
% 3.56/1.61  tff(c_136, plain, (![A_5, B_6, C_7, C_28]: (k3_mcart_1(k4_tarski(A_5, B_6), C_7, C_28)=k4_mcart_1(A_5, B_6, C_7, C_28))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_51])).
% 3.56/1.61  tff(c_18, plain, (k4_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8')=k4_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.56/1.61  tff(c_137, plain, (![A_79, B_80, C_81, C_82]: (k3_mcart_1(k4_tarski(A_79, B_80), C_81, C_82)=k4_mcart_1(A_79, B_80, C_81, C_82))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_51])).
% 3.56/1.61  tff(c_12, plain, (![E_16, D_15, F_17, C_14, A_12, B_13]: (E_16=B_13 | k3_mcart_1(D_15, E_16, F_17)!=k3_mcart_1(A_12, B_13, C_14))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.56/1.61  tff(c_186, plain, (![C_85, B_83, B_89, C_87, A_84, C_88, A_86]: (C_87=B_83 | k4_mcart_1(A_86, B_89, C_87, C_85)!=k3_mcart_1(A_84, B_83, C_88))), inference(superposition, [status(thm), theory('equality')], [c_137, c_12])).
% 3.56/1.61  tff(c_194, plain, (![B_90, A_91, C_92]: (B_90='#skF_7' | k4_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k3_mcart_1(A_91, B_90, C_92))), inference(superposition, [status(thm), theory('equality')], [c_18, c_186])).
% 3.56/1.61  tff(c_197, plain, (![C_7, A_5, B_6, C_28]: (C_7='#skF_7' | k4_mcart_1(A_5, B_6, C_7, C_28)!=k4_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_136, c_194])).
% 3.56/1.61  tff(c_270, plain, ('#skF_7'='#skF_3'), inference(reflexivity, [status(thm), theory('equality')], [c_197])).
% 3.56/1.61  tff(c_80, plain, (![A_52, B_53, C_54, D_55]: (k4_tarski(k3_mcart_1(A_52, B_53, C_54), D_55)=k4_mcart_1(A_52, B_53, C_54, D_55))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.56/1.61  tff(c_2, plain, (![D_4, B_2, C_3, A_1]: (D_4=B_2 | k4_tarski(C_3, D_4)!=k4_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.56/1.61  tff(c_107, plain, (![A_60, D_59, A_56, B_57, C_61, B_58]: (D_59=B_58 | k4_tarski(A_60, B_58)!=k4_mcart_1(A_56, B_57, C_61, D_59))), inference(superposition, [status(thm), theory('equality')], [c_80, c_2])).
% 3.56/1.61  tff(c_124, plain, (![B_67, A_68]: (B_67='#skF_8' | k4_tarski(A_68, B_67)!=k4_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_18, c_107])).
% 3.56/1.61  tff(c_127, plain, (![D_11, A_8, B_9, C_10]: (D_11='#skF_8' | k4_mcart_1(A_8, B_9, C_10, D_11)!=k4_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_8, c_124])).
% 3.56/1.61  tff(c_211, plain, ('#skF_8'='#skF_4'), inference(reflexivity, [status(thm), theory('equality')], [c_127])).
% 3.56/1.61  tff(c_221, plain, (k4_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_4')=k4_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_211, c_18])).
% 3.56/1.61  tff(c_278, plain, (k4_mcart_1('#skF_5', '#skF_6', '#skF_3', '#skF_4')=k4_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_270, c_221])).
% 3.56/1.61  tff(c_14, plain, (![E_16, D_15, F_17, C_14, A_12, B_13]: (D_15=A_12 | k3_mcart_1(D_15, E_16, F_17)!=k3_mcart_1(A_12, B_13, C_14))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.56/1.61  tff(c_314, plain, (![A_124, C_128, B_129, C_125, A_126, C_127, B_123]: (k4_tarski(A_126, B_129)=A_124 | k4_mcart_1(A_126, B_129, C_127, C_125)!=k3_mcart_1(A_124, B_123, C_128))), inference(superposition, [status(thm), theory('equality')], [c_137, c_14])).
% 3.56/1.61  tff(c_595, plain, (![C_193, C_199, C_194, B_196, C_197, A_192, A_198, B_195]: (k4_tarski(A_198, B_196)=k4_tarski(A_192, B_195) | k4_mcart_1(A_198, B_196, C_197, C_199)!=k4_mcart_1(A_192, B_195, C_194, C_193))), inference(superposition, [status(thm), theory('equality')], [c_136, c_314])).
% 3.56/1.61  tff(c_610, plain, (![A_192, B_195, C_194, C_193]: (k4_tarski(A_192, B_195)=k4_tarski('#skF_5', '#skF_6') | k4_mcart_1(A_192, B_195, C_194, C_193)!=k4_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_278, c_595])).
% 3.56/1.61  tff(c_655, plain, (k4_tarski('#skF_5', '#skF_6')=k4_tarski('#skF_1', '#skF_2')), inference(reflexivity, [status(thm), theory('equality')], [c_610])).
% 3.56/1.61  tff(c_4, plain, (![C_3, A_1, D_4, B_2]: (C_3=A_1 | k4_tarski(C_3, D_4)!=k4_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.56/1.61  tff(c_694, plain, (![C_3, D_4]: (C_3='#skF_5' | k4_tarski(C_3, D_4)!=k4_tarski('#skF_1', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_655, c_4])).
% 3.56/1.61  tff(c_832, plain, ('#skF_5'='#skF_1'), inference(reflexivity, [status(thm), theory('equality')], [c_694])).
% 3.56/1.61  tff(c_834, plain, $false, inference(negUnitSimplification, [status(thm)], [c_19, c_832])).
% 3.56/1.61  tff(c_835, plain, ('#skF_6'!='#skF_2' | '#skF_7'!='#skF_3' | '#skF_8'!='#skF_4'), inference(splitRight, [status(thm)], [c_16])).
% 3.56/1.61  tff(c_841, plain, ('#skF_8'!='#skF_4'), inference(splitLeft, [status(thm)], [c_835])).
% 3.56/1.61  tff(c_836, plain, ('#skF_5'='#skF_1'), inference(splitRight, [status(thm)], [c_16])).
% 3.56/1.61  tff(c_852, plain, (k4_mcart_1('#skF_1', '#skF_6', '#skF_7', '#skF_8')=k4_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_836, c_18])).
% 3.56/1.61  tff(c_903, plain, (![A_255, B_256, C_257, D_258]: (k4_tarski(k3_mcart_1(A_255, B_256, C_257), D_258)=k4_mcart_1(A_255, B_256, C_257, D_258))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.56/1.61  tff(c_930, plain, (![B_259, A_261, C_260, D_262, A_264, B_263]: (D_262=B_263 | k4_tarski(A_264, B_263)!=k4_mcart_1(A_261, B_259, C_260, D_262))), inference(superposition, [status(thm), theory('equality')], [c_903, c_2])).
% 3.56/1.61  tff(c_940, plain, (![B_265, A_266]: (B_265='#skF_8' | k4_tarski(A_266, B_265)!=k4_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_852, c_930])).
% 3.56/1.61  tff(c_943, plain, (![D_11, A_8, B_9, C_10]: (D_11='#skF_8' | k4_mcart_1(A_8, B_9, C_10, D_11)!=k4_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_8, c_940])).
% 3.56/1.61  tff(c_1034, plain, ('#skF_8'='#skF_4'), inference(reflexivity, [status(thm), theory('equality')], [c_943])).
% 3.56/1.61  tff(c_1036, plain, $false, inference(negUnitSimplification, [status(thm)], [c_841, c_1034])).
% 3.56/1.61  tff(c_1037, plain, ('#skF_7'!='#skF_3' | '#skF_6'!='#skF_2'), inference(splitRight, [status(thm)], [c_835])).
% 3.56/1.61  tff(c_1043, plain, ('#skF_6'!='#skF_2'), inference(splitLeft, [status(thm)], [c_1037])).
% 3.56/1.61  tff(c_1059, plain, (![A_312, B_313, C_314]: (k4_tarski(k4_tarski(A_312, B_313), C_314)=k3_mcart_1(A_312, B_313, C_314))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.56/1.61  tff(c_1062, plain, (![A_312, B_313, C_314, C_7]: (k3_mcart_1(k4_tarski(A_312, B_313), C_314, C_7)=k4_tarski(k3_mcart_1(A_312, B_313, C_314), C_7))), inference(superposition, [status(thm), theory('equality')], [c_1059, c_6])).
% 3.56/1.61  tff(c_1153, plain, (![A_312, B_313, C_314, C_7]: (k3_mcart_1(k4_tarski(A_312, B_313), C_314, C_7)=k4_mcart_1(A_312, B_313, C_314, C_7))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_1062])).
% 3.56/1.61  tff(c_1038, plain, ('#skF_8'='#skF_4'), inference(splitRight, [status(thm)], [c_835])).
% 3.56/1.61  tff(c_1054, plain, (k4_mcart_1('#skF_1', '#skF_6', '#skF_7', '#skF_4')=k4_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1038, c_836, c_18])).
% 3.56/1.61  tff(c_1154, plain, (![A_360, B_361, C_362, C_363]: (k3_mcart_1(k4_tarski(A_360, B_361), C_362, C_363)=k4_mcart_1(A_360, B_361, C_362, C_363))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_1062])).
% 3.56/1.61  tff(c_1201, plain, (![C_367, C_368, A_369, A_366, C_370, B_364, B_365]: (C_367=B_364 | k4_mcart_1(A_369, B_365, C_367, C_368)!=k3_mcart_1(A_366, B_364, C_370))), inference(superposition, [status(thm), theory('equality')], [c_1154, c_12])).
% 3.56/1.61  tff(c_1208, plain, (![B_371, A_372, C_373]: (B_371='#skF_7' | k4_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k3_mcart_1(A_372, B_371, C_373))), inference(superposition, [status(thm), theory('equality')], [c_1054, c_1201])).
% 3.56/1.61  tff(c_1211, plain, (![C_314, A_312, B_313, C_7]: (C_314='#skF_7' | k4_mcart_1(A_312, B_313, C_314, C_7)!=k4_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_1153, c_1208])).
% 3.56/1.61  tff(c_1214, plain, ('#skF_7'='#skF_3'), inference(reflexivity, [status(thm), theory('equality')], [c_1211])).
% 3.56/1.61  tff(c_1223, plain, (k4_mcart_1('#skF_1', '#skF_6', '#skF_3', '#skF_4')=k4_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1214, c_1054])).
% 3.56/1.61  tff(c_1280, plain, (![C_405, E_403, B_402, A_407, F_408, D_406, C_404]: (k4_tarski(A_407, B_402)=D_406 | k4_mcart_1(A_407, B_402, C_404, C_405)!=k3_mcart_1(D_406, E_403, F_408))), inference(superposition, [status(thm), theory('equality')], [c_1154, c_14])).
% 3.56/1.61  tff(c_1560, plain, (![C_479, C_473, C_478, A_474, B_477, C_475, A_480, B_476]: (k4_tarski(A_480, B_477)=k4_tarski(A_474, B_476) | k4_mcart_1(A_480, B_477, C_475, C_479)!=k4_mcart_1(A_474, B_476, C_473, C_478))), inference(superposition, [status(thm), theory('equality')], [c_1153, c_1280])).
% 3.56/1.61  tff(c_1575, plain, (![A_474, B_476, C_473, C_478]: (k4_tarski(A_474, B_476)=k4_tarski('#skF_1', '#skF_6') | k4_mcart_1(A_474, B_476, C_473, C_478)!=k4_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_1223, c_1560])).
% 3.56/1.61  tff(c_1614, plain, (k4_tarski('#skF_1', '#skF_6')=k4_tarski('#skF_1', '#skF_2')), inference(reflexivity, [status(thm), theory('equality')], [c_1575])).
% 3.56/1.61  tff(c_1643, plain, (![B_2, A_1]: (B_2='#skF_6' | k4_tarski(A_1, B_2)!=k4_tarski('#skF_1', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_1614, c_2])).
% 3.56/1.61  tff(c_1737, plain, ('#skF_6'='#skF_2'), inference(reflexivity, [status(thm), theory('equality')], [c_1643])).
% 3.56/1.61  tff(c_1739, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1043, c_1737])).
% 3.56/1.61  tff(c_1740, plain, ('#skF_7'!='#skF_3'), inference(splitRight, [status(thm)], [c_1037])).
% 3.56/1.61  tff(c_1741, plain, ('#skF_6'='#skF_2'), inference(splitRight, [status(thm)], [c_1037])).
% 3.56/1.61  tff(c_1787, plain, (k4_mcart_1('#skF_1', '#skF_2', '#skF_7', '#skF_4')=k4_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1741, c_836, c_1038, c_18])).
% 3.56/1.61  tff(c_1756, plain, (![A_504, B_505, C_506]: (k4_tarski(k4_tarski(A_504, B_505), C_506)=k3_mcart_1(A_504, B_505, C_506))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.56/1.61  tff(c_1777, plain, (![A_5, B_6, C_7, C_506]: (k3_mcart_1(k4_tarski(A_5, B_6), C_7, C_506)=k4_tarski(k3_mcart_1(A_5, B_6, C_7), C_506))), inference(superposition, [status(thm), theory('equality')], [c_6, c_1756])).
% 3.56/1.61  tff(c_1855, plain, (![A_5, B_6, C_7, C_506]: (k3_mcart_1(k4_tarski(A_5, B_6), C_7, C_506)=k4_mcart_1(A_5, B_6, C_7, C_506))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_1777])).
% 3.56/1.61  tff(c_1856, plain, (![A_552, B_553, C_554, C_555]: (k3_mcart_1(k4_tarski(A_552, B_553), C_554, C_555)=k4_mcart_1(A_552, B_553, C_554, C_555))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_1777])).
% 3.56/1.61  tff(c_1902, plain, (![C_562, A_558, A_559, C_560, B_561, C_557, B_556]: (C_557=B_556 | k4_mcart_1(A_558, B_561, C_557, C_560)!=k3_mcart_1(A_559, B_556, C_562))), inference(superposition, [status(thm), theory('equality')], [c_1856, c_12])).
% 3.56/1.61  tff(c_1929, plain, (![B_576, C_579, A_578, C_577, C_575, C_574, A_580, B_581]: (C_579=C_577 | k4_mcart_1(A_580, B_576, C_579, C_575)!=k4_mcart_1(A_578, B_581, C_577, C_574))), inference(superposition, [status(thm), theory('equality')], [c_1855, c_1902])).
% 3.56/1.61  tff(c_1935, plain, (![C_579, A_580, B_576, C_575]: (C_579='#skF_7' | k4_mcart_1(A_580, B_576, C_579, C_575)!=k4_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_1787, c_1929])).
% 3.56/1.61  tff(c_1938, plain, ('#skF_7'='#skF_3'), inference(reflexivity, [status(thm), theory('equality')], [c_1935])).
% 3.56/1.61  tff(c_1940, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1740, c_1938])).
% 3.56/1.61  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.56/1.61  
% 3.56/1.61  Inference rules
% 3.56/1.61  ----------------------
% 3.56/1.61  #Ref     : 43
% 3.56/1.61  #Sup     : 489
% 3.56/1.61  #Fact    : 0
% 3.56/1.61  #Define  : 0
% 3.56/1.61  #Split   : 3
% 3.56/1.61  #Chain   : 0
% 3.56/1.61  #Close   : 0
% 3.56/1.61  
% 3.56/1.61  Ordering : KBO
% 3.56/1.61  
% 3.56/1.61  Simplification rules
% 3.56/1.61  ----------------------
% 3.56/1.61  #Subsume      : 230
% 3.56/1.61  #Demod        : 174
% 3.56/1.61  #Tautology    : 129
% 3.56/1.61  #SimpNegUnit  : 4
% 3.56/1.61  #BackRed      : 24
% 3.56/1.61  
% 3.56/1.61  #Partial instantiations: 0
% 3.56/1.61  #Strategies tried      : 1
% 3.56/1.61  
% 3.56/1.61  Timing (in seconds)
% 3.56/1.61  ----------------------
% 3.56/1.62  Preprocessing        : 0.26
% 3.56/1.62  Parsing              : 0.13
% 3.56/1.62  CNF conversion       : 0.02
% 3.56/1.62  Main loop            : 0.58
% 3.56/1.62  Inferencing          : 0.21
% 3.56/1.62  Reduction            : 0.15
% 3.56/1.62  Demodulation         : 0.10
% 3.56/1.62  BG Simplification    : 0.03
% 3.56/1.62  Subsumption          : 0.16
% 3.56/1.62  Abstraction          : 0.04
% 3.56/1.62  MUC search           : 0.00
% 3.56/1.62  Cooper               : 0.00
% 3.56/1.62  Total                : 0.88
% 3.56/1.62  Index Insertion      : 0.00
% 3.56/1.62  Index Deletion       : 0.00
% 3.56/1.62  Index Matching       : 0.00
% 3.56/1.62  BG Taut test         : 0.00
%------------------------------------------------------------------------------

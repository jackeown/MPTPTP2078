%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:54:18 EST 2020

% Result     : Theorem 6.73s
% Output     : CNFRefutation 6.73s
% Verified   : 
% Statistics : Number of formulae       :  191 ( 754 expanded)
%              Number of leaves         :   38 ( 257 expanded)
%              Depth                    :   11
%              Number of atoms          :  273 (1754 expanded)
%              Number of equality atoms :   60 ( 633 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_xboole_0 > r2_hidden > r1_xboole_0 > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_xboole_0 > #skF_7 > #skF_6 > #skF_2 > #skF_9 > #skF_8 > #skF_3 > #skF_1 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(r2_xboole_0,type,(
    r2_xboole_0: ( $i * $i ) > $o )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_151,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( k2_zfmisc_1(A,B) = k2_zfmisc_1(C,D)
       => ( A = k1_xboole_0
          | B = k1_xboole_0
          | ( A = C
            & B = D ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t134_zfmisc_1)).

tff(f_140,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => ( r1_tarski(k2_zfmisc_1(A,C),k2_zfmisc_1(B,C))
        & r1_tarski(k2_zfmisc_1(C,A),k2_zfmisc_1(C,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t118_zfmisc_1)).

tff(f_134,axiom,(
    ! [A,B,C] :
      ~ ( A != k1_xboole_0
        & ( r1_tarski(k2_zfmisc_1(B,A),k2_zfmisc_1(C,A))
          | r1_tarski(k2_zfmisc_1(A,B),k2_zfmisc_1(A,C)) )
        & ~ r1_tarski(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t117_zfmisc_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_123,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,D))
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).

tff(f_93,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_87,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(c_96,plain,
    ( '#skF_7' != '#skF_9'
    | '#skF_6' != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_124,plain,(
    '#skF_6' != '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_96])).

tff(c_102,plain,(
    k2_zfmisc_1('#skF_6','#skF_7') = k2_zfmisc_1('#skF_8','#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_805,plain,(
    ! [A_161,C_162,B_163] :
      ( r1_tarski(k2_zfmisc_1(A_161,C_162),k2_zfmisc_1(B_163,C_162))
      | ~ r1_tarski(A_161,B_163) ) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_813,plain,(
    ! [A_161] :
      ( r1_tarski(k2_zfmisc_1(A_161,'#skF_7'),k2_zfmisc_1('#skF_8','#skF_9'))
      | ~ r1_tarski(A_161,'#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_102,c_805])).

tff(c_2389,plain,(
    ! [A_224,B_225,C_226] :
      ( ~ r1_tarski(k2_zfmisc_1(A_224,B_225),k2_zfmisc_1(A_224,C_226))
      | r1_tarski(B_225,C_226)
      | k1_xboole_0 = A_224 ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_2415,plain,
    ( r1_tarski('#skF_7','#skF_9')
    | k1_xboole_0 = '#skF_8'
    | ~ r1_tarski('#skF_8','#skF_6') ),
    inference(resolution,[status(thm)],[c_813,c_2389])).

tff(c_2425,plain,(
    ~ r1_tarski('#skF_8','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_2415])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_3571,plain,(
    ! [A_293,B_294,C_295,D_296] :
      ( r2_hidden(k4_tarski(A_293,B_294),k2_zfmisc_1(C_295,D_296))
      | ~ r2_hidden(B_294,D_296)
      | ~ r2_hidden(A_293,C_295) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_532,plain,(
    ! [A_151,C_152,B_153,D_154] :
      ( r2_hidden(A_151,C_152)
      | ~ r2_hidden(k4_tarski(A_151,B_153),k2_zfmisc_1(C_152,D_154)) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_535,plain,(
    ! [A_151,B_153] :
      ( r2_hidden(A_151,'#skF_6')
      | ~ r2_hidden(k4_tarski(A_151,B_153),k2_zfmisc_1('#skF_8','#skF_9')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_102,c_532])).

tff(c_3592,plain,(
    ! [A_293,B_294] :
      ( r2_hidden(A_293,'#skF_6')
      | ~ r2_hidden(B_294,'#skF_9')
      | ~ r2_hidden(A_293,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_3571,c_535])).

tff(c_3725,plain,(
    ! [B_312] : ~ r2_hidden(B_312,'#skF_9') ),
    inference(splitLeft,[status(thm)],[c_3592])).

tff(c_3757,plain,(
    ! [B_315] : r1_tarski('#skF_9',B_315) ),
    inference(resolution,[status(thm)],[c_6,c_3725])).

tff(c_56,plain,(
    ! [A_31] : r1_tarski(k1_xboole_0,A_31) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_243,plain,(
    ! [B_114,A_115] :
      ( B_114 = A_115
      | ~ r1_tarski(B_114,A_115)
      | ~ r1_tarski(A_115,B_114) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_252,plain,(
    ! [A_31] :
      ( k1_xboole_0 = A_31
      | ~ r1_tarski(A_31,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_56,c_243])).

tff(c_3764,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(resolution,[status(thm)],[c_3757,c_252])).

tff(c_100,plain,(
    k1_xboole_0 != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_3789,plain,(
    '#skF_6' != '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3764,c_100])).

tff(c_3700,plain,(
    ! [B_294] : ~ r2_hidden(B_294,'#skF_9') ),
    inference(splitLeft,[status(thm)],[c_3592])).

tff(c_3806,plain,(
    ! [A_320,B_321] :
      ( r2_hidden(k4_tarski(A_320,B_321),k2_zfmisc_1('#skF_8','#skF_9'))
      | ~ r2_hidden(B_321,'#skF_7')
      | ~ r2_hidden(A_320,'#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_102,c_3571])).

tff(c_84,plain,(
    ! [B_71,D_73,A_70,C_72] :
      ( r2_hidden(B_71,D_73)
      | ~ r2_hidden(k4_tarski(A_70,B_71),k2_zfmisc_1(C_72,D_73)) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_3815,plain,(
    ! [B_321,A_320] :
      ( r2_hidden(B_321,'#skF_9')
      | ~ r2_hidden(B_321,'#skF_7')
      | ~ r2_hidden(A_320,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_3806,c_84])).

tff(c_3825,plain,(
    ! [B_321,A_320] :
      ( ~ r2_hidden(B_321,'#skF_7')
      | ~ r2_hidden(A_320,'#skF_6') ) ),
    inference(negUnitSimplification,[status(thm)],[c_3700,c_3815])).

tff(c_4745,plain,(
    ! [A_360] : ~ r2_hidden(A_360,'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_3825])).

tff(c_4817,plain,(
    ! [B_367] : r1_tarski('#skF_6',B_367) ),
    inference(resolution,[status(thm)],[c_6,c_4745])).

tff(c_3781,plain,(
    ! [A_31] :
      ( A_31 = '#skF_9'
      | ~ r1_tarski(A_31,'#skF_9') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3764,c_3764,c_252])).

tff(c_4821,plain,(
    '#skF_6' = '#skF_9' ),
    inference(resolution,[status(thm)],[c_4817,c_3781])).

tff(c_4827,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3789,c_4821])).

tff(c_4837,plain,(
    ! [B_369] : ~ r2_hidden(B_369,'#skF_7') ),
    inference(splitRight,[status(thm)],[c_3825])).

tff(c_4870,plain,(
    ! [B_2] : r1_tarski('#skF_7',B_2) ),
    inference(resolution,[status(thm)],[c_6,c_4837])).

tff(c_810,plain,(
    ! [B_163] :
      ( r1_tarski(k2_zfmisc_1('#skF_8','#skF_9'),k2_zfmisc_1(B_163,'#skF_7'))
      | ~ r1_tarski('#skF_6',B_163) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_102,c_805])).

tff(c_2417,plain,
    ( r1_tarski('#skF_9','#skF_7')
    | k1_xboole_0 = '#skF_8'
    | ~ r1_tarski('#skF_6','#skF_8') ),
    inference(resolution,[status(thm)],[c_810,c_2389])).

tff(c_2426,plain,(
    ~ r1_tarski('#skF_6','#skF_8') ),
    inference(splitLeft,[status(thm)],[c_2417])).

tff(c_1506,plain,(
    ! [C_186,A_187,B_188] :
      ( r1_tarski(k2_zfmisc_1(C_186,A_187),k2_zfmisc_1(C_186,B_188))
      | ~ r1_tarski(A_187,B_188) ) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_1514,plain,(
    ! [A_187] :
      ( r1_tarski(k2_zfmisc_1('#skF_6',A_187),k2_zfmisc_1('#skF_8','#skF_9'))
      | ~ r1_tarski(A_187,'#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_102,c_1506])).

tff(c_2522,plain,(
    ! [B_230,A_231,C_232] :
      ( ~ r1_tarski(k2_zfmisc_1(B_230,A_231),k2_zfmisc_1(C_232,A_231))
      | r1_tarski(B_230,C_232)
      | k1_xboole_0 = A_231 ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_2530,plain,
    ( r1_tarski('#skF_6','#skF_8')
    | k1_xboole_0 = '#skF_9'
    | ~ r1_tarski('#skF_9','#skF_7') ),
    inference(resolution,[status(thm)],[c_1514,c_2522])).

tff(c_2553,plain,
    ( k1_xboole_0 = '#skF_9'
    | ~ r1_tarski('#skF_9','#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_2426,c_2530])).

tff(c_2563,plain,(
    ~ r1_tarski('#skF_9','#skF_7') ),
    inference(splitLeft,[status(thm)],[c_2553])).

tff(c_2591,plain,(
    ! [A_234,B_235,C_236,D_237] :
      ( r2_hidden(k4_tarski(A_234,B_235),k2_zfmisc_1(C_236,D_237))
      | ~ r2_hidden(B_235,D_237)
      | ~ r2_hidden(A_234,C_236) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_1221,plain,(
    ! [B_175,D_176,A_177,C_178] :
      ( r2_hidden(B_175,D_176)
      | ~ r2_hidden(k4_tarski(A_177,B_175),k2_zfmisc_1(C_178,D_176)) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_1224,plain,(
    ! [B_175,A_177] :
      ( r2_hidden(B_175,'#skF_7')
      | ~ r2_hidden(k4_tarski(A_177,B_175),k2_zfmisc_1('#skF_8','#skF_9')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_102,c_1221])).

tff(c_2611,plain,(
    ! [B_235,A_234] :
      ( r2_hidden(B_235,'#skF_7')
      | ~ r2_hidden(B_235,'#skF_9')
      | ~ r2_hidden(A_234,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_2591,c_1224])).

tff(c_2657,plain,(
    ! [A_244] : ~ r2_hidden(A_244,'#skF_8') ),
    inference(splitLeft,[status(thm)],[c_2611])).

tff(c_2676,plain,(
    ! [B_2] : r1_tarski('#skF_8',B_2) ),
    inference(resolution,[status(thm)],[c_6,c_2657])).

tff(c_2717,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2676,c_2425])).

tff(c_2719,plain,(
    ! [B_249] :
      ( r2_hidden(B_249,'#skF_7')
      | ~ r2_hidden(B_249,'#skF_9') ) ),
    inference(splitRight,[status(thm)],[c_2611])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_2733,plain,(
    ! [A_250] :
      ( r1_tarski(A_250,'#skF_7')
      | ~ r2_hidden('#skF_1'(A_250,'#skF_7'),'#skF_9') ) ),
    inference(resolution,[status(thm)],[c_2719,c_4])).

tff(c_2737,plain,(
    r1_tarski('#skF_9','#skF_7') ),
    inference(resolution,[status(thm)],[c_6,c_2733])).

tff(c_2741,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2563,c_2563,c_2737])).

tff(c_2742,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_2553])).

tff(c_2789,plain,(
    ! [A_31] : r1_tarski('#skF_9',A_31) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2742,c_56])).

tff(c_92,plain,(
    ! [C_79,A_77,B_78] :
      ( r1_tarski(k2_zfmisc_1(C_79,A_77),k2_zfmisc_1(C_79,B_78))
      | ~ r1_tarski(A_77,B_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_98,plain,(
    k1_xboole_0 != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_2540,plain,(
    ! [C_232] :
      ( ~ r1_tarski(k2_zfmisc_1('#skF_8','#skF_9'),k2_zfmisc_1(C_232,'#skF_7'))
      | r1_tarski('#skF_6',C_232)
      | k1_xboole_0 = '#skF_7' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_102,c_2522])).

tff(c_3334,plain,(
    ! [C_279] :
      ( ~ r1_tarski(k2_zfmisc_1('#skF_8','#skF_9'),k2_zfmisc_1(C_279,'#skF_7'))
      | r1_tarski('#skF_6',C_279) ) ),
    inference(negUnitSimplification,[status(thm)],[c_98,c_2540])).

tff(c_3342,plain,
    ( r1_tarski('#skF_6','#skF_8')
    | ~ r1_tarski('#skF_9','#skF_7') ),
    inference(resolution,[status(thm)],[c_92,c_3334])).

tff(c_3354,plain,(
    r1_tarski('#skF_6','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2789,c_3342])).

tff(c_3356,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2426,c_3354])).

tff(c_3357,plain,
    ( k1_xboole_0 = '#skF_8'
    | r1_tarski('#skF_9','#skF_7') ),
    inference(splitRight,[status(thm)],[c_2417])).

tff(c_3363,plain,(
    r1_tarski('#skF_9','#skF_7') ),
    inference(splitLeft,[status(thm)],[c_3357])).

tff(c_46,plain,(
    ! [B_27,A_26] :
      ( B_27 = A_26
      | ~ r1_tarski(B_27,A_26)
      | ~ r1_tarski(A_26,B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_3366,plain,
    ( '#skF_7' = '#skF_9'
    | ~ r1_tarski('#skF_7','#skF_9') ),
    inference(resolution,[status(thm)],[c_3363,c_46])).

tff(c_3367,plain,(
    ~ r1_tarski('#skF_7','#skF_9') ),
    inference(splitLeft,[status(thm)],[c_3366])).

tff(c_4891,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4870,c_3367])).

tff(c_4893,plain,(
    ! [A_372] :
      ( r2_hidden(A_372,'#skF_6')
      | ~ r2_hidden(A_372,'#skF_8') ) ),
    inference(splitRight,[status(thm)],[c_3592])).

tff(c_4920,plain,(
    ! [A_376] :
      ( r1_tarski(A_376,'#skF_6')
      | ~ r2_hidden('#skF_1'(A_376,'#skF_6'),'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_4893,c_4])).

tff(c_4924,plain,(
    r1_tarski('#skF_8','#skF_6') ),
    inference(resolution,[status(thm)],[c_6,c_4920])).

tff(c_4928,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2425,c_2425,c_4924])).

tff(c_4929,plain,(
    '#skF_7' = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_3366])).

tff(c_4938,plain,(
    k1_xboole_0 != '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4929,c_98])).

tff(c_5096,plain,(
    ! [A_383,B_384,C_385,D_386] :
      ( r2_hidden(k4_tarski(A_383,B_384),k2_zfmisc_1(C_385,D_386))
      | ~ r2_hidden(B_384,D_386)
      | ~ r2_hidden(A_383,C_385) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_5112,plain,(
    ! [A_383,B_384] :
      ( r2_hidden(A_383,'#skF_6')
      | ~ r2_hidden(B_384,'#skF_9')
      | ~ r2_hidden(A_383,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_5096,c_535])).

tff(c_5134,plain,(
    ! [B_388] : ~ r2_hidden(B_388,'#skF_9') ),
    inference(splitLeft,[status(thm)],[c_5112])).

tff(c_5166,plain,(
    ! [B_391] : r1_tarski('#skF_9',B_391) ),
    inference(resolution,[status(thm)],[c_6,c_5134])).

tff(c_5170,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(resolution,[status(thm)],[c_5166,c_252])).

tff(c_5176,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4938,c_5170])).

tff(c_5187,plain,(
    ! [A_397] :
      ( r2_hidden(A_397,'#skF_6')
      | ~ r2_hidden(A_397,'#skF_8') ) ),
    inference(splitRight,[status(thm)],[c_5112])).

tff(c_5201,plain,(
    ! [A_398] :
      ( r1_tarski(A_398,'#skF_6')
      | ~ r2_hidden('#skF_1'(A_398,'#skF_6'),'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_5187,c_4])).

tff(c_5205,plain,(
    r1_tarski('#skF_8','#skF_6') ),
    inference(resolution,[status(thm)],[c_6,c_5201])).

tff(c_5209,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2425,c_2425,c_5205])).

tff(c_5210,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_3357])).

tff(c_5231,plain,(
    ! [A_31] : r1_tarski('#skF_8',A_31) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5210,c_56])).

tff(c_5245,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5231,c_2425])).

tff(c_5247,plain,(
    r1_tarski('#skF_8','#skF_6') ),
    inference(splitRight,[status(thm)],[c_2415])).

tff(c_5249,plain,
    ( '#skF_6' = '#skF_8'
    | ~ r1_tarski('#skF_6','#skF_8') ),
    inference(resolution,[status(thm)],[c_5247,c_46])).

tff(c_5252,plain,(
    ~ r1_tarski('#skF_6','#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_124,c_5249])).

tff(c_5254,plain,(
    ! [B_400,A_401,C_402] :
      ( ~ r1_tarski(k2_zfmisc_1(B_400,A_401),k2_zfmisc_1(C_402,A_401))
      | r1_tarski(B_400,C_402)
      | k1_xboole_0 = A_401 ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_5262,plain,
    ( r1_tarski('#skF_6','#skF_8')
    | k1_xboole_0 = '#skF_9'
    | ~ r1_tarski('#skF_9','#skF_7') ),
    inference(resolution,[status(thm)],[c_1514,c_5254])).

tff(c_5284,plain,
    ( k1_xboole_0 = '#skF_9'
    | ~ r1_tarski('#skF_9','#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_5252,c_5262])).

tff(c_5296,plain,(
    ~ r1_tarski('#skF_9','#skF_7') ),
    inference(splitLeft,[status(thm)],[c_5284])).

tff(c_5324,plain,(
    ! [A_404,B_405,C_406,D_407] :
      ( r2_hidden(k4_tarski(A_404,B_405),k2_zfmisc_1(C_406,D_407))
      | ~ r2_hidden(B_405,D_407)
      | ~ r2_hidden(A_404,C_406) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_5344,plain,(
    ! [B_405,A_404] :
      ( r2_hidden(B_405,'#skF_7')
      | ~ r2_hidden(B_405,'#skF_9')
      | ~ r2_hidden(A_404,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_5324,c_1224])).

tff(c_5488,plain,(
    ! [A_417] : ~ r2_hidden(A_417,'#skF_8') ),
    inference(splitLeft,[status(thm)],[c_5344])).

tff(c_5529,plain,(
    ! [B_426] : r1_tarski('#skF_8',B_426) ),
    inference(resolution,[status(thm)],[c_6,c_5488])).

tff(c_5536,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(resolution,[status(thm)],[c_5529,c_252])).

tff(c_5560,plain,(
    '#skF_7' != '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5536,c_98])).

tff(c_5487,plain,(
    ! [A_404] : ~ r2_hidden(A_404,'#skF_8') ),
    inference(splitLeft,[status(thm)],[c_5344])).

tff(c_5921,plain,(
    ! [A_438,B_439] :
      ( r2_hidden(k4_tarski(A_438,B_439),k2_zfmisc_1('#skF_8','#skF_9'))
      | ~ r2_hidden(B_439,'#skF_7')
      | ~ r2_hidden(A_438,'#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_102,c_5324])).

tff(c_86,plain,(
    ! [A_70,C_72,B_71,D_73] :
      ( r2_hidden(A_70,C_72)
      | ~ r2_hidden(k4_tarski(A_70,B_71),k2_zfmisc_1(C_72,D_73)) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_5933,plain,(
    ! [A_438,B_439] :
      ( r2_hidden(A_438,'#skF_8')
      | ~ r2_hidden(B_439,'#skF_7')
      | ~ r2_hidden(A_438,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_5921,c_86])).

tff(c_5941,plain,(
    ! [B_439,A_438] :
      ( ~ r2_hidden(B_439,'#skF_7')
      | ~ r2_hidden(A_438,'#skF_6') ) ),
    inference(negUnitSimplification,[status(thm)],[c_5487,c_5933])).

tff(c_6569,plain,(
    ! [A_475] : ~ r2_hidden(A_475,'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_5941])).

tff(c_6602,plain,(
    ! [B_2] : r1_tarski('#skF_6',B_2) ),
    inference(resolution,[status(thm)],[c_6,c_6569])).

tff(c_6621,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6602,c_5252])).

tff(c_6624,plain,(
    ! [B_478] : ~ r2_hidden(B_478,'#skF_7') ),
    inference(splitRight,[status(thm)],[c_5941])).

tff(c_6681,plain,(
    ! [B_483] : r1_tarski('#skF_7',B_483) ),
    inference(resolution,[status(thm)],[c_6,c_6624])).

tff(c_5553,plain,(
    ! [A_31] :
      ( A_31 = '#skF_8'
      | ~ r1_tarski(A_31,'#skF_8') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5536,c_5536,c_252])).

tff(c_6685,plain,(
    '#skF_7' = '#skF_8' ),
    inference(resolution,[status(thm)],[c_6681,c_5553])).

tff(c_6691,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_5560,c_6685])).

tff(c_6717,plain,(
    ! [B_485] :
      ( r2_hidden(B_485,'#skF_7')
      | ~ r2_hidden(B_485,'#skF_9') ) ),
    inference(splitRight,[status(thm)],[c_5344])).

tff(c_6731,plain,(
    ! [A_486] :
      ( r1_tarski(A_486,'#skF_7')
      | ~ r2_hidden('#skF_1'(A_486,'#skF_7'),'#skF_9') ) ),
    inference(resolution,[status(thm)],[c_6717,c_4])).

tff(c_6735,plain,(
    r1_tarski('#skF_9','#skF_7') ),
    inference(resolution,[status(thm)],[c_6,c_6731])).

tff(c_6739,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_5296,c_5296,c_6735])).

tff(c_6740,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_5284])).

tff(c_6764,plain,(
    '#skF_7' != '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6740,c_98])).

tff(c_5246,plain,
    ( k1_xboole_0 = '#skF_8'
    | r1_tarski('#skF_7','#skF_9') ),
    inference(splitRight,[status(thm)],[c_2415])).

tff(c_5253,plain,(
    r1_tarski('#skF_7','#skF_9') ),
    inference(splitLeft,[status(thm)],[c_5246])).

tff(c_6741,plain,(
    r1_tarski('#skF_9','#skF_7') ),
    inference(splitRight,[status(thm)],[c_5284])).

tff(c_6796,plain,
    ( '#skF_7' = '#skF_9'
    | ~ r1_tarski('#skF_7','#skF_9') ),
    inference(resolution,[status(thm)],[c_6741,c_46])).

tff(c_6799,plain,(
    '#skF_7' = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5253,c_6796])).

tff(c_6801,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_6764,c_6799])).

tff(c_6803,plain,(
    ~ r1_tarski('#skF_7','#skF_9') ),
    inference(splitRight,[status(thm)],[c_5246])).

tff(c_6802,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_5246])).

tff(c_6823,plain,(
    ! [A_31] : r1_tarski('#skF_8',A_31) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6802,c_56])).

tff(c_94,plain,(
    ! [A_77,C_79,B_78] :
      ( r1_tarski(k2_zfmisc_1(A_77,C_79),k2_zfmisc_1(B_78,C_79))
      | ~ r1_tarski(A_77,B_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_2407,plain,(
    ! [C_226] :
      ( ~ r1_tarski(k2_zfmisc_1('#skF_8','#skF_9'),k2_zfmisc_1('#skF_6',C_226))
      | r1_tarski('#skF_7',C_226)
      | k1_xboole_0 = '#skF_6' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_102,c_2389])).

tff(c_7068,plain,(
    ! [C_502] :
      ( ~ r1_tarski(k2_zfmisc_1('#skF_8','#skF_9'),k2_zfmisc_1('#skF_6',C_502))
      | r1_tarski('#skF_7',C_502) ) ),
    inference(negUnitSimplification,[status(thm)],[c_100,c_2407])).

tff(c_7079,plain,
    ( r1_tarski('#skF_7','#skF_9')
    | ~ r1_tarski('#skF_8','#skF_6') ),
    inference(resolution,[status(thm)],[c_94,c_7068])).

tff(c_7089,plain,(
    r1_tarski('#skF_7','#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6823,c_7079])).

tff(c_7091,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_6803,c_7089])).

tff(c_7092,plain,(
    '#skF_7' != '#skF_9' ),
    inference(splitRight,[status(thm)],[c_96])).

tff(c_7093,plain,(
    '#skF_6' = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_96])).

tff(c_7094,plain,(
    k1_xboole_0 != '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7093,c_100])).

tff(c_50,plain,(
    ! [B_27] : r1_tarski(B_27,B_27) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_7127,plain,(
    k2_zfmisc_1('#skF_8','#skF_7') = k2_zfmisc_1('#skF_8','#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7093,c_102])).

tff(c_8050,plain,(
    ! [A_586,C_587,B_588] :
      ( r1_tarski(k2_zfmisc_1(A_586,C_587),k2_zfmisc_1(B_588,C_587))
      | ~ r1_tarski(A_586,B_588) ) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_8055,plain,(
    ! [B_588] :
      ( r1_tarski(k2_zfmisc_1('#skF_8','#skF_9'),k2_zfmisc_1(B_588,'#skF_7'))
      | ~ r1_tarski('#skF_8',B_588) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7127,c_8050])).

tff(c_9574,plain,(
    ! [A_649,B_650,C_651] :
      ( ~ r1_tarski(k2_zfmisc_1(A_649,B_650),k2_zfmisc_1(A_649,C_651))
      | r1_tarski(B_650,C_651)
      | k1_xboole_0 = A_649 ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_9578,plain,
    ( r1_tarski('#skF_9','#skF_7')
    | k1_xboole_0 = '#skF_8'
    | ~ r1_tarski('#skF_8','#skF_8') ),
    inference(resolution,[status(thm)],[c_8055,c_9574])).

tff(c_9608,plain,
    ( r1_tarski('#skF_9','#skF_7')
    | k1_xboole_0 = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_9578])).

tff(c_9609,plain,(
    r1_tarski('#skF_9','#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_7094,c_9608])).

tff(c_8058,plain,(
    ! [A_586] :
      ( r1_tarski(k2_zfmisc_1(A_586,'#skF_7'),k2_zfmisc_1('#skF_8','#skF_9'))
      | ~ r1_tarski(A_586,'#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7127,c_8050])).

tff(c_9585,plain,
    ( r1_tarski('#skF_7','#skF_9')
    | k1_xboole_0 = '#skF_8'
    | ~ r1_tarski('#skF_8','#skF_8') ),
    inference(resolution,[status(thm)],[c_8058,c_9574])).

tff(c_9615,plain,
    ( r1_tarski('#skF_7','#skF_9')
    | k1_xboole_0 = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_9585])).

tff(c_9616,plain,(
    r1_tarski('#skF_7','#skF_9') ),
    inference(negUnitSimplification,[status(thm)],[c_7094,c_9615])).

tff(c_9636,plain,
    ( '#skF_7' = '#skF_9'
    | ~ r1_tarski('#skF_9','#skF_7') ),
    inference(resolution,[status(thm)],[c_9616,c_46])).

tff(c_9643,plain,(
    '#skF_7' = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9609,c_9636])).

tff(c_9645,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_7092,c_9643])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n012.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 11:11:22 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.73/2.41  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.73/2.43  
% 6.73/2.43  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.73/2.43  %$ r2_xboole_0 > r2_hidden > r1_xboole_0 > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_xboole_0 > #skF_7 > #skF_6 > #skF_2 > #skF_9 > #skF_8 > #skF_3 > #skF_1 > #skF_5 > #skF_4
% 6.73/2.43  
% 6.73/2.43  %Foreground sorts:
% 6.73/2.43  
% 6.73/2.43  
% 6.73/2.43  %Background operators:
% 6.73/2.43  
% 6.73/2.43  
% 6.73/2.43  %Foreground operators:
% 6.73/2.43  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.73/2.43  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.73/2.43  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 6.73/2.43  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 6.73/2.43  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.73/2.43  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 6.73/2.43  tff('#skF_7', type, '#skF_7': $i).
% 6.73/2.43  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 6.73/2.43  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.73/2.43  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 6.73/2.43  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 6.73/2.43  tff('#skF_6', type, '#skF_6': $i).
% 6.73/2.43  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 6.73/2.43  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 6.73/2.43  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 6.73/2.43  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 6.73/2.43  tff('#skF_9', type, '#skF_9': $i).
% 6.73/2.43  tff(r2_xboole_0, type, r2_xboole_0: ($i * $i) > $o).
% 6.73/2.43  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 6.73/2.43  tff('#skF_8', type, '#skF_8': $i).
% 6.73/2.43  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.73/2.43  tff(k3_tarski, type, k3_tarski: $i > $i).
% 6.73/2.43  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 6.73/2.43  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 6.73/2.43  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.73/2.43  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 6.73/2.43  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 6.73/2.43  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 6.73/2.43  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 6.73/2.43  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 6.73/2.43  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 6.73/2.43  
% 6.73/2.46  tff(f_151, negated_conjecture, ~(![A, B, C, D]: ((k2_zfmisc_1(A, B) = k2_zfmisc_1(C, D)) => (((A = k1_xboole_0) | (B = k1_xboole_0)) | ((A = C) & (B = D))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t134_zfmisc_1)).
% 6.73/2.46  tff(f_140, axiom, (![A, B, C]: (r1_tarski(A, B) => (r1_tarski(k2_zfmisc_1(A, C), k2_zfmisc_1(B, C)) & r1_tarski(k2_zfmisc_1(C, A), k2_zfmisc_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t118_zfmisc_1)).
% 6.73/2.46  tff(f_134, axiom, (![A, B, C]: ~((~(A = k1_xboole_0) & (r1_tarski(k2_zfmisc_1(B, A), k2_zfmisc_1(C, A)) | r1_tarski(k2_zfmisc_1(A, B), k2_zfmisc_1(A, C)))) & ~r1_tarski(B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t117_zfmisc_1)).
% 6.73/2.46  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 6.73/2.46  tff(f_123, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, D)) <=> (r2_hidden(A, C) & r2_hidden(B, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 6.73/2.46  tff(f_93, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 6.73/2.46  tff(f_87, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 6.73/2.46  tff(c_96, plain, ('#skF_7'!='#skF_9' | '#skF_6'!='#skF_8'), inference(cnfTransformation, [status(thm)], [f_151])).
% 6.73/2.46  tff(c_124, plain, ('#skF_6'!='#skF_8'), inference(splitLeft, [status(thm)], [c_96])).
% 6.73/2.46  tff(c_102, plain, (k2_zfmisc_1('#skF_6', '#skF_7')=k2_zfmisc_1('#skF_8', '#skF_9')), inference(cnfTransformation, [status(thm)], [f_151])).
% 6.73/2.46  tff(c_805, plain, (![A_161, C_162, B_163]: (r1_tarski(k2_zfmisc_1(A_161, C_162), k2_zfmisc_1(B_163, C_162)) | ~r1_tarski(A_161, B_163))), inference(cnfTransformation, [status(thm)], [f_140])).
% 6.73/2.46  tff(c_813, plain, (![A_161]: (r1_tarski(k2_zfmisc_1(A_161, '#skF_7'), k2_zfmisc_1('#skF_8', '#skF_9')) | ~r1_tarski(A_161, '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_102, c_805])).
% 6.73/2.46  tff(c_2389, plain, (![A_224, B_225, C_226]: (~r1_tarski(k2_zfmisc_1(A_224, B_225), k2_zfmisc_1(A_224, C_226)) | r1_tarski(B_225, C_226) | k1_xboole_0=A_224)), inference(cnfTransformation, [status(thm)], [f_134])).
% 6.73/2.46  tff(c_2415, plain, (r1_tarski('#skF_7', '#skF_9') | k1_xboole_0='#skF_8' | ~r1_tarski('#skF_8', '#skF_6')), inference(resolution, [status(thm)], [c_813, c_2389])).
% 6.73/2.46  tff(c_2425, plain, (~r1_tarski('#skF_8', '#skF_6')), inference(splitLeft, [status(thm)], [c_2415])).
% 6.73/2.46  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.73/2.46  tff(c_3571, plain, (![A_293, B_294, C_295, D_296]: (r2_hidden(k4_tarski(A_293, B_294), k2_zfmisc_1(C_295, D_296)) | ~r2_hidden(B_294, D_296) | ~r2_hidden(A_293, C_295))), inference(cnfTransformation, [status(thm)], [f_123])).
% 6.73/2.46  tff(c_532, plain, (![A_151, C_152, B_153, D_154]: (r2_hidden(A_151, C_152) | ~r2_hidden(k4_tarski(A_151, B_153), k2_zfmisc_1(C_152, D_154)))), inference(cnfTransformation, [status(thm)], [f_123])).
% 6.73/2.46  tff(c_535, plain, (![A_151, B_153]: (r2_hidden(A_151, '#skF_6') | ~r2_hidden(k4_tarski(A_151, B_153), k2_zfmisc_1('#skF_8', '#skF_9')))), inference(superposition, [status(thm), theory('equality')], [c_102, c_532])).
% 6.73/2.46  tff(c_3592, plain, (![A_293, B_294]: (r2_hidden(A_293, '#skF_6') | ~r2_hidden(B_294, '#skF_9') | ~r2_hidden(A_293, '#skF_8'))), inference(resolution, [status(thm)], [c_3571, c_535])).
% 6.73/2.46  tff(c_3725, plain, (![B_312]: (~r2_hidden(B_312, '#skF_9'))), inference(splitLeft, [status(thm)], [c_3592])).
% 6.73/2.46  tff(c_3757, plain, (![B_315]: (r1_tarski('#skF_9', B_315))), inference(resolution, [status(thm)], [c_6, c_3725])).
% 6.73/2.46  tff(c_56, plain, (![A_31]: (r1_tarski(k1_xboole_0, A_31))), inference(cnfTransformation, [status(thm)], [f_93])).
% 6.73/2.46  tff(c_243, plain, (![B_114, A_115]: (B_114=A_115 | ~r1_tarski(B_114, A_115) | ~r1_tarski(A_115, B_114))), inference(cnfTransformation, [status(thm)], [f_87])).
% 6.73/2.46  tff(c_252, plain, (![A_31]: (k1_xboole_0=A_31 | ~r1_tarski(A_31, k1_xboole_0))), inference(resolution, [status(thm)], [c_56, c_243])).
% 6.73/2.46  tff(c_3764, plain, (k1_xboole_0='#skF_9'), inference(resolution, [status(thm)], [c_3757, c_252])).
% 6.73/2.46  tff(c_100, plain, (k1_xboole_0!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_151])).
% 6.73/2.46  tff(c_3789, plain, ('#skF_6'!='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_3764, c_100])).
% 6.73/2.46  tff(c_3700, plain, (![B_294]: (~r2_hidden(B_294, '#skF_9'))), inference(splitLeft, [status(thm)], [c_3592])).
% 6.73/2.46  tff(c_3806, plain, (![A_320, B_321]: (r2_hidden(k4_tarski(A_320, B_321), k2_zfmisc_1('#skF_8', '#skF_9')) | ~r2_hidden(B_321, '#skF_7') | ~r2_hidden(A_320, '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_102, c_3571])).
% 6.73/2.46  tff(c_84, plain, (![B_71, D_73, A_70, C_72]: (r2_hidden(B_71, D_73) | ~r2_hidden(k4_tarski(A_70, B_71), k2_zfmisc_1(C_72, D_73)))), inference(cnfTransformation, [status(thm)], [f_123])).
% 6.73/2.46  tff(c_3815, plain, (![B_321, A_320]: (r2_hidden(B_321, '#skF_9') | ~r2_hidden(B_321, '#skF_7') | ~r2_hidden(A_320, '#skF_6'))), inference(resolution, [status(thm)], [c_3806, c_84])).
% 6.73/2.46  tff(c_3825, plain, (![B_321, A_320]: (~r2_hidden(B_321, '#skF_7') | ~r2_hidden(A_320, '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_3700, c_3815])).
% 6.73/2.46  tff(c_4745, plain, (![A_360]: (~r2_hidden(A_360, '#skF_6'))), inference(splitLeft, [status(thm)], [c_3825])).
% 6.73/2.46  tff(c_4817, plain, (![B_367]: (r1_tarski('#skF_6', B_367))), inference(resolution, [status(thm)], [c_6, c_4745])).
% 6.73/2.46  tff(c_3781, plain, (![A_31]: (A_31='#skF_9' | ~r1_tarski(A_31, '#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_3764, c_3764, c_252])).
% 6.73/2.46  tff(c_4821, plain, ('#skF_6'='#skF_9'), inference(resolution, [status(thm)], [c_4817, c_3781])).
% 6.73/2.46  tff(c_4827, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3789, c_4821])).
% 6.73/2.46  tff(c_4837, plain, (![B_369]: (~r2_hidden(B_369, '#skF_7'))), inference(splitRight, [status(thm)], [c_3825])).
% 6.73/2.46  tff(c_4870, plain, (![B_2]: (r1_tarski('#skF_7', B_2))), inference(resolution, [status(thm)], [c_6, c_4837])).
% 6.73/2.46  tff(c_810, plain, (![B_163]: (r1_tarski(k2_zfmisc_1('#skF_8', '#skF_9'), k2_zfmisc_1(B_163, '#skF_7')) | ~r1_tarski('#skF_6', B_163))), inference(superposition, [status(thm), theory('equality')], [c_102, c_805])).
% 6.73/2.46  tff(c_2417, plain, (r1_tarski('#skF_9', '#skF_7') | k1_xboole_0='#skF_8' | ~r1_tarski('#skF_6', '#skF_8')), inference(resolution, [status(thm)], [c_810, c_2389])).
% 6.73/2.46  tff(c_2426, plain, (~r1_tarski('#skF_6', '#skF_8')), inference(splitLeft, [status(thm)], [c_2417])).
% 6.73/2.46  tff(c_1506, plain, (![C_186, A_187, B_188]: (r1_tarski(k2_zfmisc_1(C_186, A_187), k2_zfmisc_1(C_186, B_188)) | ~r1_tarski(A_187, B_188))), inference(cnfTransformation, [status(thm)], [f_140])).
% 6.73/2.46  tff(c_1514, plain, (![A_187]: (r1_tarski(k2_zfmisc_1('#skF_6', A_187), k2_zfmisc_1('#skF_8', '#skF_9')) | ~r1_tarski(A_187, '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_102, c_1506])).
% 6.73/2.46  tff(c_2522, plain, (![B_230, A_231, C_232]: (~r1_tarski(k2_zfmisc_1(B_230, A_231), k2_zfmisc_1(C_232, A_231)) | r1_tarski(B_230, C_232) | k1_xboole_0=A_231)), inference(cnfTransformation, [status(thm)], [f_134])).
% 6.73/2.46  tff(c_2530, plain, (r1_tarski('#skF_6', '#skF_8') | k1_xboole_0='#skF_9' | ~r1_tarski('#skF_9', '#skF_7')), inference(resolution, [status(thm)], [c_1514, c_2522])).
% 6.73/2.46  tff(c_2553, plain, (k1_xboole_0='#skF_9' | ~r1_tarski('#skF_9', '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_2426, c_2530])).
% 6.73/2.46  tff(c_2563, plain, (~r1_tarski('#skF_9', '#skF_7')), inference(splitLeft, [status(thm)], [c_2553])).
% 6.73/2.46  tff(c_2591, plain, (![A_234, B_235, C_236, D_237]: (r2_hidden(k4_tarski(A_234, B_235), k2_zfmisc_1(C_236, D_237)) | ~r2_hidden(B_235, D_237) | ~r2_hidden(A_234, C_236))), inference(cnfTransformation, [status(thm)], [f_123])).
% 6.73/2.46  tff(c_1221, plain, (![B_175, D_176, A_177, C_178]: (r2_hidden(B_175, D_176) | ~r2_hidden(k4_tarski(A_177, B_175), k2_zfmisc_1(C_178, D_176)))), inference(cnfTransformation, [status(thm)], [f_123])).
% 6.73/2.46  tff(c_1224, plain, (![B_175, A_177]: (r2_hidden(B_175, '#skF_7') | ~r2_hidden(k4_tarski(A_177, B_175), k2_zfmisc_1('#skF_8', '#skF_9')))), inference(superposition, [status(thm), theory('equality')], [c_102, c_1221])).
% 6.73/2.46  tff(c_2611, plain, (![B_235, A_234]: (r2_hidden(B_235, '#skF_7') | ~r2_hidden(B_235, '#skF_9') | ~r2_hidden(A_234, '#skF_8'))), inference(resolution, [status(thm)], [c_2591, c_1224])).
% 6.73/2.46  tff(c_2657, plain, (![A_244]: (~r2_hidden(A_244, '#skF_8'))), inference(splitLeft, [status(thm)], [c_2611])).
% 6.73/2.46  tff(c_2676, plain, (![B_2]: (r1_tarski('#skF_8', B_2))), inference(resolution, [status(thm)], [c_6, c_2657])).
% 6.73/2.46  tff(c_2717, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2676, c_2425])).
% 6.73/2.46  tff(c_2719, plain, (![B_249]: (r2_hidden(B_249, '#skF_7') | ~r2_hidden(B_249, '#skF_9'))), inference(splitRight, [status(thm)], [c_2611])).
% 6.73/2.46  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.73/2.46  tff(c_2733, plain, (![A_250]: (r1_tarski(A_250, '#skF_7') | ~r2_hidden('#skF_1'(A_250, '#skF_7'), '#skF_9'))), inference(resolution, [status(thm)], [c_2719, c_4])).
% 6.73/2.46  tff(c_2737, plain, (r1_tarski('#skF_9', '#skF_7')), inference(resolution, [status(thm)], [c_6, c_2733])).
% 6.73/2.46  tff(c_2741, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2563, c_2563, c_2737])).
% 6.73/2.46  tff(c_2742, plain, (k1_xboole_0='#skF_9'), inference(splitRight, [status(thm)], [c_2553])).
% 6.73/2.46  tff(c_2789, plain, (![A_31]: (r1_tarski('#skF_9', A_31))), inference(demodulation, [status(thm), theory('equality')], [c_2742, c_56])).
% 6.73/2.46  tff(c_92, plain, (![C_79, A_77, B_78]: (r1_tarski(k2_zfmisc_1(C_79, A_77), k2_zfmisc_1(C_79, B_78)) | ~r1_tarski(A_77, B_78))), inference(cnfTransformation, [status(thm)], [f_140])).
% 6.73/2.46  tff(c_98, plain, (k1_xboole_0!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_151])).
% 6.73/2.46  tff(c_2540, plain, (![C_232]: (~r1_tarski(k2_zfmisc_1('#skF_8', '#skF_9'), k2_zfmisc_1(C_232, '#skF_7')) | r1_tarski('#skF_6', C_232) | k1_xboole_0='#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_102, c_2522])).
% 6.73/2.46  tff(c_3334, plain, (![C_279]: (~r1_tarski(k2_zfmisc_1('#skF_8', '#skF_9'), k2_zfmisc_1(C_279, '#skF_7')) | r1_tarski('#skF_6', C_279))), inference(negUnitSimplification, [status(thm)], [c_98, c_2540])).
% 6.73/2.46  tff(c_3342, plain, (r1_tarski('#skF_6', '#skF_8') | ~r1_tarski('#skF_9', '#skF_7')), inference(resolution, [status(thm)], [c_92, c_3334])).
% 6.73/2.46  tff(c_3354, plain, (r1_tarski('#skF_6', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_2789, c_3342])).
% 6.73/2.46  tff(c_3356, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2426, c_3354])).
% 6.73/2.46  tff(c_3357, plain, (k1_xboole_0='#skF_8' | r1_tarski('#skF_9', '#skF_7')), inference(splitRight, [status(thm)], [c_2417])).
% 6.73/2.46  tff(c_3363, plain, (r1_tarski('#skF_9', '#skF_7')), inference(splitLeft, [status(thm)], [c_3357])).
% 6.73/2.46  tff(c_46, plain, (![B_27, A_26]: (B_27=A_26 | ~r1_tarski(B_27, A_26) | ~r1_tarski(A_26, B_27))), inference(cnfTransformation, [status(thm)], [f_87])).
% 6.73/2.46  tff(c_3366, plain, ('#skF_7'='#skF_9' | ~r1_tarski('#skF_7', '#skF_9')), inference(resolution, [status(thm)], [c_3363, c_46])).
% 6.73/2.46  tff(c_3367, plain, (~r1_tarski('#skF_7', '#skF_9')), inference(splitLeft, [status(thm)], [c_3366])).
% 6.73/2.46  tff(c_4891, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4870, c_3367])).
% 6.73/2.46  tff(c_4893, plain, (![A_372]: (r2_hidden(A_372, '#skF_6') | ~r2_hidden(A_372, '#skF_8'))), inference(splitRight, [status(thm)], [c_3592])).
% 6.73/2.46  tff(c_4920, plain, (![A_376]: (r1_tarski(A_376, '#skF_6') | ~r2_hidden('#skF_1'(A_376, '#skF_6'), '#skF_8'))), inference(resolution, [status(thm)], [c_4893, c_4])).
% 6.73/2.46  tff(c_4924, plain, (r1_tarski('#skF_8', '#skF_6')), inference(resolution, [status(thm)], [c_6, c_4920])).
% 6.73/2.46  tff(c_4928, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2425, c_2425, c_4924])).
% 6.73/2.46  tff(c_4929, plain, ('#skF_7'='#skF_9'), inference(splitRight, [status(thm)], [c_3366])).
% 6.73/2.46  tff(c_4938, plain, (k1_xboole_0!='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_4929, c_98])).
% 6.73/2.46  tff(c_5096, plain, (![A_383, B_384, C_385, D_386]: (r2_hidden(k4_tarski(A_383, B_384), k2_zfmisc_1(C_385, D_386)) | ~r2_hidden(B_384, D_386) | ~r2_hidden(A_383, C_385))), inference(cnfTransformation, [status(thm)], [f_123])).
% 6.73/2.46  tff(c_5112, plain, (![A_383, B_384]: (r2_hidden(A_383, '#skF_6') | ~r2_hidden(B_384, '#skF_9') | ~r2_hidden(A_383, '#skF_8'))), inference(resolution, [status(thm)], [c_5096, c_535])).
% 6.73/2.46  tff(c_5134, plain, (![B_388]: (~r2_hidden(B_388, '#skF_9'))), inference(splitLeft, [status(thm)], [c_5112])).
% 6.73/2.46  tff(c_5166, plain, (![B_391]: (r1_tarski('#skF_9', B_391))), inference(resolution, [status(thm)], [c_6, c_5134])).
% 6.73/2.46  tff(c_5170, plain, (k1_xboole_0='#skF_9'), inference(resolution, [status(thm)], [c_5166, c_252])).
% 6.73/2.46  tff(c_5176, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4938, c_5170])).
% 6.73/2.46  tff(c_5187, plain, (![A_397]: (r2_hidden(A_397, '#skF_6') | ~r2_hidden(A_397, '#skF_8'))), inference(splitRight, [status(thm)], [c_5112])).
% 6.73/2.46  tff(c_5201, plain, (![A_398]: (r1_tarski(A_398, '#skF_6') | ~r2_hidden('#skF_1'(A_398, '#skF_6'), '#skF_8'))), inference(resolution, [status(thm)], [c_5187, c_4])).
% 6.73/2.46  tff(c_5205, plain, (r1_tarski('#skF_8', '#skF_6')), inference(resolution, [status(thm)], [c_6, c_5201])).
% 6.73/2.46  tff(c_5209, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2425, c_2425, c_5205])).
% 6.73/2.46  tff(c_5210, plain, (k1_xboole_0='#skF_8'), inference(splitRight, [status(thm)], [c_3357])).
% 6.73/2.46  tff(c_5231, plain, (![A_31]: (r1_tarski('#skF_8', A_31))), inference(demodulation, [status(thm), theory('equality')], [c_5210, c_56])).
% 6.73/2.46  tff(c_5245, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_5231, c_2425])).
% 6.73/2.46  tff(c_5247, plain, (r1_tarski('#skF_8', '#skF_6')), inference(splitRight, [status(thm)], [c_2415])).
% 6.73/2.46  tff(c_5249, plain, ('#skF_6'='#skF_8' | ~r1_tarski('#skF_6', '#skF_8')), inference(resolution, [status(thm)], [c_5247, c_46])).
% 6.73/2.46  tff(c_5252, plain, (~r1_tarski('#skF_6', '#skF_8')), inference(negUnitSimplification, [status(thm)], [c_124, c_5249])).
% 6.73/2.46  tff(c_5254, plain, (![B_400, A_401, C_402]: (~r1_tarski(k2_zfmisc_1(B_400, A_401), k2_zfmisc_1(C_402, A_401)) | r1_tarski(B_400, C_402) | k1_xboole_0=A_401)), inference(cnfTransformation, [status(thm)], [f_134])).
% 6.73/2.46  tff(c_5262, plain, (r1_tarski('#skF_6', '#skF_8') | k1_xboole_0='#skF_9' | ~r1_tarski('#skF_9', '#skF_7')), inference(resolution, [status(thm)], [c_1514, c_5254])).
% 6.73/2.46  tff(c_5284, plain, (k1_xboole_0='#skF_9' | ~r1_tarski('#skF_9', '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_5252, c_5262])).
% 6.73/2.46  tff(c_5296, plain, (~r1_tarski('#skF_9', '#skF_7')), inference(splitLeft, [status(thm)], [c_5284])).
% 6.73/2.46  tff(c_5324, plain, (![A_404, B_405, C_406, D_407]: (r2_hidden(k4_tarski(A_404, B_405), k2_zfmisc_1(C_406, D_407)) | ~r2_hidden(B_405, D_407) | ~r2_hidden(A_404, C_406))), inference(cnfTransformation, [status(thm)], [f_123])).
% 6.73/2.46  tff(c_5344, plain, (![B_405, A_404]: (r2_hidden(B_405, '#skF_7') | ~r2_hidden(B_405, '#skF_9') | ~r2_hidden(A_404, '#skF_8'))), inference(resolution, [status(thm)], [c_5324, c_1224])).
% 6.73/2.46  tff(c_5488, plain, (![A_417]: (~r2_hidden(A_417, '#skF_8'))), inference(splitLeft, [status(thm)], [c_5344])).
% 6.73/2.46  tff(c_5529, plain, (![B_426]: (r1_tarski('#skF_8', B_426))), inference(resolution, [status(thm)], [c_6, c_5488])).
% 6.73/2.46  tff(c_5536, plain, (k1_xboole_0='#skF_8'), inference(resolution, [status(thm)], [c_5529, c_252])).
% 6.73/2.46  tff(c_5560, plain, ('#skF_7'!='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_5536, c_98])).
% 6.73/2.46  tff(c_5487, plain, (![A_404]: (~r2_hidden(A_404, '#skF_8'))), inference(splitLeft, [status(thm)], [c_5344])).
% 6.73/2.46  tff(c_5921, plain, (![A_438, B_439]: (r2_hidden(k4_tarski(A_438, B_439), k2_zfmisc_1('#skF_8', '#skF_9')) | ~r2_hidden(B_439, '#skF_7') | ~r2_hidden(A_438, '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_102, c_5324])).
% 6.73/2.46  tff(c_86, plain, (![A_70, C_72, B_71, D_73]: (r2_hidden(A_70, C_72) | ~r2_hidden(k4_tarski(A_70, B_71), k2_zfmisc_1(C_72, D_73)))), inference(cnfTransformation, [status(thm)], [f_123])).
% 6.73/2.46  tff(c_5933, plain, (![A_438, B_439]: (r2_hidden(A_438, '#skF_8') | ~r2_hidden(B_439, '#skF_7') | ~r2_hidden(A_438, '#skF_6'))), inference(resolution, [status(thm)], [c_5921, c_86])).
% 6.73/2.46  tff(c_5941, plain, (![B_439, A_438]: (~r2_hidden(B_439, '#skF_7') | ~r2_hidden(A_438, '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_5487, c_5933])).
% 6.73/2.46  tff(c_6569, plain, (![A_475]: (~r2_hidden(A_475, '#skF_6'))), inference(splitLeft, [status(thm)], [c_5941])).
% 6.73/2.46  tff(c_6602, plain, (![B_2]: (r1_tarski('#skF_6', B_2))), inference(resolution, [status(thm)], [c_6, c_6569])).
% 6.73/2.46  tff(c_6621, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6602, c_5252])).
% 6.73/2.46  tff(c_6624, plain, (![B_478]: (~r2_hidden(B_478, '#skF_7'))), inference(splitRight, [status(thm)], [c_5941])).
% 6.73/2.46  tff(c_6681, plain, (![B_483]: (r1_tarski('#skF_7', B_483))), inference(resolution, [status(thm)], [c_6, c_6624])).
% 6.73/2.46  tff(c_5553, plain, (![A_31]: (A_31='#skF_8' | ~r1_tarski(A_31, '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_5536, c_5536, c_252])).
% 6.73/2.46  tff(c_6685, plain, ('#skF_7'='#skF_8'), inference(resolution, [status(thm)], [c_6681, c_5553])).
% 6.73/2.46  tff(c_6691, plain, $false, inference(negUnitSimplification, [status(thm)], [c_5560, c_6685])).
% 6.73/2.46  tff(c_6717, plain, (![B_485]: (r2_hidden(B_485, '#skF_7') | ~r2_hidden(B_485, '#skF_9'))), inference(splitRight, [status(thm)], [c_5344])).
% 6.73/2.46  tff(c_6731, plain, (![A_486]: (r1_tarski(A_486, '#skF_7') | ~r2_hidden('#skF_1'(A_486, '#skF_7'), '#skF_9'))), inference(resolution, [status(thm)], [c_6717, c_4])).
% 6.73/2.46  tff(c_6735, plain, (r1_tarski('#skF_9', '#skF_7')), inference(resolution, [status(thm)], [c_6, c_6731])).
% 6.73/2.46  tff(c_6739, plain, $false, inference(negUnitSimplification, [status(thm)], [c_5296, c_5296, c_6735])).
% 6.73/2.46  tff(c_6740, plain, (k1_xboole_0='#skF_9'), inference(splitRight, [status(thm)], [c_5284])).
% 6.73/2.46  tff(c_6764, plain, ('#skF_7'!='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_6740, c_98])).
% 6.73/2.46  tff(c_5246, plain, (k1_xboole_0='#skF_8' | r1_tarski('#skF_7', '#skF_9')), inference(splitRight, [status(thm)], [c_2415])).
% 6.73/2.46  tff(c_5253, plain, (r1_tarski('#skF_7', '#skF_9')), inference(splitLeft, [status(thm)], [c_5246])).
% 6.73/2.46  tff(c_6741, plain, (r1_tarski('#skF_9', '#skF_7')), inference(splitRight, [status(thm)], [c_5284])).
% 6.73/2.46  tff(c_6796, plain, ('#skF_7'='#skF_9' | ~r1_tarski('#skF_7', '#skF_9')), inference(resolution, [status(thm)], [c_6741, c_46])).
% 6.73/2.46  tff(c_6799, plain, ('#skF_7'='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_5253, c_6796])).
% 6.73/2.46  tff(c_6801, plain, $false, inference(negUnitSimplification, [status(thm)], [c_6764, c_6799])).
% 6.73/2.46  tff(c_6803, plain, (~r1_tarski('#skF_7', '#skF_9')), inference(splitRight, [status(thm)], [c_5246])).
% 6.73/2.46  tff(c_6802, plain, (k1_xboole_0='#skF_8'), inference(splitRight, [status(thm)], [c_5246])).
% 6.73/2.46  tff(c_6823, plain, (![A_31]: (r1_tarski('#skF_8', A_31))), inference(demodulation, [status(thm), theory('equality')], [c_6802, c_56])).
% 6.73/2.46  tff(c_94, plain, (![A_77, C_79, B_78]: (r1_tarski(k2_zfmisc_1(A_77, C_79), k2_zfmisc_1(B_78, C_79)) | ~r1_tarski(A_77, B_78))), inference(cnfTransformation, [status(thm)], [f_140])).
% 6.73/2.46  tff(c_2407, plain, (![C_226]: (~r1_tarski(k2_zfmisc_1('#skF_8', '#skF_9'), k2_zfmisc_1('#skF_6', C_226)) | r1_tarski('#skF_7', C_226) | k1_xboole_0='#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_102, c_2389])).
% 6.73/2.46  tff(c_7068, plain, (![C_502]: (~r1_tarski(k2_zfmisc_1('#skF_8', '#skF_9'), k2_zfmisc_1('#skF_6', C_502)) | r1_tarski('#skF_7', C_502))), inference(negUnitSimplification, [status(thm)], [c_100, c_2407])).
% 6.73/2.46  tff(c_7079, plain, (r1_tarski('#skF_7', '#skF_9') | ~r1_tarski('#skF_8', '#skF_6')), inference(resolution, [status(thm)], [c_94, c_7068])).
% 6.73/2.46  tff(c_7089, plain, (r1_tarski('#skF_7', '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_6823, c_7079])).
% 6.73/2.46  tff(c_7091, plain, $false, inference(negUnitSimplification, [status(thm)], [c_6803, c_7089])).
% 6.73/2.46  tff(c_7092, plain, ('#skF_7'!='#skF_9'), inference(splitRight, [status(thm)], [c_96])).
% 6.73/2.46  tff(c_7093, plain, ('#skF_6'='#skF_8'), inference(splitRight, [status(thm)], [c_96])).
% 6.73/2.46  tff(c_7094, plain, (k1_xboole_0!='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_7093, c_100])).
% 6.73/2.46  tff(c_50, plain, (![B_27]: (r1_tarski(B_27, B_27))), inference(cnfTransformation, [status(thm)], [f_87])).
% 6.73/2.46  tff(c_7127, plain, (k2_zfmisc_1('#skF_8', '#skF_7')=k2_zfmisc_1('#skF_8', '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_7093, c_102])).
% 6.73/2.46  tff(c_8050, plain, (![A_586, C_587, B_588]: (r1_tarski(k2_zfmisc_1(A_586, C_587), k2_zfmisc_1(B_588, C_587)) | ~r1_tarski(A_586, B_588))), inference(cnfTransformation, [status(thm)], [f_140])).
% 6.73/2.46  tff(c_8055, plain, (![B_588]: (r1_tarski(k2_zfmisc_1('#skF_8', '#skF_9'), k2_zfmisc_1(B_588, '#skF_7')) | ~r1_tarski('#skF_8', B_588))), inference(superposition, [status(thm), theory('equality')], [c_7127, c_8050])).
% 6.73/2.46  tff(c_9574, plain, (![A_649, B_650, C_651]: (~r1_tarski(k2_zfmisc_1(A_649, B_650), k2_zfmisc_1(A_649, C_651)) | r1_tarski(B_650, C_651) | k1_xboole_0=A_649)), inference(cnfTransformation, [status(thm)], [f_134])).
% 6.73/2.46  tff(c_9578, plain, (r1_tarski('#skF_9', '#skF_7') | k1_xboole_0='#skF_8' | ~r1_tarski('#skF_8', '#skF_8')), inference(resolution, [status(thm)], [c_8055, c_9574])).
% 6.73/2.46  tff(c_9608, plain, (r1_tarski('#skF_9', '#skF_7') | k1_xboole_0='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_50, c_9578])).
% 6.73/2.46  tff(c_9609, plain, (r1_tarski('#skF_9', '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_7094, c_9608])).
% 6.73/2.46  tff(c_8058, plain, (![A_586]: (r1_tarski(k2_zfmisc_1(A_586, '#skF_7'), k2_zfmisc_1('#skF_8', '#skF_9')) | ~r1_tarski(A_586, '#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_7127, c_8050])).
% 6.73/2.46  tff(c_9585, plain, (r1_tarski('#skF_7', '#skF_9') | k1_xboole_0='#skF_8' | ~r1_tarski('#skF_8', '#skF_8')), inference(resolution, [status(thm)], [c_8058, c_9574])).
% 6.73/2.46  tff(c_9615, plain, (r1_tarski('#skF_7', '#skF_9') | k1_xboole_0='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_50, c_9585])).
% 6.73/2.46  tff(c_9616, plain, (r1_tarski('#skF_7', '#skF_9')), inference(negUnitSimplification, [status(thm)], [c_7094, c_9615])).
% 6.73/2.46  tff(c_9636, plain, ('#skF_7'='#skF_9' | ~r1_tarski('#skF_9', '#skF_7')), inference(resolution, [status(thm)], [c_9616, c_46])).
% 6.73/2.46  tff(c_9643, plain, ('#skF_7'='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_9609, c_9636])).
% 6.73/2.46  tff(c_9645, plain, $false, inference(negUnitSimplification, [status(thm)], [c_7092, c_9643])).
% 6.73/2.46  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.73/2.46  
% 6.73/2.46  Inference rules
% 6.73/2.46  ----------------------
% 6.73/2.46  #Ref     : 0
% 6.73/2.46  #Sup     : 2094
% 6.73/2.46  #Fact    : 0
% 6.73/2.46  #Define  : 0
% 6.73/2.46  #Split   : 18
% 6.73/2.46  #Chain   : 0
% 6.73/2.46  #Close   : 0
% 6.73/2.46  
% 6.73/2.46  Ordering : KBO
% 6.73/2.46  
% 6.73/2.46  Simplification rules
% 6.73/2.46  ----------------------
% 6.73/2.46  #Subsume      : 143
% 6.73/2.46  #Demod        : 1624
% 6.73/2.46  #Tautology    : 1399
% 6.73/2.46  #SimpNegUnit  : 68
% 6.73/2.46  #BackRed      : 188
% 6.73/2.46  
% 6.73/2.46  #Partial instantiations: 0
% 6.73/2.46  #Strategies tried      : 1
% 6.73/2.46  
% 6.73/2.46  Timing (in seconds)
% 6.73/2.46  ----------------------
% 6.73/2.46  Preprocessing        : 0.38
% 6.73/2.46  Parsing              : 0.20
% 6.73/2.46  CNF conversion       : 0.03
% 6.73/2.46  Main loop            : 1.31
% 6.73/2.46  Inferencing          : 0.45
% 6.73/2.46  Reduction            : 0.47
% 6.73/2.46  Demodulation         : 0.35
% 6.73/2.46  BG Simplification    : 0.05
% 6.73/2.46  Subsumption          : 0.22
% 6.73/2.46  Abstraction          : 0.06
% 6.73/2.46  MUC search           : 0.00
% 6.73/2.46  Cooper               : 0.00
% 6.73/2.46  Total                : 1.74
% 6.73/2.46  Index Insertion      : 0.00
% 6.73/2.46  Index Deletion       : 0.00
% 6.73/2.46  Index Matching       : 0.00
% 6.73/2.46  BG Taut test         : 0.00
%------------------------------------------------------------------------------

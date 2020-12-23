%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:53:16 EST 2020

% Result     : Theorem 14.19s
% Output     : CNFRefutation 14.19s
% Verified   : 
% Statistics : Number of formulae       :  126 ( 241 expanded)
%              Number of leaves         :   31 (  91 expanded)
%              Depth                    :    9
%              Number of atoms          :  161 ( 369 expanded)
%              Number of equality atoms :   75 ( 173 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_8 > #skF_4 > #skF_2 > #skF_1

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_105,negated_conjecture,(
    ~ ! [A,B,C] :
        ( k4_xboole_0(k2_tarski(A,B),C) = k1_xboole_0
      <=> ( r2_hidden(A,C)
          & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_zfmisc_1)).

tff(f_58,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_xboole_0(k1_tarski(A),k1_tarski(B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).

tff(f_41,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_xboole_1)).

tff(f_66,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_zfmisc_1)).

tff(f_29,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_90,axiom,(
    ! [A,B,C] :
      ( k4_xboole_0(k2_tarski(A,B),C) = k1_tarski(A)
    <=> ( ~ r2_hidden(A,C)
        & ( r2_hidden(B,C)
          | A = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_zfmisc_1)).

tff(f_98,axiom,(
    ! [A,B,C] :
      ( k4_xboole_0(k2_tarski(A,B),C) = k2_tarski(A,B)
    <=> ( ~ r2_hidden(A,C)
        & ~ r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_zfmisc_1)).

tff(f_72,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_39,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(c_72,plain,
    ( r2_hidden('#skF_4','#skF_5')
    | ~ r2_hidden('#skF_7','#skF_8')
    | ~ r2_hidden('#skF_6','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_175,plain,(
    ~ r2_hidden('#skF_6','#skF_8') ),
    inference(splitLeft,[status(thm)],[c_72])).

tff(c_603,plain,(
    ! [A_86,B_87] : k2_xboole_0(k1_tarski(A_86),k1_tarski(B_87)) = k2_tarski(A_86,B_87) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_16,plain,(
    ! [A_11,B_12] : k4_xboole_0(A_11,k2_xboole_0(A_11,B_12)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_628,plain,(
    ! [A_86,B_87] : k4_xboole_0(k1_tarski(A_86),k2_tarski(A_86,B_87)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_603,c_16])).

tff(c_420,plain,(
    ! [A_70,B_71] :
      ( r1_tarski(A_70,B_71)
      | k4_xboole_0(A_70,B_71) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_42,plain,(
    ! [A_27,B_28] :
      ( r2_hidden(A_27,B_28)
      | ~ r1_tarski(k1_tarski(A_27),B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_1294,plain,(
    ! [A_112,B_113] :
      ( r2_hidden(A_112,B_113)
      | k4_xboole_0(k1_tarski(A_112),B_113) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_420,c_42])).

tff(c_1326,plain,(
    ! [A_86,B_87] : r2_hidden(A_86,k2_tarski(A_86,B_87)) ),
    inference(superposition,[status(thm),theory(equality)],[c_628,c_1294])).

tff(c_4,plain,(
    ! [A_3] : k2_xboole_0(A_3,k1_xboole_0) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_105,plain,(
    ! [A_46,B_47] : k4_xboole_0(A_46,k2_xboole_0(A_46,B_47)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_118,plain,(
    ! [A_3] : k4_xboole_0(A_3,A_3) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_105])).

tff(c_1539,plain,(
    ! [A_125,C_126,B_127] :
      ( ~ r2_hidden(A_125,C_126)
      | k4_xboole_0(k2_tarski(A_125,B_127),C_126) != k1_tarski(A_125) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_1567,plain,(
    ! [A_125,B_127] :
      ( ~ r2_hidden(A_125,k2_tarski(A_125,B_127))
      | k1_tarski(A_125) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_118,c_1539])).

tff(c_1573,plain,(
    ! [A_125] : k1_tarski(A_125) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1326,c_1567])).

tff(c_3170,plain,(
    ! [B_173,C_174,A_175] :
      ( ~ r2_hidden(B_173,C_174)
      | k4_xboole_0(k2_tarski(A_175,B_173),C_174) = k1_tarski(A_175)
      | r2_hidden(A_175,C_174) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_78,plain,
    ( r2_hidden('#skF_4','#skF_5')
    | k4_xboole_0(k2_tarski('#skF_6','#skF_7'),'#skF_8') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_363,plain,(
    k4_xboole_0(k2_tarski('#skF_6','#skF_7'),'#skF_8') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_78])).

tff(c_3212,plain,
    ( k1_tarski('#skF_6') = k1_xboole_0
    | ~ r2_hidden('#skF_7','#skF_8')
    | r2_hidden('#skF_6','#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_3170,c_363])).

tff(c_3261,plain,(
    ~ r2_hidden('#skF_7','#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_175,c_1573,c_3212])).

tff(c_1733,plain,(
    ! [A_136,C_137,B_138] :
      ( ~ r2_hidden(A_136,C_137)
      | k4_xboole_0(k2_tarski(A_136,B_138),C_137) != k2_tarski(A_136,B_138) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_1761,plain,(
    ! [A_136,B_138] :
      ( ~ r2_hidden(A_136,k2_tarski(A_136,B_138))
      | k2_tarski(A_136,B_138) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_118,c_1733])).

tff(c_1769,plain,(
    ! [A_136,B_138] : k2_tarski(A_136,B_138) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1326,c_1761])).

tff(c_3949,plain,(
    ! [A_186,B_187,C_188] :
      ( k4_xboole_0(k2_tarski(A_186,B_187),C_188) = k2_tarski(A_186,B_187)
      | r2_hidden(B_187,C_188)
      | r2_hidden(A_186,C_188) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_3998,plain,
    ( k2_tarski('#skF_6','#skF_7') = k1_xboole_0
    | r2_hidden('#skF_7','#skF_8')
    | r2_hidden('#skF_6','#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_3949,c_363])).

tff(c_4061,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_175,c_3261,c_1769,c_3998])).

tff(c_4062,plain,(
    r2_hidden('#skF_4','#skF_5') ),
    inference(splitRight,[status(thm)],[c_78])).

tff(c_4063,plain,(
    k4_xboole_0(k2_tarski('#skF_6','#skF_7'),'#skF_8') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_78])).

tff(c_80,plain,
    ( r2_hidden('#skF_3','#skF_5')
    | k4_xboole_0(k2_tarski('#skF_6','#skF_7'),'#skF_8') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_4065,plain,(
    r2_hidden('#skF_3','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_4063,c_80])).

tff(c_5165,plain,(
    ! [A_262,B_263,C_264] :
      ( r1_tarski(k2_tarski(A_262,B_263),C_264)
      | ~ r2_hidden(B_263,C_264)
      | ~ r2_hidden(A_262,C_264) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_12,plain,(
    ! [A_7,B_8] :
      ( k4_xboole_0(A_7,B_8) = k1_xboole_0
      | ~ r1_tarski(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_9606,plain,(
    ! [A_367,B_368,C_369] :
      ( k4_xboole_0(k2_tarski(A_367,B_368),C_369) = k1_xboole_0
      | ~ r2_hidden(B_368,C_369)
      | ~ r2_hidden(A_367,C_369) ) ),
    inference(resolution,[status(thm)],[c_5165,c_12])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4275,plain,(
    ! [A_209,B_210] : k2_xboole_0(k1_tarski(A_209),k1_tarski(B_210)) = k2_tarski(A_209,B_210) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_4715,plain,(
    ! [B_233,A_234] : k2_xboole_0(k1_tarski(B_233),k1_tarski(A_234)) = k2_tarski(A_234,B_233) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_4275])).

tff(c_38,plain,(
    ! [A_23,B_24] : k2_xboole_0(k1_tarski(A_23),k1_tarski(B_24)) = k2_tarski(A_23,B_24) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_4731,plain,(
    ! [B_233,A_234] : k2_tarski(B_233,A_234) = k2_tarski(A_234,B_233) ),
    inference(superposition,[status(thm),theory(equality)],[c_4715,c_38])).

tff(c_76,plain,
    ( k4_xboole_0(k2_tarski('#skF_3','#skF_4'),'#skF_5') != k1_xboole_0
    | k4_xboole_0(k2_tarski('#skF_6','#skF_7'),'#skF_8') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_4392,plain,(
    k4_xboole_0(k2_tarski('#skF_3','#skF_4'),'#skF_5') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_4063,c_76])).

tff(c_4788,plain,(
    k4_xboole_0(k2_tarski('#skF_4','#skF_3'),'#skF_5') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4731,c_4392])).

tff(c_9656,plain,
    ( ~ r2_hidden('#skF_3','#skF_5')
    | ~ r2_hidden('#skF_4','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_9606,c_4788])).

tff(c_9746,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4062,c_4065,c_9656])).

tff(c_9747,plain,
    ( ~ r2_hidden('#skF_7','#skF_8')
    | r2_hidden('#skF_4','#skF_5') ),
    inference(splitRight,[status(thm)],[c_72])).

tff(c_9891,plain,(
    ~ r2_hidden('#skF_7','#skF_8') ),
    inference(splitLeft,[status(thm)],[c_9747])).

tff(c_10220,plain,(
    ! [A_407,B_408] : k2_xboole_0(A_407,k4_xboole_0(B_408,A_407)) = k2_xboole_0(A_407,B_408) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_10275,plain,(
    ! [A_3] : k2_xboole_0(A_3,k1_xboole_0) = k2_xboole_0(A_3,A_3) ),
    inference(superposition,[status(thm),theory(equality)],[c_118,c_10220])).

tff(c_10294,plain,(
    ! [A_3] : k2_xboole_0(A_3,A_3) = A_3 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_10275])).

tff(c_9852,plain,(
    k4_xboole_0(k2_tarski('#skF_6','#skF_7'),'#skF_8') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_80])).

tff(c_10268,plain,(
    k2_xboole_0('#skF_8',k2_tarski('#skF_6','#skF_7')) = k2_xboole_0('#skF_8',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_9852,c_10220])).

tff(c_10292,plain,(
    k2_xboole_0('#skF_8',k2_tarski('#skF_6','#skF_7')) = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_10268])).

tff(c_9749,plain,(
    ! [B_370,A_371] : k2_xboole_0(B_370,A_371) = k2_xboole_0(A_371,B_370) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_9770,plain,(
    ! [A_371,B_370] : k4_xboole_0(A_371,k2_xboole_0(B_370,A_371)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_9749,c_16])).

tff(c_10265,plain,(
    ! [B_370,A_371] : k2_xboole_0(k2_xboole_0(B_370,A_371),k1_xboole_0) = k2_xboole_0(k2_xboole_0(B_370,A_371),A_371) ),
    inference(superposition,[status(thm),theory(equality)],[c_9770,c_10220])).

tff(c_11426,plain,(
    ! [B_459,A_460] : k2_xboole_0(k2_xboole_0(B_459,A_460),A_460) = k2_xboole_0(B_459,A_460) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_10265])).

tff(c_12383,plain,(
    ! [A_479,B_480] : k2_xboole_0(k2_xboole_0(A_479,B_480),A_479) = k2_xboole_0(B_480,A_479) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_11426])).

tff(c_12502,plain,(
    k2_xboole_0(k2_tarski('#skF_6','#skF_7'),'#skF_8') = k2_xboole_0('#skF_8','#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_10292,c_12383])).

tff(c_12570,plain,(
    k2_xboole_0(k2_tarski('#skF_6','#skF_7'),'#skF_8') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10294,c_12502])).

tff(c_10113,plain,(
    ! [A_400,B_401] : k2_xboole_0(k1_tarski(A_400),k1_tarski(B_401)) = k2_tarski(A_400,B_401) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_10413,plain,(
    ! [B_414,A_415] : k2_xboole_0(k1_tarski(B_414),k1_tarski(A_415)) = k2_tarski(A_415,B_414) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_10113])).

tff(c_10423,plain,(
    ! [B_414,A_415] : k2_tarski(B_414,A_415) = k2_tarski(A_415,B_414) ),
    inference(superposition,[status(thm),theory(equality)],[c_10413,c_38])).

tff(c_10,plain,(
    ! [A_7,B_8] :
      ( r1_tarski(A_7,B_8)
      | k4_xboole_0(A_7,B_8) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_10384,plain,(
    ! [A_411,C_412,B_413] :
      ( r2_hidden(A_411,C_412)
      | ~ r1_tarski(k2_tarski(A_411,B_413),C_412) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_14236,plain,(
    ! [A_513,B_514,B_515] :
      ( r2_hidden(A_513,B_514)
      | k4_xboole_0(k2_tarski(A_513,B_515),B_514) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_10,c_10384])).

tff(c_14291,plain,(
    ! [A_516,B_517,B_518] : r2_hidden(A_516,k2_xboole_0(k2_tarski(A_516,B_517),B_518)) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_14236])).

tff(c_14417,plain,(
    ! [A_522,B_523,B_524] : r2_hidden(A_522,k2_xboole_0(k2_tarski(B_523,A_522),B_524)) ),
    inference(superposition,[status(thm),theory(equality)],[c_10423,c_14291])).

tff(c_14424,plain,(
    r2_hidden('#skF_7','#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_12570,c_14417])).

tff(c_14471,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_9891,c_14424])).

tff(c_14472,plain,(
    r2_hidden('#skF_4','#skF_5') ),
    inference(splitRight,[status(thm)],[c_9747])).

tff(c_9748,plain,(
    r2_hidden('#skF_6','#skF_8') ),
    inference(splitRight,[status(thm)],[c_72])).

tff(c_14473,plain,(
    r2_hidden('#skF_7','#skF_8') ),
    inference(splitRight,[status(thm)],[c_9747])).

tff(c_74,plain,
    ( r2_hidden('#skF_3','#skF_5')
    | ~ r2_hidden('#skF_7','#skF_8')
    | ~ r2_hidden('#skF_6','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_14643,plain,(
    r2_hidden('#skF_3','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9748,c_14473,c_74])).

tff(c_15831,plain,(
    ! [A_605,B_606,C_607] :
      ( r1_tarski(k2_tarski(A_605,B_606),C_607)
      | ~ r2_hidden(B_606,C_607)
      | ~ r2_hidden(A_605,C_607) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_20632,plain,(
    ! [A_707,B_708,C_709] :
      ( k4_xboole_0(k2_tarski(A_707,B_708),C_709) = k1_xboole_0
      | ~ r2_hidden(B_708,C_709)
      | ~ r2_hidden(A_707,C_709) ) ),
    inference(resolution,[status(thm)],[c_15831,c_12])).

tff(c_14645,plain,(
    ! [A_546,B_547] : k2_xboole_0(k1_tarski(A_546),k1_tarski(B_547)) = k2_tarski(A_546,B_547) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_15112,plain,(
    ! [B_569,A_570] : k2_xboole_0(k1_tarski(B_569),k1_tarski(A_570)) = k2_tarski(A_570,B_569) ),
    inference(superposition,[status(thm),theory(equality)],[c_14645,c_2])).

tff(c_15125,plain,(
    ! [B_569,A_570] : k2_tarski(B_569,A_570) = k2_tarski(A_570,B_569) ),
    inference(superposition,[status(thm),theory(equality)],[c_15112,c_38])).

tff(c_70,plain,
    ( k4_xboole_0(k2_tarski('#skF_3','#skF_4'),'#skF_5') != k1_xboole_0
    | ~ r2_hidden('#skF_7','#skF_8')
    | ~ r2_hidden('#skF_6','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_14793,plain,(
    k4_xboole_0(k2_tarski('#skF_3','#skF_4'),'#skF_5') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_9748,c_14473,c_70])).

tff(c_15177,plain,(
    k4_xboole_0(k2_tarski('#skF_4','#skF_3'),'#skF_5') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_15125,c_14793])).

tff(c_20679,plain,
    ( ~ r2_hidden('#skF_3','#skF_5')
    | ~ r2_hidden('#skF_4','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_20632,c_15177])).

tff(c_20771,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14472,c_14643,c_20679])).

tff(c_20773,plain,(
    k4_xboole_0(k2_tarski('#skF_6','#skF_7'),'#skF_8') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_80])).

tff(c_20901,plain,(
    r2_hidden('#skF_4','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_20773,c_78])).

tff(c_20772,plain,(
    r2_hidden('#skF_3','#skF_5') ),
    inference(splitRight,[status(thm)],[c_80])).

tff(c_21661,plain,(
    ! [A_775,B_776,C_777] :
      ( r1_tarski(k2_tarski(A_775,B_776),C_777)
      | ~ r2_hidden(B_776,C_777)
      | ~ r2_hidden(A_775,C_777) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_26295,plain,(
    ! [A_893,B_894,C_895] :
      ( k4_xboole_0(k2_tarski(A_893,B_894),C_895) = k1_xboole_0
      | ~ r2_hidden(B_894,C_895)
      | ~ r2_hidden(A_893,C_895) ) ),
    inference(resolution,[status(thm)],[c_21661,c_12])).

tff(c_21186,plain,(
    ! [A_741,B_742] : k2_xboole_0(k1_tarski(A_741),k1_tarski(B_742)) = k2_tarski(A_741,B_742) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_21792,plain,(
    ! [B_780,A_781] : k2_xboole_0(k1_tarski(B_780),k1_tarski(A_781)) = k2_tarski(A_781,B_780) ),
    inference(superposition,[status(thm),theory(equality)],[c_21186,c_2])).

tff(c_21810,plain,(
    ! [B_780,A_781] : k2_tarski(B_780,A_781) = k2_tarski(A_781,B_780) ),
    inference(superposition,[status(thm),theory(equality)],[c_21792,c_38])).

tff(c_21016,plain,(
    k4_xboole_0(k2_tarski('#skF_3','#skF_4'),'#skF_5') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_20773,c_76])).

tff(c_21873,plain,(
    k4_xboole_0(k2_tarski('#skF_4','#skF_3'),'#skF_5') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_21810,c_21016])).

tff(c_26339,plain,
    ( ~ r2_hidden('#skF_3','#skF_5')
    | ~ r2_hidden('#skF_4','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_26295,c_21873])).

tff(c_26431,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_20901,c_20772,c_26339])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n017.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:01:31 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 14.19/5.83  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 14.19/5.85  
% 14.19/5.85  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 14.19/5.85  %$ r2_hidden > r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_8 > #skF_4 > #skF_2 > #skF_1
% 14.19/5.85  
% 14.19/5.85  %Foreground sorts:
% 14.19/5.85  
% 14.19/5.85  
% 14.19/5.85  %Background operators:
% 14.19/5.85  
% 14.19/5.85  
% 14.19/5.85  %Foreground operators:
% 14.19/5.85  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 14.19/5.85  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 14.19/5.85  tff(k1_tarski, type, k1_tarski: $i > $i).
% 14.19/5.85  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 14.19/5.85  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 14.19/5.85  tff('#skF_7', type, '#skF_7': $i).
% 14.19/5.85  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 14.19/5.85  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 14.19/5.85  tff('#skF_5', type, '#skF_5': $i).
% 14.19/5.85  tff('#skF_6', type, '#skF_6': $i).
% 14.19/5.85  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 14.19/5.85  tff('#skF_3', type, '#skF_3': $i).
% 14.19/5.85  tff('#skF_8', type, '#skF_8': $i).
% 14.19/5.85  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 14.19/5.85  tff('#skF_4', type, '#skF_4': $i).
% 14.19/5.85  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 14.19/5.85  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 14.19/5.85  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 14.19/5.85  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 14.19/5.85  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 14.19/5.85  
% 14.19/5.89  tff(f_105, negated_conjecture, ~(![A, B, C]: ((k4_xboole_0(k2_tarski(A, B), C) = k1_xboole_0) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_zfmisc_1)).
% 14.19/5.89  tff(f_58, axiom, (![A, B]: (k2_tarski(A, B) = k2_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_enumset1)).
% 14.19/5.89  tff(f_41, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_xboole_1)).
% 14.19/5.89  tff(f_37, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t37_xboole_1)).
% 14.19/5.89  tff(f_66, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t37_zfmisc_1)).
% 14.19/5.89  tff(f_29, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 14.19/5.89  tff(f_90, axiom, (![A, B, C]: ((k4_xboole_0(k2_tarski(A, B), C) = k1_tarski(A)) <=> (~r2_hidden(A, C) & (r2_hidden(B, C) | (A = B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_zfmisc_1)).
% 14.19/5.89  tff(f_98, axiom, (![A, B, C]: ((k4_xboole_0(k2_tarski(A, B), C) = k2_tarski(A, B)) <=> (~r2_hidden(A, C) & ~r2_hidden(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_zfmisc_1)).
% 14.19/5.89  tff(f_72, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 14.19/5.89  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 14.19/5.89  tff(f_39, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 14.19/5.89  tff(c_72, plain, (r2_hidden('#skF_4', '#skF_5') | ~r2_hidden('#skF_7', '#skF_8') | ~r2_hidden('#skF_6', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_105])).
% 14.19/5.89  tff(c_175, plain, (~r2_hidden('#skF_6', '#skF_8')), inference(splitLeft, [status(thm)], [c_72])).
% 14.19/5.89  tff(c_603, plain, (![A_86, B_87]: (k2_xboole_0(k1_tarski(A_86), k1_tarski(B_87))=k2_tarski(A_86, B_87))), inference(cnfTransformation, [status(thm)], [f_58])).
% 14.19/5.89  tff(c_16, plain, (![A_11, B_12]: (k4_xboole_0(A_11, k2_xboole_0(A_11, B_12))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_41])).
% 14.19/5.89  tff(c_628, plain, (![A_86, B_87]: (k4_xboole_0(k1_tarski(A_86), k2_tarski(A_86, B_87))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_603, c_16])).
% 14.19/5.89  tff(c_420, plain, (![A_70, B_71]: (r1_tarski(A_70, B_71) | k4_xboole_0(A_70, B_71)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 14.19/5.89  tff(c_42, plain, (![A_27, B_28]: (r2_hidden(A_27, B_28) | ~r1_tarski(k1_tarski(A_27), B_28))), inference(cnfTransformation, [status(thm)], [f_66])).
% 14.19/5.89  tff(c_1294, plain, (![A_112, B_113]: (r2_hidden(A_112, B_113) | k4_xboole_0(k1_tarski(A_112), B_113)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_420, c_42])).
% 14.19/5.89  tff(c_1326, plain, (![A_86, B_87]: (r2_hidden(A_86, k2_tarski(A_86, B_87)))), inference(superposition, [status(thm), theory('equality')], [c_628, c_1294])).
% 14.19/5.89  tff(c_4, plain, (![A_3]: (k2_xboole_0(A_3, k1_xboole_0)=A_3)), inference(cnfTransformation, [status(thm)], [f_29])).
% 14.19/5.89  tff(c_105, plain, (![A_46, B_47]: (k4_xboole_0(A_46, k2_xboole_0(A_46, B_47))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_41])).
% 14.19/5.89  tff(c_118, plain, (![A_3]: (k4_xboole_0(A_3, A_3)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_4, c_105])).
% 14.19/5.89  tff(c_1539, plain, (![A_125, C_126, B_127]: (~r2_hidden(A_125, C_126) | k4_xboole_0(k2_tarski(A_125, B_127), C_126)!=k1_tarski(A_125))), inference(cnfTransformation, [status(thm)], [f_90])).
% 14.19/5.89  tff(c_1567, plain, (![A_125, B_127]: (~r2_hidden(A_125, k2_tarski(A_125, B_127)) | k1_tarski(A_125)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_118, c_1539])).
% 14.19/5.89  tff(c_1573, plain, (![A_125]: (k1_tarski(A_125)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1326, c_1567])).
% 14.19/5.89  tff(c_3170, plain, (![B_173, C_174, A_175]: (~r2_hidden(B_173, C_174) | k4_xboole_0(k2_tarski(A_175, B_173), C_174)=k1_tarski(A_175) | r2_hidden(A_175, C_174))), inference(cnfTransformation, [status(thm)], [f_90])).
% 14.19/5.89  tff(c_78, plain, (r2_hidden('#skF_4', '#skF_5') | k4_xboole_0(k2_tarski('#skF_6', '#skF_7'), '#skF_8')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_105])).
% 14.19/5.89  tff(c_363, plain, (k4_xboole_0(k2_tarski('#skF_6', '#skF_7'), '#skF_8')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_78])).
% 14.19/5.89  tff(c_3212, plain, (k1_tarski('#skF_6')=k1_xboole_0 | ~r2_hidden('#skF_7', '#skF_8') | r2_hidden('#skF_6', '#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_3170, c_363])).
% 14.19/5.89  tff(c_3261, plain, (~r2_hidden('#skF_7', '#skF_8')), inference(negUnitSimplification, [status(thm)], [c_175, c_1573, c_3212])).
% 14.19/5.89  tff(c_1733, plain, (![A_136, C_137, B_138]: (~r2_hidden(A_136, C_137) | k4_xboole_0(k2_tarski(A_136, B_138), C_137)!=k2_tarski(A_136, B_138))), inference(cnfTransformation, [status(thm)], [f_98])).
% 14.19/5.89  tff(c_1761, plain, (![A_136, B_138]: (~r2_hidden(A_136, k2_tarski(A_136, B_138)) | k2_tarski(A_136, B_138)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_118, c_1733])).
% 14.19/5.89  tff(c_1769, plain, (![A_136, B_138]: (k2_tarski(A_136, B_138)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1326, c_1761])).
% 14.19/5.89  tff(c_3949, plain, (![A_186, B_187, C_188]: (k4_xboole_0(k2_tarski(A_186, B_187), C_188)=k2_tarski(A_186, B_187) | r2_hidden(B_187, C_188) | r2_hidden(A_186, C_188))), inference(cnfTransformation, [status(thm)], [f_98])).
% 14.19/5.89  tff(c_3998, plain, (k2_tarski('#skF_6', '#skF_7')=k1_xboole_0 | r2_hidden('#skF_7', '#skF_8') | r2_hidden('#skF_6', '#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_3949, c_363])).
% 14.19/5.89  tff(c_4061, plain, $false, inference(negUnitSimplification, [status(thm)], [c_175, c_3261, c_1769, c_3998])).
% 14.19/5.89  tff(c_4062, plain, (r2_hidden('#skF_4', '#skF_5')), inference(splitRight, [status(thm)], [c_78])).
% 14.19/5.89  tff(c_4063, plain, (k4_xboole_0(k2_tarski('#skF_6', '#skF_7'), '#skF_8')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_78])).
% 14.19/5.89  tff(c_80, plain, (r2_hidden('#skF_3', '#skF_5') | k4_xboole_0(k2_tarski('#skF_6', '#skF_7'), '#skF_8')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_105])).
% 14.19/5.89  tff(c_4065, plain, (r2_hidden('#skF_3', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_4063, c_80])).
% 14.19/5.89  tff(c_5165, plain, (![A_262, B_263, C_264]: (r1_tarski(k2_tarski(A_262, B_263), C_264) | ~r2_hidden(B_263, C_264) | ~r2_hidden(A_262, C_264))), inference(cnfTransformation, [status(thm)], [f_72])).
% 14.19/5.89  tff(c_12, plain, (![A_7, B_8]: (k4_xboole_0(A_7, B_8)=k1_xboole_0 | ~r1_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_37])).
% 14.19/5.89  tff(c_9606, plain, (![A_367, B_368, C_369]: (k4_xboole_0(k2_tarski(A_367, B_368), C_369)=k1_xboole_0 | ~r2_hidden(B_368, C_369) | ~r2_hidden(A_367, C_369))), inference(resolution, [status(thm)], [c_5165, c_12])).
% 14.19/5.89  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 14.19/5.89  tff(c_4275, plain, (![A_209, B_210]: (k2_xboole_0(k1_tarski(A_209), k1_tarski(B_210))=k2_tarski(A_209, B_210))), inference(cnfTransformation, [status(thm)], [f_58])).
% 14.19/5.89  tff(c_4715, plain, (![B_233, A_234]: (k2_xboole_0(k1_tarski(B_233), k1_tarski(A_234))=k2_tarski(A_234, B_233))), inference(superposition, [status(thm), theory('equality')], [c_2, c_4275])).
% 14.19/5.89  tff(c_38, plain, (![A_23, B_24]: (k2_xboole_0(k1_tarski(A_23), k1_tarski(B_24))=k2_tarski(A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_58])).
% 14.19/5.89  tff(c_4731, plain, (![B_233, A_234]: (k2_tarski(B_233, A_234)=k2_tarski(A_234, B_233))), inference(superposition, [status(thm), theory('equality')], [c_4715, c_38])).
% 14.19/5.89  tff(c_76, plain, (k4_xboole_0(k2_tarski('#skF_3', '#skF_4'), '#skF_5')!=k1_xboole_0 | k4_xboole_0(k2_tarski('#skF_6', '#skF_7'), '#skF_8')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_105])).
% 14.19/5.89  tff(c_4392, plain, (k4_xboole_0(k2_tarski('#skF_3', '#skF_4'), '#skF_5')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_4063, c_76])).
% 14.19/5.89  tff(c_4788, plain, (k4_xboole_0(k2_tarski('#skF_4', '#skF_3'), '#skF_5')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_4731, c_4392])).
% 14.19/5.89  tff(c_9656, plain, (~r2_hidden('#skF_3', '#skF_5') | ~r2_hidden('#skF_4', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_9606, c_4788])).
% 14.19/5.89  tff(c_9746, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4062, c_4065, c_9656])).
% 14.19/5.89  tff(c_9747, plain, (~r2_hidden('#skF_7', '#skF_8') | r2_hidden('#skF_4', '#skF_5')), inference(splitRight, [status(thm)], [c_72])).
% 14.19/5.89  tff(c_9891, plain, (~r2_hidden('#skF_7', '#skF_8')), inference(splitLeft, [status(thm)], [c_9747])).
% 14.19/5.89  tff(c_10220, plain, (![A_407, B_408]: (k2_xboole_0(A_407, k4_xboole_0(B_408, A_407))=k2_xboole_0(A_407, B_408))), inference(cnfTransformation, [status(thm)], [f_39])).
% 14.19/5.89  tff(c_10275, plain, (![A_3]: (k2_xboole_0(A_3, k1_xboole_0)=k2_xboole_0(A_3, A_3))), inference(superposition, [status(thm), theory('equality')], [c_118, c_10220])).
% 14.19/5.89  tff(c_10294, plain, (![A_3]: (k2_xboole_0(A_3, A_3)=A_3)), inference(demodulation, [status(thm), theory('equality')], [c_4, c_10275])).
% 14.19/5.89  tff(c_9852, plain, (k4_xboole_0(k2_tarski('#skF_6', '#skF_7'), '#skF_8')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_80])).
% 14.19/5.89  tff(c_10268, plain, (k2_xboole_0('#skF_8', k2_tarski('#skF_6', '#skF_7'))=k2_xboole_0('#skF_8', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_9852, c_10220])).
% 14.19/5.89  tff(c_10292, plain, (k2_xboole_0('#skF_8', k2_tarski('#skF_6', '#skF_7'))='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_4, c_10268])).
% 14.19/5.89  tff(c_9749, plain, (![B_370, A_371]: (k2_xboole_0(B_370, A_371)=k2_xboole_0(A_371, B_370))), inference(cnfTransformation, [status(thm)], [f_27])).
% 14.19/5.89  tff(c_9770, plain, (![A_371, B_370]: (k4_xboole_0(A_371, k2_xboole_0(B_370, A_371))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_9749, c_16])).
% 14.19/5.89  tff(c_10265, plain, (![B_370, A_371]: (k2_xboole_0(k2_xboole_0(B_370, A_371), k1_xboole_0)=k2_xboole_0(k2_xboole_0(B_370, A_371), A_371))), inference(superposition, [status(thm), theory('equality')], [c_9770, c_10220])).
% 14.19/5.89  tff(c_11426, plain, (![B_459, A_460]: (k2_xboole_0(k2_xboole_0(B_459, A_460), A_460)=k2_xboole_0(B_459, A_460))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_10265])).
% 14.19/5.89  tff(c_12383, plain, (![A_479, B_480]: (k2_xboole_0(k2_xboole_0(A_479, B_480), A_479)=k2_xboole_0(B_480, A_479))), inference(superposition, [status(thm), theory('equality')], [c_2, c_11426])).
% 14.19/5.89  tff(c_12502, plain, (k2_xboole_0(k2_tarski('#skF_6', '#skF_7'), '#skF_8')=k2_xboole_0('#skF_8', '#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_10292, c_12383])).
% 14.19/5.89  tff(c_12570, plain, (k2_xboole_0(k2_tarski('#skF_6', '#skF_7'), '#skF_8')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_10294, c_12502])).
% 14.19/5.89  tff(c_10113, plain, (![A_400, B_401]: (k2_xboole_0(k1_tarski(A_400), k1_tarski(B_401))=k2_tarski(A_400, B_401))), inference(cnfTransformation, [status(thm)], [f_58])).
% 14.19/5.89  tff(c_10413, plain, (![B_414, A_415]: (k2_xboole_0(k1_tarski(B_414), k1_tarski(A_415))=k2_tarski(A_415, B_414))), inference(superposition, [status(thm), theory('equality')], [c_2, c_10113])).
% 14.19/5.89  tff(c_10423, plain, (![B_414, A_415]: (k2_tarski(B_414, A_415)=k2_tarski(A_415, B_414))), inference(superposition, [status(thm), theory('equality')], [c_10413, c_38])).
% 14.19/5.89  tff(c_10, plain, (![A_7, B_8]: (r1_tarski(A_7, B_8) | k4_xboole_0(A_7, B_8)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 14.19/5.89  tff(c_10384, plain, (![A_411, C_412, B_413]: (r2_hidden(A_411, C_412) | ~r1_tarski(k2_tarski(A_411, B_413), C_412))), inference(cnfTransformation, [status(thm)], [f_72])).
% 14.19/5.89  tff(c_14236, plain, (![A_513, B_514, B_515]: (r2_hidden(A_513, B_514) | k4_xboole_0(k2_tarski(A_513, B_515), B_514)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_10, c_10384])).
% 14.19/5.89  tff(c_14291, plain, (![A_516, B_517, B_518]: (r2_hidden(A_516, k2_xboole_0(k2_tarski(A_516, B_517), B_518)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_14236])).
% 14.19/5.89  tff(c_14417, plain, (![A_522, B_523, B_524]: (r2_hidden(A_522, k2_xboole_0(k2_tarski(B_523, A_522), B_524)))), inference(superposition, [status(thm), theory('equality')], [c_10423, c_14291])).
% 14.19/5.89  tff(c_14424, plain, (r2_hidden('#skF_7', '#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_12570, c_14417])).
% 14.19/5.89  tff(c_14471, plain, $false, inference(negUnitSimplification, [status(thm)], [c_9891, c_14424])).
% 14.19/5.89  tff(c_14472, plain, (r2_hidden('#skF_4', '#skF_5')), inference(splitRight, [status(thm)], [c_9747])).
% 14.19/5.89  tff(c_9748, plain, (r2_hidden('#skF_6', '#skF_8')), inference(splitRight, [status(thm)], [c_72])).
% 14.19/5.89  tff(c_14473, plain, (r2_hidden('#skF_7', '#skF_8')), inference(splitRight, [status(thm)], [c_9747])).
% 14.19/5.89  tff(c_74, plain, (r2_hidden('#skF_3', '#skF_5') | ~r2_hidden('#skF_7', '#skF_8') | ~r2_hidden('#skF_6', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_105])).
% 14.19/5.89  tff(c_14643, plain, (r2_hidden('#skF_3', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_9748, c_14473, c_74])).
% 14.19/5.89  tff(c_15831, plain, (![A_605, B_606, C_607]: (r1_tarski(k2_tarski(A_605, B_606), C_607) | ~r2_hidden(B_606, C_607) | ~r2_hidden(A_605, C_607))), inference(cnfTransformation, [status(thm)], [f_72])).
% 14.19/5.89  tff(c_20632, plain, (![A_707, B_708, C_709]: (k4_xboole_0(k2_tarski(A_707, B_708), C_709)=k1_xboole_0 | ~r2_hidden(B_708, C_709) | ~r2_hidden(A_707, C_709))), inference(resolution, [status(thm)], [c_15831, c_12])).
% 14.19/5.89  tff(c_14645, plain, (![A_546, B_547]: (k2_xboole_0(k1_tarski(A_546), k1_tarski(B_547))=k2_tarski(A_546, B_547))), inference(cnfTransformation, [status(thm)], [f_58])).
% 14.19/5.89  tff(c_15112, plain, (![B_569, A_570]: (k2_xboole_0(k1_tarski(B_569), k1_tarski(A_570))=k2_tarski(A_570, B_569))), inference(superposition, [status(thm), theory('equality')], [c_14645, c_2])).
% 14.19/5.89  tff(c_15125, plain, (![B_569, A_570]: (k2_tarski(B_569, A_570)=k2_tarski(A_570, B_569))), inference(superposition, [status(thm), theory('equality')], [c_15112, c_38])).
% 14.19/5.89  tff(c_70, plain, (k4_xboole_0(k2_tarski('#skF_3', '#skF_4'), '#skF_5')!=k1_xboole_0 | ~r2_hidden('#skF_7', '#skF_8') | ~r2_hidden('#skF_6', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_105])).
% 14.19/5.89  tff(c_14793, plain, (k4_xboole_0(k2_tarski('#skF_3', '#skF_4'), '#skF_5')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_9748, c_14473, c_70])).
% 14.19/5.89  tff(c_15177, plain, (k4_xboole_0(k2_tarski('#skF_4', '#skF_3'), '#skF_5')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_15125, c_14793])).
% 14.19/5.89  tff(c_20679, plain, (~r2_hidden('#skF_3', '#skF_5') | ~r2_hidden('#skF_4', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_20632, c_15177])).
% 14.19/5.89  tff(c_20771, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_14472, c_14643, c_20679])).
% 14.19/5.89  tff(c_20773, plain, (k4_xboole_0(k2_tarski('#skF_6', '#skF_7'), '#skF_8')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_80])).
% 14.19/5.89  tff(c_20901, plain, (r2_hidden('#skF_4', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_20773, c_78])).
% 14.19/5.89  tff(c_20772, plain, (r2_hidden('#skF_3', '#skF_5')), inference(splitRight, [status(thm)], [c_80])).
% 14.19/5.89  tff(c_21661, plain, (![A_775, B_776, C_777]: (r1_tarski(k2_tarski(A_775, B_776), C_777) | ~r2_hidden(B_776, C_777) | ~r2_hidden(A_775, C_777))), inference(cnfTransformation, [status(thm)], [f_72])).
% 14.19/5.89  tff(c_26295, plain, (![A_893, B_894, C_895]: (k4_xboole_0(k2_tarski(A_893, B_894), C_895)=k1_xboole_0 | ~r2_hidden(B_894, C_895) | ~r2_hidden(A_893, C_895))), inference(resolution, [status(thm)], [c_21661, c_12])).
% 14.19/5.89  tff(c_21186, plain, (![A_741, B_742]: (k2_xboole_0(k1_tarski(A_741), k1_tarski(B_742))=k2_tarski(A_741, B_742))), inference(cnfTransformation, [status(thm)], [f_58])).
% 14.19/5.89  tff(c_21792, plain, (![B_780, A_781]: (k2_xboole_0(k1_tarski(B_780), k1_tarski(A_781))=k2_tarski(A_781, B_780))), inference(superposition, [status(thm), theory('equality')], [c_21186, c_2])).
% 14.19/5.89  tff(c_21810, plain, (![B_780, A_781]: (k2_tarski(B_780, A_781)=k2_tarski(A_781, B_780))), inference(superposition, [status(thm), theory('equality')], [c_21792, c_38])).
% 14.19/5.89  tff(c_21016, plain, (k4_xboole_0(k2_tarski('#skF_3', '#skF_4'), '#skF_5')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_20773, c_76])).
% 14.19/5.89  tff(c_21873, plain, (k4_xboole_0(k2_tarski('#skF_4', '#skF_3'), '#skF_5')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_21810, c_21016])).
% 14.19/5.89  tff(c_26339, plain, (~r2_hidden('#skF_3', '#skF_5') | ~r2_hidden('#skF_4', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_26295, c_21873])).
% 14.19/5.89  tff(c_26431, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_20901, c_20772, c_26339])).
% 14.19/5.89  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 14.19/5.89  
% 14.19/5.89  Inference rules
% 14.19/5.89  ----------------------
% 14.19/5.89  #Ref     : 0
% 14.19/5.89  #Sup     : 6232
% 14.19/5.89  #Fact    : 0
% 14.19/5.89  #Define  : 0
% 14.19/5.89  #Split   : 5
% 14.19/5.89  #Chain   : 0
% 14.19/5.89  #Close   : 0
% 14.19/5.89  
% 14.19/5.89  Ordering : KBO
% 14.19/5.89  
% 14.19/5.89  Simplification rules
% 14.19/5.89  ----------------------
% 14.19/5.89  #Subsume      : 740
% 14.19/5.89  #Demod        : 5659
% 14.19/5.89  #Tautology    : 4114
% 14.19/5.89  #SimpNegUnit  : 266
% 14.19/5.89  #BackRed      : 8
% 14.19/5.89  
% 14.19/5.89  #Partial instantiations: 0
% 14.19/5.89  #Strategies tried      : 1
% 14.19/5.89  
% 14.19/5.89  Timing (in seconds)
% 14.19/5.89  ----------------------
% 14.19/5.90  Preprocessing        : 0.52
% 14.19/5.90  Parsing              : 0.27
% 14.19/5.90  CNF conversion       : 0.04
% 14.19/5.90  Main loop            : 4.42
% 14.19/5.90  Inferencing          : 1.23
% 14.19/5.90  Reduction            : 2.10
% 14.19/5.90  Demodulation         : 1.75
% 14.19/5.90  BG Simplification    : 0.13
% 14.19/5.90  Subsumption          : 0.68
% 14.19/5.90  Abstraction          : 0.22
% 14.19/5.90  MUC search           : 0.00
% 14.19/5.90  Cooper               : 0.00
% 14.19/5.90  Total                : 5.01
% 14.19/5.90  Index Insertion      : 0.00
% 14.19/5.90  Index Deletion       : 0.00
% 14.19/5.90  Index Matching       : 0.00
% 14.19/5.90  BG Taut test         : 0.00
%------------------------------------------------------------------------------

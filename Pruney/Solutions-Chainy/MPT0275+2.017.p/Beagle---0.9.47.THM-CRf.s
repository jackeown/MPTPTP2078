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
% DateTime   : Thu Dec  3 09:53:18 EST 2020

% Result     : Theorem 40.48s
% Output     : CNFRefutation 40.61s
% Verified   : 
% Statistics : Number of formulae       :  111 ( 407 expanded)
%              Number of leaves         :   24 ( 143 expanded)
%              Depth                    :   11
%              Number of atoms          :  176 ( 851 expanded)
%              Number of equality atoms :   70 ( 349 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_xboole_0 > #skF_1 > #skF_4 > #skF_7 > #skF_10 > #skF_5 > #skF_6 > #skF_2 > #skF_9 > #skF_8 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(f_57,negated_conjecture,(
    ~ ! [A,B,C] :
        ( k4_xboole_0(k2_tarski(A,B),C) = k1_xboole_0
      <=> ( r2_hidden(A,C)
          & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_zfmisc_1)).

tff(f_48,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

tff(f_39,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

tff(c_46,plain,
    ( r2_hidden('#skF_6','#skF_7')
    | ~ r2_hidden('#skF_9','#skF_10')
    | ~ r2_hidden('#skF_8','#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_98,plain,(
    ~ r2_hidden('#skF_8','#skF_10') ),
    inference(splitLeft,[status(thm)],[c_46])).

tff(c_28,plain,(
    ! [D_15,B_11] : r2_hidden(D_15,k2_tarski(D_15,B_11)) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_26,plain,(
    ! [D_15,A_10] : r2_hidden(D_15,k2_tarski(A_10,D_15)) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_22,plain,(
    ! [A_9] : k4_xboole_0(k1_xboole_0,A_9) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_86,plain,(
    ! [D_30,B_31,A_32] :
      ( ~ r2_hidden(D_30,B_31)
      | ~ r2_hidden(D_30,k4_xboole_0(A_32,B_31)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_90,plain,(
    ! [D_33,A_34] :
      ( ~ r2_hidden(D_33,A_34)
      | ~ r2_hidden(D_33,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_86])).

tff(c_95,plain,(
    ! [D_15] : ~ r2_hidden(D_15,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_26,c_90])).

tff(c_54,plain,
    ( r2_hidden('#skF_5','#skF_7')
    | k4_xboole_0(k2_tarski('#skF_8','#skF_9'),'#skF_10') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_110,plain,(
    k4_xboole_0(k2_tarski('#skF_8','#skF_9'),'#skF_10') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_54])).

tff(c_122,plain,(
    ! [D_39,A_40,B_41] :
      ( r2_hidden(D_39,k4_xboole_0(A_40,B_41))
      | r2_hidden(D_39,B_41)
      | ~ r2_hidden(D_39,A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_131,plain,(
    ! [D_39] :
      ( r2_hidden(D_39,k1_xboole_0)
      | r2_hidden(D_39,'#skF_10')
      | ~ r2_hidden(D_39,k2_tarski('#skF_8','#skF_9')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_110,c_122])).

tff(c_139,plain,(
    ! [D_42] :
      ( r2_hidden(D_42,'#skF_10')
      | ~ r2_hidden(D_42,k2_tarski('#skF_8','#skF_9')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_95,c_131])).

tff(c_147,plain,(
    r2_hidden('#skF_8','#skF_10') ),
    inference(resolution,[status(thm)],[c_28,c_139])).

tff(c_152,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_98,c_147])).

tff(c_154,plain,(
    k4_xboole_0(k2_tarski('#skF_8','#skF_9'),'#skF_10') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_50,plain,
    ( k4_xboole_0(k2_tarski('#skF_5','#skF_6'),'#skF_7') != k1_xboole_0
    | k4_xboole_0(k2_tarski('#skF_8','#skF_9'),'#skF_10') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_172,plain,(
    k4_xboole_0(k2_tarski('#skF_5','#skF_6'),'#skF_7') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_154,c_50])).

tff(c_52,plain,
    ( r2_hidden('#skF_6','#skF_7')
    | k4_xboole_0(k2_tarski('#skF_8','#skF_9'),'#skF_10') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_155,plain,(
    k4_xboole_0(k2_tarski('#skF_8','#skF_9'),'#skF_10') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_156,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_154,c_155])).

tff(c_157,plain,(
    r2_hidden('#skF_6','#skF_7') ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_153,plain,(
    r2_hidden('#skF_5','#skF_7') ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_206,plain,(
    ! [A_55,B_56,C_57] :
      ( r2_hidden('#skF_1'(A_55,B_56,C_57),A_55)
      | r2_hidden('#skF_2'(A_55,B_56,C_57),C_57)
      | k4_xboole_0(A_55,B_56) = C_57 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_6,plain,(
    ! [D_6,A_1,B_2] :
      ( r2_hidden(D_6,A_1)
      | ~ r2_hidden(D_6,k4_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_3954,plain,(
    ! [A_201,B_202,A_203,B_204] :
      ( r2_hidden('#skF_2'(A_201,B_202,k4_xboole_0(A_203,B_204)),A_203)
      | r2_hidden('#skF_1'(A_201,B_202,k4_xboole_0(A_203,B_204)),A_201)
      | k4_xboole_0(A_203,B_204) = k4_xboole_0(A_201,B_202) ) ),
    inference(resolution,[status(thm)],[c_206,c_6])).

tff(c_4095,plain,(
    ! [A_201,B_202,A_9] :
      ( r2_hidden('#skF_2'(A_201,B_202,k4_xboole_0(k1_xboole_0,A_9)),k1_xboole_0)
      | r2_hidden('#skF_1'(A_201,B_202,k1_xboole_0),A_201)
      | k4_xboole_0(k1_xboole_0,A_9) = k4_xboole_0(A_201,B_202) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_3954])).

tff(c_4141,plain,(
    ! [A_201,B_202] :
      ( r2_hidden('#skF_2'(A_201,B_202,k1_xboole_0),k1_xboole_0)
      | r2_hidden('#skF_1'(A_201,B_202,k1_xboole_0),A_201)
      | k4_xboole_0(A_201,B_202) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_22,c_4095])).

tff(c_4143,plain,(
    ! [A_205,B_206] :
      ( r2_hidden('#skF_1'(A_205,B_206,k1_xboole_0),A_205)
      | k4_xboole_0(A_205,B_206) = k1_xboole_0 ) ),
    inference(negUnitSimplification,[status(thm)],[c_95,c_4141])).

tff(c_24,plain,(
    ! [D_15,B_11,A_10] :
      ( D_15 = B_11
      | D_15 = A_10
      | ~ r2_hidden(D_15,k2_tarski(A_10,B_11)) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_13799,plain,(
    ! [A_356,B_357,B_358] :
      ( '#skF_1'(k2_tarski(A_356,B_357),B_358,k1_xboole_0) = B_357
      | '#skF_1'(k2_tarski(A_356,B_357),B_358,k1_xboole_0) = A_356
      | k4_xboole_0(k2_tarski(A_356,B_357),B_358) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_4143,c_24])).

tff(c_14125,plain,
    ( '#skF_1'(k2_tarski('#skF_5','#skF_6'),'#skF_7',k1_xboole_0) = '#skF_6'
    | '#skF_1'(k2_tarski('#skF_5','#skF_6'),'#skF_7',k1_xboole_0) = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_13799,c_172])).

tff(c_14130,plain,(
    '#skF_1'(k2_tarski('#skF_5','#skF_6'),'#skF_7',k1_xboole_0) = '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_14125])).

tff(c_16,plain,(
    ! [A_1,B_2,C_3] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2,C_3),B_2)
      | r2_hidden('#skF_2'(A_1,B_2,C_3),C_3)
      | k4_xboole_0(A_1,B_2) = C_3 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_14143,plain,
    ( ~ r2_hidden('#skF_5','#skF_7')
    | r2_hidden('#skF_2'(k2_tarski('#skF_5','#skF_6'),'#skF_7',k1_xboole_0),k1_xboole_0)
    | k4_xboole_0(k2_tarski('#skF_5','#skF_6'),'#skF_7') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_14130,c_16])).

tff(c_14161,plain,
    ( r2_hidden('#skF_2'(k2_tarski('#skF_5','#skF_6'),'#skF_7',k1_xboole_0),k1_xboole_0)
    | k4_xboole_0(k2_tarski('#skF_5','#skF_6'),'#skF_7') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_153,c_14143])).

tff(c_14163,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_172,c_95,c_14161])).

tff(c_14164,plain,(
    '#skF_1'(k2_tarski('#skF_5','#skF_6'),'#skF_7',k1_xboole_0) = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_14125])).

tff(c_14178,plain,
    ( ~ r2_hidden('#skF_6','#skF_7')
    | r2_hidden('#skF_2'(k2_tarski('#skF_5','#skF_6'),'#skF_7',k1_xboole_0),k1_xboole_0)
    | k4_xboole_0(k2_tarski('#skF_5','#skF_6'),'#skF_7') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_14164,c_16])).

tff(c_14196,plain,
    ( r2_hidden('#skF_2'(k2_tarski('#skF_5','#skF_6'),'#skF_7',k1_xboole_0),k1_xboole_0)
    | k4_xboole_0(k2_tarski('#skF_5','#skF_6'),'#skF_7') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_157,c_14178])).

tff(c_14198,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_172,c_95,c_14196])).

tff(c_14200,plain,(
    r2_hidden('#skF_8','#skF_10') ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_14199,plain,
    ( ~ r2_hidden('#skF_9','#skF_10')
    | r2_hidden('#skF_6','#skF_7') ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_14201,plain,(
    ~ r2_hidden('#skF_9','#skF_10') ),
    inference(splitLeft,[status(thm)],[c_14199])).

tff(c_14202,plain,(
    k4_xboole_0(k2_tarski('#skF_8','#skF_9'),'#skF_10') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_54])).

tff(c_14227,plain,(
    ! [D_362,A_363,B_364] :
      ( r2_hidden(D_362,k4_xboole_0(A_363,B_364))
      | r2_hidden(D_362,B_364)
      | ~ r2_hidden(D_362,A_363) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_14236,plain,(
    ! [D_362] :
      ( r2_hidden(D_362,k1_xboole_0)
      | r2_hidden(D_362,'#skF_10')
      | ~ r2_hidden(D_362,k2_tarski('#skF_8','#skF_9')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14202,c_14227])).

tff(c_14244,plain,(
    ! [D_365] :
      ( r2_hidden(D_365,'#skF_10')
      | ~ r2_hidden(D_365,k2_tarski('#skF_8','#skF_9')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_95,c_14236])).

tff(c_14248,plain,(
    r2_hidden('#skF_9','#skF_10') ),
    inference(resolution,[status(thm)],[c_26,c_14244])).

tff(c_14256,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_14201,c_14248])).

tff(c_14258,plain,(
    k4_xboole_0(k2_tarski('#skF_8','#skF_9'),'#skF_10') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_14288,plain,(
    k4_xboole_0(k2_tarski('#skF_5','#skF_6'),'#skF_7') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_14258,c_50])).

tff(c_14259,plain,(
    r2_hidden('#skF_6','#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_14258,c_52])).

tff(c_14257,plain,(
    r2_hidden('#skF_5','#skF_7') ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_14301,plain,(
    ! [A_378,B_379,C_380] :
      ( r2_hidden('#skF_1'(A_378,B_379,C_380),A_378)
      | r2_hidden('#skF_2'(A_378,B_379,C_380),C_380)
      | k4_xboole_0(A_378,B_379) = C_380 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_19407,plain,(
    ! [A_554,B_555,A_556,B_557] :
      ( r2_hidden('#skF_2'(A_554,B_555,k4_xboole_0(A_556,B_557)),A_556)
      | r2_hidden('#skF_1'(A_554,B_555,k4_xboole_0(A_556,B_557)),A_554)
      | k4_xboole_0(A_556,B_557) = k4_xboole_0(A_554,B_555) ) ),
    inference(resolution,[status(thm)],[c_14301,c_6])).

tff(c_19576,plain,(
    ! [A_554,B_555,A_9] :
      ( r2_hidden('#skF_2'(A_554,B_555,k4_xboole_0(k1_xboole_0,A_9)),k1_xboole_0)
      | r2_hidden('#skF_1'(A_554,B_555,k1_xboole_0),A_554)
      | k4_xboole_0(k1_xboole_0,A_9) = k4_xboole_0(A_554,B_555) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_19407])).

tff(c_19632,plain,(
    ! [A_554,B_555] :
      ( r2_hidden('#skF_2'(A_554,B_555,k1_xboole_0),k1_xboole_0)
      | r2_hidden('#skF_1'(A_554,B_555,k1_xboole_0),A_554)
      | k4_xboole_0(A_554,B_555) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_22,c_19576])).

tff(c_19634,plain,(
    ! [A_558,B_559] :
      ( r2_hidden('#skF_1'(A_558,B_559,k1_xboole_0),A_558)
      | k4_xboole_0(A_558,B_559) = k1_xboole_0 ) ),
    inference(negUnitSimplification,[status(thm)],[c_95,c_19632])).

tff(c_32926,plain,(
    ! [A_761,B_762,B_763] :
      ( '#skF_1'(k2_tarski(A_761,B_762),B_763,k1_xboole_0) = B_762
      | '#skF_1'(k2_tarski(A_761,B_762),B_763,k1_xboole_0) = A_761
      | k4_xboole_0(k2_tarski(A_761,B_762),B_763) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_19634,c_24])).

tff(c_33338,plain,
    ( '#skF_1'(k2_tarski('#skF_5','#skF_6'),'#skF_7',k1_xboole_0) = '#skF_6'
    | '#skF_1'(k2_tarski('#skF_5','#skF_6'),'#skF_7',k1_xboole_0) = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_32926,c_14288])).

tff(c_33343,plain,(
    '#skF_1'(k2_tarski('#skF_5','#skF_6'),'#skF_7',k1_xboole_0) = '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_33338])).

tff(c_33362,plain,
    ( ~ r2_hidden('#skF_5','#skF_7')
    | r2_hidden('#skF_2'(k2_tarski('#skF_5','#skF_6'),'#skF_7',k1_xboole_0),k1_xboole_0)
    | k4_xboole_0(k2_tarski('#skF_5','#skF_6'),'#skF_7') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_33343,c_16])).

tff(c_33379,plain,
    ( r2_hidden('#skF_2'(k2_tarski('#skF_5','#skF_6'),'#skF_7',k1_xboole_0),k1_xboole_0)
    | k4_xboole_0(k2_tarski('#skF_5','#skF_6'),'#skF_7') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14257,c_33362])).

tff(c_33381,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_14288,c_95,c_33379])).

tff(c_33382,plain,(
    '#skF_1'(k2_tarski('#skF_5','#skF_6'),'#skF_7',k1_xboole_0) = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_33338])).

tff(c_33402,plain,
    ( ~ r2_hidden('#skF_6','#skF_7')
    | r2_hidden('#skF_2'(k2_tarski('#skF_5','#skF_6'),'#skF_7',k1_xboole_0),k1_xboole_0)
    | k4_xboole_0(k2_tarski('#skF_5','#skF_6'),'#skF_7') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_33382,c_16])).

tff(c_33419,plain,
    ( r2_hidden('#skF_2'(k2_tarski('#skF_5','#skF_6'),'#skF_7',k1_xboole_0),k1_xboole_0)
    | k4_xboole_0(k2_tarski('#skF_5','#skF_6'),'#skF_7') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14259,c_33402])).

tff(c_33421,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_14288,c_95,c_33419])).

tff(c_33423,plain,(
    r2_hidden('#skF_9','#skF_10') ),
    inference(splitRight,[status(thm)],[c_14199])).

tff(c_44,plain,
    ( k4_xboole_0(k2_tarski('#skF_5','#skF_6'),'#skF_7') != k1_xboole_0
    | ~ r2_hidden('#skF_9','#skF_10')
    | ~ r2_hidden('#skF_8','#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_33481,plain,(
    k4_xboole_0(k2_tarski('#skF_5','#skF_6'),'#skF_7') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14200,c_33423,c_44])).

tff(c_33422,plain,(
    r2_hidden('#skF_6','#skF_7') ),
    inference(splitRight,[status(thm)],[c_14199])).

tff(c_48,plain,
    ( r2_hidden('#skF_5','#skF_7')
    | ~ r2_hidden('#skF_9','#skF_10')
    | ~ r2_hidden('#skF_8','#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_33448,plain,(
    r2_hidden('#skF_5','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14200,c_33423,c_48])).

tff(c_33532,plain,(
    ! [A_788,B_789,C_790] :
      ( r2_hidden('#skF_1'(A_788,B_789,C_790),A_788)
      | r2_hidden('#skF_2'(A_788,B_789,C_790),C_790)
      | k4_xboole_0(A_788,B_789) = C_790 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_45208,plain,(
    ! [A_1050,B_1051,B_1052,C_1053] :
      ( '#skF_1'(k2_tarski(A_1050,B_1051),B_1052,C_1053) = B_1051
      | '#skF_1'(k2_tarski(A_1050,B_1051),B_1052,C_1053) = A_1050
      | r2_hidden('#skF_2'(k2_tarski(A_1050,B_1051),B_1052,C_1053),C_1053)
      | k4_xboole_0(k2_tarski(A_1050,B_1051),B_1052) = C_1053 ) ),
    inference(resolution,[status(thm)],[c_33532,c_24])).

tff(c_165334,plain,(
    ! [A_2148,B_2149,B_2150] :
      ( '#skF_1'(k2_tarski(A_2148,B_2149),B_2150,k1_xboole_0) = B_2149
      | '#skF_1'(k2_tarski(A_2148,B_2149),B_2150,k1_xboole_0) = A_2148
      | k4_xboole_0(k2_tarski(A_2148,B_2149),B_2150) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_45208,c_95])).

tff(c_166697,plain,
    ( '#skF_1'(k2_tarski('#skF_5','#skF_6'),'#skF_7',k1_xboole_0) = '#skF_6'
    | '#skF_1'(k2_tarski('#skF_5','#skF_6'),'#skF_7',k1_xboole_0) = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_165334,c_33481])).

tff(c_166703,plain,(
    '#skF_1'(k2_tarski('#skF_5','#skF_6'),'#skF_7',k1_xboole_0) = '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_166697])).

tff(c_166731,plain,
    ( ~ r2_hidden('#skF_5','#skF_7')
    | r2_hidden('#skF_2'(k2_tarski('#skF_5','#skF_6'),'#skF_7',k1_xboole_0),k1_xboole_0)
    | k4_xboole_0(k2_tarski('#skF_5','#skF_6'),'#skF_7') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_166703,c_16])).

tff(c_166749,plain,
    ( r2_hidden('#skF_2'(k2_tarski('#skF_5','#skF_6'),'#skF_7',k1_xboole_0),k1_xboole_0)
    | k4_xboole_0(k2_tarski('#skF_5','#skF_6'),'#skF_7') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_33448,c_166731])).

tff(c_166751,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_33481,c_95,c_166749])).

tff(c_166752,plain,(
    '#skF_1'(k2_tarski('#skF_5','#skF_6'),'#skF_7',k1_xboole_0) = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_166697])).

tff(c_166781,plain,
    ( ~ r2_hidden('#skF_6','#skF_7')
    | r2_hidden('#skF_2'(k2_tarski('#skF_5','#skF_6'),'#skF_7',k1_xboole_0),k1_xboole_0)
    | k4_xboole_0(k2_tarski('#skF_5','#skF_6'),'#skF_7') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_166752,c_16])).

tff(c_166799,plain,
    ( r2_hidden('#skF_2'(k2_tarski('#skF_5','#skF_6'),'#skF_7',k1_xboole_0),k1_xboole_0)
    | k4_xboole_0(k2_tarski('#skF_5','#skF_6'),'#skF_7') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_33422,c_166781])).

tff(c_166801,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_33481,c_95,c_166799])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:37:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 40.48/30.44  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 40.48/30.45  
% 40.48/30.45  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 40.48/30.45  %$ r2_hidden > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_xboole_0 > #skF_1 > #skF_4 > #skF_7 > #skF_10 > #skF_5 > #skF_6 > #skF_2 > #skF_9 > #skF_8 > #skF_3
% 40.48/30.45  
% 40.48/30.45  %Foreground sorts:
% 40.48/30.45  
% 40.48/30.45  
% 40.48/30.45  %Background operators:
% 40.48/30.45  
% 40.48/30.45  
% 40.48/30.45  %Foreground operators:
% 40.48/30.45  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 40.48/30.45  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 40.48/30.45  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 40.48/30.45  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 40.48/30.45  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 40.48/30.45  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 40.48/30.45  tff('#skF_7', type, '#skF_7': $i).
% 40.48/30.45  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 40.48/30.45  tff('#skF_10', type, '#skF_10': $i).
% 40.48/30.45  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 40.48/30.45  tff('#skF_5', type, '#skF_5': $i).
% 40.48/30.45  tff('#skF_6', type, '#skF_6': $i).
% 40.48/30.45  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 40.48/30.45  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 40.48/30.45  tff('#skF_9', type, '#skF_9': $i).
% 40.48/30.45  tff('#skF_8', type, '#skF_8': $i).
% 40.48/30.45  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 40.48/30.45  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 40.48/30.45  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 40.48/30.45  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 40.48/30.45  
% 40.61/30.47  tff(f_57, negated_conjecture, ~(![A, B, C]: ((k4_xboole_0(k2_tarski(A, B), C) = k1_xboole_0) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_zfmisc_1)).
% 40.61/30.47  tff(f_48, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tarski)).
% 40.61/30.47  tff(f_39, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_boole)).
% 40.61/30.47  tff(f_35, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 40.61/30.47  tff(c_46, plain, (r2_hidden('#skF_6', '#skF_7') | ~r2_hidden('#skF_9', '#skF_10') | ~r2_hidden('#skF_8', '#skF_10')), inference(cnfTransformation, [status(thm)], [f_57])).
% 40.61/30.47  tff(c_98, plain, (~r2_hidden('#skF_8', '#skF_10')), inference(splitLeft, [status(thm)], [c_46])).
% 40.61/30.47  tff(c_28, plain, (![D_15, B_11]: (r2_hidden(D_15, k2_tarski(D_15, B_11)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 40.61/30.47  tff(c_26, plain, (![D_15, A_10]: (r2_hidden(D_15, k2_tarski(A_10, D_15)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 40.61/30.47  tff(c_22, plain, (![A_9]: (k4_xboole_0(k1_xboole_0, A_9)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 40.61/30.47  tff(c_86, plain, (![D_30, B_31, A_32]: (~r2_hidden(D_30, B_31) | ~r2_hidden(D_30, k4_xboole_0(A_32, B_31)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 40.61/30.47  tff(c_90, plain, (![D_33, A_34]: (~r2_hidden(D_33, A_34) | ~r2_hidden(D_33, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_22, c_86])).
% 40.61/30.47  tff(c_95, plain, (![D_15]: (~r2_hidden(D_15, k1_xboole_0))), inference(resolution, [status(thm)], [c_26, c_90])).
% 40.61/30.47  tff(c_54, plain, (r2_hidden('#skF_5', '#skF_7') | k4_xboole_0(k2_tarski('#skF_8', '#skF_9'), '#skF_10')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_57])).
% 40.61/30.47  tff(c_110, plain, (k4_xboole_0(k2_tarski('#skF_8', '#skF_9'), '#skF_10')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_54])).
% 40.61/30.47  tff(c_122, plain, (![D_39, A_40, B_41]: (r2_hidden(D_39, k4_xboole_0(A_40, B_41)) | r2_hidden(D_39, B_41) | ~r2_hidden(D_39, A_40))), inference(cnfTransformation, [status(thm)], [f_35])).
% 40.61/30.47  tff(c_131, plain, (![D_39]: (r2_hidden(D_39, k1_xboole_0) | r2_hidden(D_39, '#skF_10') | ~r2_hidden(D_39, k2_tarski('#skF_8', '#skF_9')))), inference(superposition, [status(thm), theory('equality')], [c_110, c_122])).
% 40.61/30.47  tff(c_139, plain, (![D_42]: (r2_hidden(D_42, '#skF_10') | ~r2_hidden(D_42, k2_tarski('#skF_8', '#skF_9')))), inference(negUnitSimplification, [status(thm)], [c_95, c_131])).
% 40.61/30.47  tff(c_147, plain, (r2_hidden('#skF_8', '#skF_10')), inference(resolution, [status(thm)], [c_28, c_139])).
% 40.61/30.47  tff(c_152, plain, $false, inference(negUnitSimplification, [status(thm)], [c_98, c_147])).
% 40.61/30.47  tff(c_154, plain, (k4_xboole_0(k2_tarski('#skF_8', '#skF_9'), '#skF_10')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_54])).
% 40.61/30.47  tff(c_50, plain, (k4_xboole_0(k2_tarski('#skF_5', '#skF_6'), '#skF_7')!=k1_xboole_0 | k4_xboole_0(k2_tarski('#skF_8', '#skF_9'), '#skF_10')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_57])).
% 40.61/30.47  tff(c_172, plain, (k4_xboole_0(k2_tarski('#skF_5', '#skF_6'), '#skF_7')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_154, c_50])).
% 40.61/30.47  tff(c_52, plain, (r2_hidden('#skF_6', '#skF_7') | k4_xboole_0(k2_tarski('#skF_8', '#skF_9'), '#skF_10')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_57])).
% 40.61/30.47  tff(c_155, plain, (k4_xboole_0(k2_tarski('#skF_8', '#skF_9'), '#skF_10')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_52])).
% 40.61/30.47  tff(c_156, plain, $false, inference(negUnitSimplification, [status(thm)], [c_154, c_155])).
% 40.61/30.47  tff(c_157, plain, (r2_hidden('#skF_6', '#skF_7')), inference(splitRight, [status(thm)], [c_52])).
% 40.61/30.47  tff(c_153, plain, (r2_hidden('#skF_5', '#skF_7')), inference(splitRight, [status(thm)], [c_54])).
% 40.61/30.47  tff(c_206, plain, (![A_55, B_56, C_57]: (r2_hidden('#skF_1'(A_55, B_56, C_57), A_55) | r2_hidden('#skF_2'(A_55, B_56, C_57), C_57) | k4_xboole_0(A_55, B_56)=C_57)), inference(cnfTransformation, [status(thm)], [f_35])).
% 40.61/30.47  tff(c_6, plain, (![D_6, A_1, B_2]: (r2_hidden(D_6, A_1) | ~r2_hidden(D_6, k4_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 40.61/30.47  tff(c_3954, plain, (![A_201, B_202, A_203, B_204]: (r2_hidden('#skF_2'(A_201, B_202, k4_xboole_0(A_203, B_204)), A_203) | r2_hidden('#skF_1'(A_201, B_202, k4_xboole_0(A_203, B_204)), A_201) | k4_xboole_0(A_203, B_204)=k4_xboole_0(A_201, B_202))), inference(resolution, [status(thm)], [c_206, c_6])).
% 40.61/30.47  tff(c_4095, plain, (![A_201, B_202, A_9]: (r2_hidden('#skF_2'(A_201, B_202, k4_xboole_0(k1_xboole_0, A_9)), k1_xboole_0) | r2_hidden('#skF_1'(A_201, B_202, k1_xboole_0), A_201) | k4_xboole_0(k1_xboole_0, A_9)=k4_xboole_0(A_201, B_202))), inference(superposition, [status(thm), theory('equality')], [c_22, c_3954])).
% 40.61/30.47  tff(c_4141, plain, (![A_201, B_202]: (r2_hidden('#skF_2'(A_201, B_202, k1_xboole_0), k1_xboole_0) | r2_hidden('#skF_1'(A_201, B_202, k1_xboole_0), A_201) | k4_xboole_0(A_201, B_202)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_22, c_22, c_4095])).
% 40.61/30.47  tff(c_4143, plain, (![A_205, B_206]: (r2_hidden('#skF_1'(A_205, B_206, k1_xboole_0), A_205) | k4_xboole_0(A_205, B_206)=k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_95, c_4141])).
% 40.61/30.47  tff(c_24, plain, (![D_15, B_11, A_10]: (D_15=B_11 | D_15=A_10 | ~r2_hidden(D_15, k2_tarski(A_10, B_11)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 40.61/30.47  tff(c_13799, plain, (![A_356, B_357, B_358]: ('#skF_1'(k2_tarski(A_356, B_357), B_358, k1_xboole_0)=B_357 | '#skF_1'(k2_tarski(A_356, B_357), B_358, k1_xboole_0)=A_356 | k4_xboole_0(k2_tarski(A_356, B_357), B_358)=k1_xboole_0)), inference(resolution, [status(thm)], [c_4143, c_24])).
% 40.61/30.47  tff(c_14125, plain, ('#skF_1'(k2_tarski('#skF_5', '#skF_6'), '#skF_7', k1_xboole_0)='#skF_6' | '#skF_1'(k2_tarski('#skF_5', '#skF_6'), '#skF_7', k1_xboole_0)='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_13799, c_172])).
% 40.61/30.47  tff(c_14130, plain, ('#skF_1'(k2_tarski('#skF_5', '#skF_6'), '#skF_7', k1_xboole_0)='#skF_5'), inference(splitLeft, [status(thm)], [c_14125])).
% 40.61/30.47  tff(c_16, plain, (![A_1, B_2, C_3]: (~r2_hidden('#skF_1'(A_1, B_2, C_3), B_2) | r2_hidden('#skF_2'(A_1, B_2, C_3), C_3) | k4_xboole_0(A_1, B_2)=C_3)), inference(cnfTransformation, [status(thm)], [f_35])).
% 40.61/30.47  tff(c_14143, plain, (~r2_hidden('#skF_5', '#skF_7') | r2_hidden('#skF_2'(k2_tarski('#skF_5', '#skF_6'), '#skF_7', k1_xboole_0), k1_xboole_0) | k4_xboole_0(k2_tarski('#skF_5', '#skF_6'), '#skF_7')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_14130, c_16])).
% 40.61/30.47  tff(c_14161, plain, (r2_hidden('#skF_2'(k2_tarski('#skF_5', '#skF_6'), '#skF_7', k1_xboole_0), k1_xboole_0) | k4_xboole_0(k2_tarski('#skF_5', '#skF_6'), '#skF_7')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_153, c_14143])).
% 40.61/30.47  tff(c_14163, plain, $false, inference(negUnitSimplification, [status(thm)], [c_172, c_95, c_14161])).
% 40.61/30.47  tff(c_14164, plain, ('#skF_1'(k2_tarski('#skF_5', '#skF_6'), '#skF_7', k1_xboole_0)='#skF_6'), inference(splitRight, [status(thm)], [c_14125])).
% 40.61/30.47  tff(c_14178, plain, (~r2_hidden('#skF_6', '#skF_7') | r2_hidden('#skF_2'(k2_tarski('#skF_5', '#skF_6'), '#skF_7', k1_xboole_0), k1_xboole_0) | k4_xboole_0(k2_tarski('#skF_5', '#skF_6'), '#skF_7')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_14164, c_16])).
% 40.61/30.47  tff(c_14196, plain, (r2_hidden('#skF_2'(k2_tarski('#skF_5', '#skF_6'), '#skF_7', k1_xboole_0), k1_xboole_0) | k4_xboole_0(k2_tarski('#skF_5', '#skF_6'), '#skF_7')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_157, c_14178])).
% 40.61/30.47  tff(c_14198, plain, $false, inference(negUnitSimplification, [status(thm)], [c_172, c_95, c_14196])).
% 40.61/30.47  tff(c_14200, plain, (r2_hidden('#skF_8', '#skF_10')), inference(splitRight, [status(thm)], [c_46])).
% 40.61/30.47  tff(c_14199, plain, (~r2_hidden('#skF_9', '#skF_10') | r2_hidden('#skF_6', '#skF_7')), inference(splitRight, [status(thm)], [c_46])).
% 40.61/30.47  tff(c_14201, plain, (~r2_hidden('#skF_9', '#skF_10')), inference(splitLeft, [status(thm)], [c_14199])).
% 40.61/30.47  tff(c_14202, plain, (k4_xboole_0(k2_tarski('#skF_8', '#skF_9'), '#skF_10')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_54])).
% 40.61/30.47  tff(c_14227, plain, (![D_362, A_363, B_364]: (r2_hidden(D_362, k4_xboole_0(A_363, B_364)) | r2_hidden(D_362, B_364) | ~r2_hidden(D_362, A_363))), inference(cnfTransformation, [status(thm)], [f_35])).
% 40.61/30.47  tff(c_14236, plain, (![D_362]: (r2_hidden(D_362, k1_xboole_0) | r2_hidden(D_362, '#skF_10') | ~r2_hidden(D_362, k2_tarski('#skF_8', '#skF_9')))), inference(superposition, [status(thm), theory('equality')], [c_14202, c_14227])).
% 40.61/30.47  tff(c_14244, plain, (![D_365]: (r2_hidden(D_365, '#skF_10') | ~r2_hidden(D_365, k2_tarski('#skF_8', '#skF_9')))), inference(negUnitSimplification, [status(thm)], [c_95, c_14236])).
% 40.61/30.47  tff(c_14248, plain, (r2_hidden('#skF_9', '#skF_10')), inference(resolution, [status(thm)], [c_26, c_14244])).
% 40.61/30.47  tff(c_14256, plain, $false, inference(negUnitSimplification, [status(thm)], [c_14201, c_14248])).
% 40.61/30.47  tff(c_14258, plain, (k4_xboole_0(k2_tarski('#skF_8', '#skF_9'), '#skF_10')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_54])).
% 40.61/30.47  tff(c_14288, plain, (k4_xboole_0(k2_tarski('#skF_5', '#skF_6'), '#skF_7')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_14258, c_50])).
% 40.61/30.47  tff(c_14259, plain, (r2_hidden('#skF_6', '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_14258, c_52])).
% 40.61/30.47  tff(c_14257, plain, (r2_hidden('#skF_5', '#skF_7')), inference(splitRight, [status(thm)], [c_54])).
% 40.61/30.47  tff(c_14301, plain, (![A_378, B_379, C_380]: (r2_hidden('#skF_1'(A_378, B_379, C_380), A_378) | r2_hidden('#skF_2'(A_378, B_379, C_380), C_380) | k4_xboole_0(A_378, B_379)=C_380)), inference(cnfTransformation, [status(thm)], [f_35])).
% 40.61/30.47  tff(c_19407, plain, (![A_554, B_555, A_556, B_557]: (r2_hidden('#skF_2'(A_554, B_555, k4_xboole_0(A_556, B_557)), A_556) | r2_hidden('#skF_1'(A_554, B_555, k4_xboole_0(A_556, B_557)), A_554) | k4_xboole_0(A_556, B_557)=k4_xboole_0(A_554, B_555))), inference(resolution, [status(thm)], [c_14301, c_6])).
% 40.61/30.47  tff(c_19576, plain, (![A_554, B_555, A_9]: (r2_hidden('#skF_2'(A_554, B_555, k4_xboole_0(k1_xboole_0, A_9)), k1_xboole_0) | r2_hidden('#skF_1'(A_554, B_555, k1_xboole_0), A_554) | k4_xboole_0(k1_xboole_0, A_9)=k4_xboole_0(A_554, B_555))), inference(superposition, [status(thm), theory('equality')], [c_22, c_19407])).
% 40.61/30.47  tff(c_19632, plain, (![A_554, B_555]: (r2_hidden('#skF_2'(A_554, B_555, k1_xboole_0), k1_xboole_0) | r2_hidden('#skF_1'(A_554, B_555, k1_xboole_0), A_554) | k4_xboole_0(A_554, B_555)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_22, c_22, c_19576])).
% 40.61/30.47  tff(c_19634, plain, (![A_558, B_559]: (r2_hidden('#skF_1'(A_558, B_559, k1_xboole_0), A_558) | k4_xboole_0(A_558, B_559)=k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_95, c_19632])).
% 40.61/30.47  tff(c_32926, plain, (![A_761, B_762, B_763]: ('#skF_1'(k2_tarski(A_761, B_762), B_763, k1_xboole_0)=B_762 | '#skF_1'(k2_tarski(A_761, B_762), B_763, k1_xboole_0)=A_761 | k4_xboole_0(k2_tarski(A_761, B_762), B_763)=k1_xboole_0)), inference(resolution, [status(thm)], [c_19634, c_24])).
% 40.61/30.47  tff(c_33338, plain, ('#skF_1'(k2_tarski('#skF_5', '#skF_6'), '#skF_7', k1_xboole_0)='#skF_6' | '#skF_1'(k2_tarski('#skF_5', '#skF_6'), '#skF_7', k1_xboole_0)='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_32926, c_14288])).
% 40.61/30.47  tff(c_33343, plain, ('#skF_1'(k2_tarski('#skF_5', '#skF_6'), '#skF_7', k1_xboole_0)='#skF_5'), inference(splitLeft, [status(thm)], [c_33338])).
% 40.61/30.47  tff(c_33362, plain, (~r2_hidden('#skF_5', '#skF_7') | r2_hidden('#skF_2'(k2_tarski('#skF_5', '#skF_6'), '#skF_7', k1_xboole_0), k1_xboole_0) | k4_xboole_0(k2_tarski('#skF_5', '#skF_6'), '#skF_7')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_33343, c_16])).
% 40.61/30.47  tff(c_33379, plain, (r2_hidden('#skF_2'(k2_tarski('#skF_5', '#skF_6'), '#skF_7', k1_xboole_0), k1_xboole_0) | k4_xboole_0(k2_tarski('#skF_5', '#skF_6'), '#skF_7')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_14257, c_33362])).
% 40.61/30.47  tff(c_33381, plain, $false, inference(negUnitSimplification, [status(thm)], [c_14288, c_95, c_33379])).
% 40.61/30.47  tff(c_33382, plain, ('#skF_1'(k2_tarski('#skF_5', '#skF_6'), '#skF_7', k1_xboole_0)='#skF_6'), inference(splitRight, [status(thm)], [c_33338])).
% 40.61/30.47  tff(c_33402, plain, (~r2_hidden('#skF_6', '#skF_7') | r2_hidden('#skF_2'(k2_tarski('#skF_5', '#skF_6'), '#skF_7', k1_xboole_0), k1_xboole_0) | k4_xboole_0(k2_tarski('#skF_5', '#skF_6'), '#skF_7')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_33382, c_16])).
% 40.61/30.47  tff(c_33419, plain, (r2_hidden('#skF_2'(k2_tarski('#skF_5', '#skF_6'), '#skF_7', k1_xboole_0), k1_xboole_0) | k4_xboole_0(k2_tarski('#skF_5', '#skF_6'), '#skF_7')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_14259, c_33402])).
% 40.61/30.47  tff(c_33421, plain, $false, inference(negUnitSimplification, [status(thm)], [c_14288, c_95, c_33419])).
% 40.61/30.47  tff(c_33423, plain, (r2_hidden('#skF_9', '#skF_10')), inference(splitRight, [status(thm)], [c_14199])).
% 40.61/30.47  tff(c_44, plain, (k4_xboole_0(k2_tarski('#skF_5', '#skF_6'), '#skF_7')!=k1_xboole_0 | ~r2_hidden('#skF_9', '#skF_10') | ~r2_hidden('#skF_8', '#skF_10')), inference(cnfTransformation, [status(thm)], [f_57])).
% 40.61/30.47  tff(c_33481, plain, (k4_xboole_0(k2_tarski('#skF_5', '#skF_6'), '#skF_7')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_14200, c_33423, c_44])).
% 40.61/30.47  tff(c_33422, plain, (r2_hidden('#skF_6', '#skF_7')), inference(splitRight, [status(thm)], [c_14199])).
% 40.61/30.47  tff(c_48, plain, (r2_hidden('#skF_5', '#skF_7') | ~r2_hidden('#skF_9', '#skF_10') | ~r2_hidden('#skF_8', '#skF_10')), inference(cnfTransformation, [status(thm)], [f_57])).
% 40.61/30.47  tff(c_33448, plain, (r2_hidden('#skF_5', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_14200, c_33423, c_48])).
% 40.61/30.47  tff(c_33532, plain, (![A_788, B_789, C_790]: (r2_hidden('#skF_1'(A_788, B_789, C_790), A_788) | r2_hidden('#skF_2'(A_788, B_789, C_790), C_790) | k4_xboole_0(A_788, B_789)=C_790)), inference(cnfTransformation, [status(thm)], [f_35])).
% 40.61/30.47  tff(c_45208, plain, (![A_1050, B_1051, B_1052, C_1053]: ('#skF_1'(k2_tarski(A_1050, B_1051), B_1052, C_1053)=B_1051 | '#skF_1'(k2_tarski(A_1050, B_1051), B_1052, C_1053)=A_1050 | r2_hidden('#skF_2'(k2_tarski(A_1050, B_1051), B_1052, C_1053), C_1053) | k4_xboole_0(k2_tarski(A_1050, B_1051), B_1052)=C_1053)), inference(resolution, [status(thm)], [c_33532, c_24])).
% 40.61/30.47  tff(c_165334, plain, (![A_2148, B_2149, B_2150]: ('#skF_1'(k2_tarski(A_2148, B_2149), B_2150, k1_xboole_0)=B_2149 | '#skF_1'(k2_tarski(A_2148, B_2149), B_2150, k1_xboole_0)=A_2148 | k4_xboole_0(k2_tarski(A_2148, B_2149), B_2150)=k1_xboole_0)), inference(resolution, [status(thm)], [c_45208, c_95])).
% 40.61/30.47  tff(c_166697, plain, ('#skF_1'(k2_tarski('#skF_5', '#skF_6'), '#skF_7', k1_xboole_0)='#skF_6' | '#skF_1'(k2_tarski('#skF_5', '#skF_6'), '#skF_7', k1_xboole_0)='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_165334, c_33481])).
% 40.61/30.47  tff(c_166703, plain, ('#skF_1'(k2_tarski('#skF_5', '#skF_6'), '#skF_7', k1_xboole_0)='#skF_5'), inference(splitLeft, [status(thm)], [c_166697])).
% 40.61/30.47  tff(c_166731, plain, (~r2_hidden('#skF_5', '#skF_7') | r2_hidden('#skF_2'(k2_tarski('#skF_5', '#skF_6'), '#skF_7', k1_xboole_0), k1_xboole_0) | k4_xboole_0(k2_tarski('#skF_5', '#skF_6'), '#skF_7')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_166703, c_16])).
% 40.61/30.47  tff(c_166749, plain, (r2_hidden('#skF_2'(k2_tarski('#skF_5', '#skF_6'), '#skF_7', k1_xboole_0), k1_xboole_0) | k4_xboole_0(k2_tarski('#skF_5', '#skF_6'), '#skF_7')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_33448, c_166731])).
% 40.61/30.47  tff(c_166751, plain, $false, inference(negUnitSimplification, [status(thm)], [c_33481, c_95, c_166749])).
% 40.61/30.47  tff(c_166752, plain, ('#skF_1'(k2_tarski('#skF_5', '#skF_6'), '#skF_7', k1_xboole_0)='#skF_6'), inference(splitRight, [status(thm)], [c_166697])).
% 40.61/30.47  tff(c_166781, plain, (~r2_hidden('#skF_6', '#skF_7') | r2_hidden('#skF_2'(k2_tarski('#skF_5', '#skF_6'), '#skF_7', k1_xboole_0), k1_xboole_0) | k4_xboole_0(k2_tarski('#skF_5', '#skF_6'), '#skF_7')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_166752, c_16])).
% 40.61/30.47  tff(c_166799, plain, (r2_hidden('#skF_2'(k2_tarski('#skF_5', '#skF_6'), '#skF_7', k1_xboole_0), k1_xboole_0) | k4_xboole_0(k2_tarski('#skF_5', '#skF_6'), '#skF_7')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_33422, c_166781])).
% 40.61/30.47  tff(c_166801, plain, $false, inference(negUnitSimplification, [status(thm)], [c_33481, c_95, c_166799])).
% 40.61/30.47  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 40.61/30.47  
% 40.61/30.47  Inference rules
% 40.61/30.47  ----------------------
% 40.61/30.47  #Ref     : 0
% 40.61/30.47  #Sup     : 42175
% 40.61/30.47  #Fact    : 66
% 40.61/30.47  #Define  : 0
% 40.61/30.47  #Split   : 20
% 40.61/30.47  #Chain   : 0
% 40.61/30.47  #Close   : 0
% 40.61/30.47  
% 40.61/30.47  Ordering : KBO
% 40.61/30.47  
% 40.61/30.47  Simplification rules
% 40.61/30.47  ----------------------
% 40.61/30.47  #Subsume      : 19140
% 40.61/30.47  #Demod        : 44858
% 40.61/30.47  #Tautology    : 10898
% 40.61/30.47  #SimpNegUnit  : 1747
% 40.61/30.47  #BackRed      : 74
% 40.61/30.47  
% 40.61/30.47  #Partial instantiations: 0
% 40.61/30.47  #Strategies tried      : 1
% 40.61/30.47  
% 40.61/30.47  Timing (in seconds)
% 40.61/30.47  ----------------------
% 40.61/30.47  Preprocessing        : 0.31
% 40.61/30.47  Parsing              : 0.16
% 40.61/30.47  CNF conversion       : 0.02
% 40.61/30.47  Main loop            : 29.34
% 40.61/30.47  Inferencing          : 4.27
% 40.61/30.47  Reduction            : 14.83
% 40.61/30.47  Demodulation         : 12.85
% 40.61/30.47  BG Simplification    : 0.42
% 40.61/30.47  Subsumption          : 8.52
% 40.61/30.47  Abstraction          : 1.06
% 40.61/30.47  MUC search           : 0.00
% 40.61/30.47  Cooper               : 0.00
% 40.61/30.47  Total                : 29.70
% 40.61/30.47  Index Insertion      : 0.00
% 40.61/30.47  Index Deletion       : 0.00
% 40.61/30.47  Index Matching       : 0.00
% 40.61/30.47  BG Taut test         : 0.00
%------------------------------------------------------------------------------

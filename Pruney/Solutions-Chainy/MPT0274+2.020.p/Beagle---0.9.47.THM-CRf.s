%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:53:14 EST 2020

% Result     : Theorem 8.84s
% Output     : CNFRefutation 8.84s
% Verified   : 
% Statistics : Number of formulae       :  127 ( 240 expanded)
%              Number of leaves         :   31 (  91 expanded)
%              Depth                    :    7
%              Number of atoms          :  159 ( 390 expanded)
%              Number of equality atoms :   34 (  90 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k3_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

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

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_74,axiom,(
    ! [A,B] : r1_tarski(k1_tarski(A),k2_tarski(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_zfmisc_1)).

tff(f_68,axiom,(
    ! [A,B] : k3_enumset1(A,A,A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_enumset1)).

tff(f_70,axiom,(
    ! [A] : k3_enumset1(A,A,A,A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_enumset1)).

tff(f_80,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(f_66,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_99,negated_conjecture,(
    ~ ! [A,B,C] :
        ( k4_xboole_0(k2_tarski(A,B),C) = k2_tarski(A,B)
      <=> ( ~ r2_hidden(A,C)
          & ~ r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_zfmisc_1)).

tff(f_90,axiom,(
    ! [A,B,C] :
      ~ ( ~ r2_hidden(A,B)
        & ~ r2_hidden(C,B)
        & ~ r1_xboole_0(k2_tarski(A,C),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_zfmisc_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_62,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),k5_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t96_xboole_1)).

tff(f_32,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k5_xboole_0(B,C))
    <=> ~ ( r2_hidden(A,B)
        <=> r2_hidden(A,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_0)).

tff(c_48,plain,(
    ! [A_38,B_39] : r1_tarski(k1_tarski(A_38),k2_tarski(A_38,B_39)) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_14350,plain,(
    ! [A_830,B_831] : k3_enumset1(A_830,A_830,A_830,A_830,B_831) = k2_tarski(A_830,B_831) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_44,plain,(
    ! [A_35] : k3_enumset1(A_35,A_35,A_35,A_35,A_35) = k1_tarski(A_35) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_14366,plain,(
    ! [B_832] : k2_tarski(B_832,B_832) = k1_tarski(B_832) ),
    inference(superposition,[status(thm),theory(equality)],[c_14350,c_44])).

tff(c_54,plain,(
    ! [A_40,C_42,B_41] :
      ( r2_hidden(A_40,C_42)
      | ~ r1_tarski(k2_tarski(A_40,B_41),C_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_14658,plain,(
    ! [B_850,C_851] :
      ( r2_hidden(B_850,C_851)
      | ~ r1_tarski(k1_tarski(B_850),C_851) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14366,c_54])).

tff(c_14686,plain,(
    ! [A_38,B_39] : r2_hidden(A_38,k2_tarski(A_38,B_39)) ),
    inference(resolution,[status(thm)],[c_48,c_14658])).

tff(c_40,plain,(
    ! [B_32,A_31] : k2_tarski(B_32,A_31) = k2_tarski(A_31,B_32) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_105,plain,(
    ! [A_52,B_53] : r1_tarski(k1_tarski(A_52),k2_tarski(A_52,B_53)) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_108,plain,(
    ! [A_31,B_32] : r1_tarski(k1_tarski(A_31),k2_tarski(B_32,A_31)) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_105])).

tff(c_12118,plain,(
    ! [A_685,B_686] : k3_enumset1(A_685,A_685,A_685,A_685,B_686) = k2_tarski(A_685,B_686) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_12134,plain,(
    ! [B_687] : k2_tarski(B_687,B_687) = k1_tarski(B_687) ),
    inference(superposition,[status(thm),theory(equality)],[c_12118,c_44])).

tff(c_52,plain,(
    ! [B_41,C_42,A_40] :
      ( r2_hidden(B_41,C_42)
      | ~ r1_tarski(k2_tarski(A_40,B_41),C_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_12308,plain,(
    ! [B_699,C_700] :
      ( r2_hidden(B_699,C_700)
      | ~ r1_tarski(k1_tarski(B_699),C_700) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12134,c_52])).

tff(c_12335,plain,(
    ! [A_31,B_32] : r2_hidden(A_31,k2_tarski(B_32,A_31)) ),
    inference(resolution,[status(thm)],[c_108,c_12308])).

tff(c_10013,plain,(
    ! [A_549,B_550] : k3_enumset1(A_549,A_549,A_549,A_549,B_550) = k2_tarski(A_549,B_550) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_10029,plain,(
    ! [B_551] : k2_tarski(B_551,B_551) = k1_tarski(B_551) ),
    inference(superposition,[status(thm),theory(equality)],[c_10013,c_44])).

tff(c_10178,plain,(
    ! [B_563,C_564] :
      ( r2_hidden(B_563,C_564)
      | ~ r1_tarski(k1_tarski(B_563),C_564) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10029,c_52])).

tff(c_10206,plain,(
    ! [A_38,B_39] : r2_hidden(A_38,k2_tarski(A_38,B_39)) ),
    inference(resolution,[status(thm)],[c_48,c_10178])).

tff(c_9183,plain,(
    ! [A_480,B_481] : k3_enumset1(A_480,A_480,A_480,A_480,B_481) = k2_tarski(A_480,B_481) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_9199,plain,(
    ! [B_482] : k2_tarski(B_482,B_482) = k1_tarski(B_482) ),
    inference(superposition,[status(thm),theory(equality)],[c_9183,c_44])).

tff(c_9399,plain,(
    ! [B_499,C_500] :
      ( r2_hidden(B_499,C_500)
      | ~ r1_tarski(k1_tarski(B_499),C_500) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_9199,c_54])).

tff(c_9426,plain,(
    ! [A_31,B_32] : r2_hidden(A_31,k2_tarski(B_32,A_31)) ),
    inference(resolution,[status(thm)],[c_108,c_9399])).

tff(c_475,plain,(
    ! [A_103,B_104] : k3_enumset1(A_103,A_103,A_103,A_103,B_104) = k2_tarski(A_103,B_104) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_491,plain,(
    ! [B_105] : k2_tarski(B_105,B_105) = k1_tarski(B_105) ),
    inference(superposition,[status(thm),theory(equality)],[c_475,c_44])).

tff(c_7797,plain,(
    ! [B_392,C_393] :
      ( r2_hidden(B_392,C_393)
      | ~ r1_tarski(k1_tarski(B_392),C_393) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_491,c_54])).

tff(c_7825,plain,(
    ! [A_38,B_39] : r2_hidden(A_38,k2_tarski(A_38,B_39)) ),
    inference(resolution,[status(thm)],[c_48,c_7797])).

tff(c_6346,plain,(
    ! [B_313,C_314] :
      ( r2_hidden(B_313,C_314)
      | ~ r1_tarski(k1_tarski(B_313),C_314) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_491,c_54])).

tff(c_6373,plain,(
    ! [A_31,B_32] : r2_hidden(A_31,k2_tarski(B_32,A_31)) ),
    inference(resolution,[status(thm)],[c_108,c_6346])).

tff(c_62,plain,
    ( ~ r2_hidden('#skF_1','#skF_3')
    | r2_hidden('#skF_5','#skF_6')
    | r2_hidden('#skF_4','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_244,plain,(
    ~ r2_hidden('#skF_1','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_62])).

tff(c_60,plain,
    ( ~ r2_hidden('#skF_2','#skF_3')
    | r2_hidden('#skF_5','#skF_6')
    | r2_hidden('#skF_4','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_139,plain,(
    ~ r2_hidden('#skF_2','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_60])).

tff(c_1352,plain,(
    ! [A_173,C_174,B_175] :
      ( r1_xboole_0(k2_tarski(A_173,C_174),B_175)
      | r2_hidden(C_174,B_175)
      | r2_hidden(A_173,B_175) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_26,plain,(
    ! [A_18,B_19] :
      ( k4_xboole_0(A_18,B_19) = A_18
      | ~ r1_xboole_0(A_18,B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_5869,plain,(
    ! [A_297,C_298,B_299] :
      ( k4_xboole_0(k2_tarski(A_297,C_298),B_299) = k2_tarski(A_297,C_298)
      | r2_hidden(C_298,B_299)
      | r2_hidden(A_297,B_299) ) ),
    inference(resolution,[status(thm)],[c_1352,c_26])).

tff(c_58,plain,
    ( k4_xboole_0(k2_tarski('#skF_1','#skF_2'),'#skF_3') != k2_tarski('#skF_1','#skF_2')
    | r2_hidden('#skF_5','#skF_6')
    | r2_hidden('#skF_4','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_532,plain,(
    k4_xboole_0(k2_tarski('#skF_1','#skF_2'),'#skF_3') != k2_tarski('#skF_1','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_58])).

tff(c_5999,plain,
    ( r2_hidden('#skF_2','#skF_3')
    | r2_hidden('#skF_1','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_5869,c_532])).

tff(c_6076,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_244,c_139,c_5999])).

tff(c_6077,plain,
    ( r2_hidden('#skF_4','#skF_6')
    | r2_hidden('#skF_5','#skF_6') ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_6080,plain,(
    r2_hidden('#skF_5','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_6077])).

tff(c_64,plain,
    ( k4_xboole_0(k2_tarski('#skF_1','#skF_2'),'#skF_3') != k2_tarski('#skF_1','#skF_2')
    | k4_xboole_0(k2_tarski('#skF_4','#skF_5'),'#skF_6') = k2_tarski('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_6081,plain,(
    k4_xboole_0(k2_tarski('#skF_1','#skF_2'),'#skF_3') != k2_tarski('#skF_1','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_64])).

tff(c_6078,plain,(
    k4_xboole_0(k2_tarski('#skF_1','#skF_2'),'#skF_3') = k2_tarski('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_6170,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_6081,c_6078])).

tff(c_6171,plain,(
    k4_xboole_0(k2_tarski('#skF_4','#skF_5'),'#skF_6') = k2_tarski('#skF_4','#skF_5') ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_36,plain,(
    ! [A_27,B_28] : r1_tarski(k4_xboole_0(A_27,B_28),k5_xboole_0(A_27,B_28)) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_6268,plain,(
    r1_tarski(k2_tarski('#skF_4','#skF_5'),k5_xboole_0(k2_tarski('#skF_4','#skF_5'),'#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_6171,c_36])).

tff(c_6523,plain,(
    r2_hidden('#skF_5',k5_xboole_0(k2_tarski('#skF_4','#skF_5'),'#skF_6')) ),
    inference(resolution,[status(thm)],[c_6268,c_52])).

tff(c_7522,plain,(
    ! [A_376,C_377,B_378] :
      ( ~ r2_hidden(A_376,C_377)
      | ~ r2_hidden(A_376,B_378)
      | ~ r2_hidden(A_376,k5_xboole_0(B_378,C_377)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_7540,plain,
    ( ~ r2_hidden('#skF_5','#skF_6')
    | ~ r2_hidden('#skF_5',k2_tarski('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_6523,c_7522])).

tff(c_7560,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6373,c_6080,c_7540])).

tff(c_7561,plain,(
    r2_hidden('#skF_4','#skF_6') ),
    inference(splitRight,[status(thm)],[c_6077])).

tff(c_7600,plain,(
    k4_xboole_0(k2_tarski('#skF_1','#skF_2'),'#skF_3') != k2_tarski('#skF_1','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_64])).

tff(c_7654,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_7600,c_6078])).

tff(c_7655,plain,(
    k4_xboole_0(k2_tarski('#skF_4','#skF_5'),'#skF_6') = k2_tarski('#skF_4','#skF_5') ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_7716,plain,(
    r1_tarski(k2_tarski('#skF_4','#skF_5'),k5_xboole_0(k2_tarski('#skF_4','#skF_5'),'#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_7655,c_36])).

tff(c_8106,plain,(
    r2_hidden('#skF_4',k5_xboole_0(k2_tarski('#skF_4','#skF_5'),'#skF_6')) ),
    inference(resolution,[status(thm)],[c_7716,c_54])).

tff(c_8957,plain,(
    ! [A_455,C_456,B_457] :
      ( ~ r2_hidden(A_455,C_456)
      | ~ r2_hidden(A_455,B_457)
      | ~ r2_hidden(A_455,k5_xboole_0(B_457,C_456)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_8969,plain,
    ( ~ r2_hidden('#skF_4','#skF_6')
    | ~ r2_hidden('#skF_4',k2_tarski('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_8106,c_8957])).

tff(c_8992,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_7825,c_7561,c_8969])).

tff(c_8993,plain,
    ( r2_hidden('#skF_4','#skF_6')
    | r2_hidden('#skF_5','#skF_6') ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_8995,plain,(
    r2_hidden('#skF_5','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_8993])).

tff(c_8994,plain,(
    r2_hidden('#skF_1','#skF_3') ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_68,plain,
    ( ~ r2_hidden('#skF_1','#skF_3')
    | k4_xboole_0(k2_tarski('#skF_4','#skF_5'),'#skF_6') = k2_tarski('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_8997,plain,(
    k4_xboole_0(k2_tarski('#skF_4','#skF_5'),'#skF_6') = k2_tarski('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8994,c_68])).

tff(c_9010,plain,(
    r1_tarski(k2_tarski('#skF_4','#skF_5'),k5_xboole_0(k2_tarski('#skF_4','#skF_5'),'#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_8997,c_36])).

tff(c_9347,plain,(
    r2_hidden('#skF_5',k5_xboole_0(k2_tarski('#skF_4','#skF_5'),'#skF_6')) ),
    inference(resolution,[status(thm)],[c_9010,c_52])).

tff(c_9754,plain,(
    ! [A_522,C_523,B_524] :
      ( ~ r2_hidden(A_522,C_523)
      | ~ r2_hidden(A_522,B_524)
      | ~ r2_hidden(A_522,k5_xboole_0(B_524,C_523)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_9757,plain,
    ( ~ r2_hidden('#skF_5','#skF_6')
    | ~ r2_hidden('#skF_5',k2_tarski('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_9347,c_9754])).

tff(c_9773,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_9426,c_8995,c_9757])).

tff(c_9774,plain,(
    r2_hidden('#skF_4','#skF_6') ),
    inference(splitRight,[status(thm)],[c_8993])).

tff(c_9777,plain,(
    k4_xboole_0(k2_tarski('#skF_4','#skF_5'),'#skF_6') = k2_tarski('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8994,c_68])).

tff(c_9790,plain,(
    r1_tarski(k2_tarski('#skF_4','#skF_5'),k5_xboole_0(k2_tarski('#skF_4','#skF_5'),'#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_9777,c_36])).

tff(c_10271,plain,(
    r2_hidden('#skF_4',k5_xboole_0(k2_tarski('#skF_4','#skF_5'),'#skF_6')) ),
    inference(resolution,[status(thm)],[c_9790,c_54])).

tff(c_11706,plain,(
    ! [A_641,C_642,B_643] :
      ( ~ r2_hidden(A_641,C_642)
      | ~ r2_hidden(A_641,B_643)
      | ~ r2_hidden(A_641,k5_xboole_0(B_643,C_642)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_11721,plain,
    ( ~ r2_hidden('#skF_4','#skF_6')
    | ~ r2_hidden('#skF_4',k2_tarski('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_10271,c_11706])).

tff(c_11735,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_10206,c_9774,c_11721])).

tff(c_11736,plain,
    ( r2_hidden('#skF_4','#skF_6')
    | r2_hidden('#skF_5','#skF_6') ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_11738,plain,(
    r2_hidden('#skF_5','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_11736])).

tff(c_11737,plain,(
    r2_hidden('#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_66,plain,
    ( ~ r2_hidden('#skF_2','#skF_3')
    | k4_xboole_0(k2_tarski('#skF_4','#skF_5'),'#skF_6') = k2_tarski('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_11852,plain,(
    k4_xboole_0(k2_tarski('#skF_4','#skF_5'),'#skF_6') = k2_tarski('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_11737,c_66])).

tff(c_11865,plain,(
    r1_tarski(k2_tarski('#skF_4','#skF_5'),k5_xboole_0(k2_tarski('#skF_4','#skF_5'),'#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_11852,c_36])).

tff(c_12288,plain,(
    r2_hidden('#skF_5',k5_xboole_0(k2_tarski('#skF_4','#skF_5'),'#skF_6')) ),
    inference(resolution,[status(thm)],[c_11865,c_52])).

tff(c_13907,plain,(
    ! [A_784,C_785,B_786] :
      ( ~ r2_hidden(A_784,C_785)
      | ~ r2_hidden(A_784,B_786)
      | ~ r2_hidden(A_784,k5_xboole_0(B_786,C_785)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_13925,plain,
    ( ~ r2_hidden('#skF_5','#skF_6')
    | ~ r2_hidden('#skF_5',k2_tarski('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_12288,c_13907])).

tff(c_13943,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12335,c_11738,c_13925])).

tff(c_13944,plain,(
    r2_hidden('#skF_4','#skF_6') ),
    inference(splitRight,[status(thm)],[c_11736])).

tff(c_14054,plain,(
    k4_xboole_0(k2_tarski('#skF_4','#skF_5'),'#skF_6') = k2_tarski('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_11737,c_66])).

tff(c_14067,plain,(
    r1_tarski(k2_tarski('#skF_4','#skF_5'),k5_xboole_0(k2_tarski('#skF_4','#skF_5'),'#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_14054,c_36])).

tff(c_14543,plain,(
    r2_hidden('#skF_4',k5_xboole_0(k2_tarski('#skF_4','#skF_5'),'#skF_6')) ),
    inference(resolution,[status(thm)],[c_14067,c_54])).

tff(c_16146,plain,(
    ! [A_928,C_929,B_930] :
      ( ~ r2_hidden(A_928,C_929)
      | ~ r2_hidden(A_928,B_930)
      | ~ r2_hidden(A_928,k5_xboole_0(B_930,C_929)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_16164,plain,
    ( ~ r2_hidden('#skF_4','#skF_6')
    | ~ r2_hidden('#skF_4',k2_tarski('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_14543,c_16146])).

tff(c_16179,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14686,c_13944,c_16164])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:46:16 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.84/3.19  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.84/3.20  
% 8.84/3.20  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.84/3.20  %$ r2_hidden > r1_xboole_0 > r1_tarski > k3_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 8.84/3.20  
% 8.84/3.20  %Foreground sorts:
% 8.84/3.20  
% 8.84/3.20  
% 8.84/3.20  %Background operators:
% 8.84/3.20  
% 8.84/3.20  
% 8.84/3.20  %Foreground operators:
% 8.84/3.20  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.84/3.20  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 8.84/3.20  tff(k1_tarski, type, k1_tarski: $i > $i).
% 8.84/3.20  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 8.84/3.20  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 8.84/3.20  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 8.84/3.20  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 8.84/3.20  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.84/3.20  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 8.84/3.20  tff('#skF_5', type, '#skF_5': $i).
% 8.84/3.20  tff('#skF_6', type, '#skF_6': $i).
% 8.84/3.20  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 8.84/3.20  tff('#skF_2', type, '#skF_2': $i).
% 8.84/3.20  tff('#skF_3', type, '#skF_3': $i).
% 8.84/3.20  tff('#skF_1', type, '#skF_1': $i).
% 8.84/3.20  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.84/3.20  tff(k3_tarski, type, k3_tarski: $i > $i).
% 8.84/3.20  tff('#skF_4', type, '#skF_4': $i).
% 8.84/3.20  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.84/3.20  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 8.84/3.20  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 8.84/3.20  
% 8.84/3.22  tff(f_74, axiom, (![A, B]: r1_tarski(k1_tarski(A), k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_zfmisc_1)).
% 8.84/3.22  tff(f_68, axiom, (![A, B]: (k3_enumset1(A, A, A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_enumset1)).
% 8.84/3.22  tff(f_70, axiom, (![A]: (k3_enumset1(A, A, A, A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t87_enumset1)).
% 8.84/3.22  tff(f_80, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 8.84/3.22  tff(f_66, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 8.84/3.22  tff(f_99, negated_conjecture, ~(![A, B, C]: ((k4_xboole_0(k2_tarski(A, B), C) = k2_tarski(A, B)) <=> (~r2_hidden(A, C) & ~r2_hidden(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_zfmisc_1)).
% 8.84/3.22  tff(f_90, axiom, (![A, B, C]: ~((~r2_hidden(A, B) & ~r2_hidden(C, B)) & ~r1_xboole_0(k2_tarski(A, C), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t57_zfmisc_1)).
% 8.84/3.22  tff(f_54, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 8.84/3.22  tff(f_62, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), k5_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t96_xboole_1)).
% 8.84/3.22  tff(f_32, axiom, (![A, B, C]: (r2_hidden(A, k5_xboole_0(B, C)) <=> ~(r2_hidden(A, B) <=> r2_hidden(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_0)).
% 8.84/3.22  tff(c_48, plain, (![A_38, B_39]: (r1_tarski(k1_tarski(A_38), k2_tarski(A_38, B_39)))), inference(cnfTransformation, [status(thm)], [f_74])).
% 8.84/3.22  tff(c_14350, plain, (![A_830, B_831]: (k3_enumset1(A_830, A_830, A_830, A_830, B_831)=k2_tarski(A_830, B_831))), inference(cnfTransformation, [status(thm)], [f_68])).
% 8.84/3.22  tff(c_44, plain, (![A_35]: (k3_enumset1(A_35, A_35, A_35, A_35, A_35)=k1_tarski(A_35))), inference(cnfTransformation, [status(thm)], [f_70])).
% 8.84/3.22  tff(c_14366, plain, (![B_832]: (k2_tarski(B_832, B_832)=k1_tarski(B_832))), inference(superposition, [status(thm), theory('equality')], [c_14350, c_44])).
% 8.84/3.22  tff(c_54, plain, (![A_40, C_42, B_41]: (r2_hidden(A_40, C_42) | ~r1_tarski(k2_tarski(A_40, B_41), C_42))), inference(cnfTransformation, [status(thm)], [f_80])).
% 8.84/3.22  tff(c_14658, plain, (![B_850, C_851]: (r2_hidden(B_850, C_851) | ~r1_tarski(k1_tarski(B_850), C_851))), inference(superposition, [status(thm), theory('equality')], [c_14366, c_54])).
% 8.84/3.22  tff(c_14686, plain, (![A_38, B_39]: (r2_hidden(A_38, k2_tarski(A_38, B_39)))), inference(resolution, [status(thm)], [c_48, c_14658])).
% 8.84/3.22  tff(c_40, plain, (![B_32, A_31]: (k2_tarski(B_32, A_31)=k2_tarski(A_31, B_32))), inference(cnfTransformation, [status(thm)], [f_66])).
% 8.84/3.22  tff(c_105, plain, (![A_52, B_53]: (r1_tarski(k1_tarski(A_52), k2_tarski(A_52, B_53)))), inference(cnfTransformation, [status(thm)], [f_74])).
% 8.84/3.22  tff(c_108, plain, (![A_31, B_32]: (r1_tarski(k1_tarski(A_31), k2_tarski(B_32, A_31)))), inference(superposition, [status(thm), theory('equality')], [c_40, c_105])).
% 8.84/3.22  tff(c_12118, plain, (![A_685, B_686]: (k3_enumset1(A_685, A_685, A_685, A_685, B_686)=k2_tarski(A_685, B_686))), inference(cnfTransformation, [status(thm)], [f_68])).
% 8.84/3.22  tff(c_12134, plain, (![B_687]: (k2_tarski(B_687, B_687)=k1_tarski(B_687))), inference(superposition, [status(thm), theory('equality')], [c_12118, c_44])).
% 8.84/3.22  tff(c_52, plain, (![B_41, C_42, A_40]: (r2_hidden(B_41, C_42) | ~r1_tarski(k2_tarski(A_40, B_41), C_42))), inference(cnfTransformation, [status(thm)], [f_80])).
% 8.84/3.22  tff(c_12308, plain, (![B_699, C_700]: (r2_hidden(B_699, C_700) | ~r1_tarski(k1_tarski(B_699), C_700))), inference(superposition, [status(thm), theory('equality')], [c_12134, c_52])).
% 8.84/3.22  tff(c_12335, plain, (![A_31, B_32]: (r2_hidden(A_31, k2_tarski(B_32, A_31)))), inference(resolution, [status(thm)], [c_108, c_12308])).
% 8.84/3.22  tff(c_10013, plain, (![A_549, B_550]: (k3_enumset1(A_549, A_549, A_549, A_549, B_550)=k2_tarski(A_549, B_550))), inference(cnfTransformation, [status(thm)], [f_68])).
% 8.84/3.22  tff(c_10029, plain, (![B_551]: (k2_tarski(B_551, B_551)=k1_tarski(B_551))), inference(superposition, [status(thm), theory('equality')], [c_10013, c_44])).
% 8.84/3.22  tff(c_10178, plain, (![B_563, C_564]: (r2_hidden(B_563, C_564) | ~r1_tarski(k1_tarski(B_563), C_564))), inference(superposition, [status(thm), theory('equality')], [c_10029, c_52])).
% 8.84/3.22  tff(c_10206, plain, (![A_38, B_39]: (r2_hidden(A_38, k2_tarski(A_38, B_39)))), inference(resolution, [status(thm)], [c_48, c_10178])).
% 8.84/3.22  tff(c_9183, plain, (![A_480, B_481]: (k3_enumset1(A_480, A_480, A_480, A_480, B_481)=k2_tarski(A_480, B_481))), inference(cnfTransformation, [status(thm)], [f_68])).
% 8.84/3.22  tff(c_9199, plain, (![B_482]: (k2_tarski(B_482, B_482)=k1_tarski(B_482))), inference(superposition, [status(thm), theory('equality')], [c_9183, c_44])).
% 8.84/3.22  tff(c_9399, plain, (![B_499, C_500]: (r2_hidden(B_499, C_500) | ~r1_tarski(k1_tarski(B_499), C_500))), inference(superposition, [status(thm), theory('equality')], [c_9199, c_54])).
% 8.84/3.22  tff(c_9426, plain, (![A_31, B_32]: (r2_hidden(A_31, k2_tarski(B_32, A_31)))), inference(resolution, [status(thm)], [c_108, c_9399])).
% 8.84/3.22  tff(c_475, plain, (![A_103, B_104]: (k3_enumset1(A_103, A_103, A_103, A_103, B_104)=k2_tarski(A_103, B_104))), inference(cnfTransformation, [status(thm)], [f_68])).
% 8.84/3.22  tff(c_491, plain, (![B_105]: (k2_tarski(B_105, B_105)=k1_tarski(B_105))), inference(superposition, [status(thm), theory('equality')], [c_475, c_44])).
% 8.84/3.22  tff(c_7797, plain, (![B_392, C_393]: (r2_hidden(B_392, C_393) | ~r1_tarski(k1_tarski(B_392), C_393))), inference(superposition, [status(thm), theory('equality')], [c_491, c_54])).
% 8.84/3.22  tff(c_7825, plain, (![A_38, B_39]: (r2_hidden(A_38, k2_tarski(A_38, B_39)))), inference(resolution, [status(thm)], [c_48, c_7797])).
% 8.84/3.22  tff(c_6346, plain, (![B_313, C_314]: (r2_hidden(B_313, C_314) | ~r1_tarski(k1_tarski(B_313), C_314))), inference(superposition, [status(thm), theory('equality')], [c_491, c_54])).
% 8.84/3.22  tff(c_6373, plain, (![A_31, B_32]: (r2_hidden(A_31, k2_tarski(B_32, A_31)))), inference(resolution, [status(thm)], [c_108, c_6346])).
% 8.84/3.22  tff(c_62, plain, (~r2_hidden('#skF_1', '#skF_3') | r2_hidden('#skF_5', '#skF_6') | r2_hidden('#skF_4', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_99])).
% 8.84/3.22  tff(c_244, plain, (~r2_hidden('#skF_1', '#skF_3')), inference(splitLeft, [status(thm)], [c_62])).
% 8.84/3.22  tff(c_60, plain, (~r2_hidden('#skF_2', '#skF_3') | r2_hidden('#skF_5', '#skF_6') | r2_hidden('#skF_4', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_99])).
% 8.84/3.22  tff(c_139, plain, (~r2_hidden('#skF_2', '#skF_3')), inference(splitLeft, [status(thm)], [c_60])).
% 8.84/3.22  tff(c_1352, plain, (![A_173, C_174, B_175]: (r1_xboole_0(k2_tarski(A_173, C_174), B_175) | r2_hidden(C_174, B_175) | r2_hidden(A_173, B_175))), inference(cnfTransformation, [status(thm)], [f_90])).
% 8.84/3.22  tff(c_26, plain, (![A_18, B_19]: (k4_xboole_0(A_18, B_19)=A_18 | ~r1_xboole_0(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_54])).
% 8.84/3.22  tff(c_5869, plain, (![A_297, C_298, B_299]: (k4_xboole_0(k2_tarski(A_297, C_298), B_299)=k2_tarski(A_297, C_298) | r2_hidden(C_298, B_299) | r2_hidden(A_297, B_299))), inference(resolution, [status(thm)], [c_1352, c_26])).
% 8.84/3.22  tff(c_58, plain, (k4_xboole_0(k2_tarski('#skF_1', '#skF_2'), '#skF_3')!=k2_tarski('#skF_1', '#skF_2') | r2_hidden('#skF_5', '#skF_6') | r2_hidden('#skF_4', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_99])).
% 8.84/3.22  tff(c_532, plain, (k4_xboole_0(k2_tarski('#skF_1', '#skF_2'), '#skF_3')!=k2_tarski('#skF_1', '#skF_2')), inference(splitLeft, [status(thm)], [c_58])).
% 8.84/3.22  tff(c_5999, plain, (r2_hidden('#skF_2', '#skF_3') | r2_hidden('#skF_1', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_5869, c_532])).
% 8.84/3.22  tff(c_6076, plain, $false, inference(negUnitSimplification, [status(thm)], [c_244, c_139, c_5999])).
% 8.84/3.22  tff(c_6077, plain, (r2_hidden('#skF_4', '#skF_6') | r2_hidden('#skF_5', '#skF_6')), inference(splitRight, [status(thm)], [c_58])).
% 8.84/3.22  tff(c_6080, plain, (r2_hidden('#skF_5', '#skF_6')), inference(splitLeft, [status(thm)], [c_6077])).
% 8.84/3.22  tff(c_64, plain, (k4_xboole_0(k2_tarski('#skF_1', '#skF_2'), '#skF_3')!=k2_tarski('#skF_1', '#skF_2') | k4_xboole_0(k2_tarski('#skF_4', '#skF_5'), '#skF_6')=k2_tarski('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_99])).
% 8.84/3.22  tff(c_6081, plain, (k4_xboole_0(k2_tarski('#skF_1', '#skF_2'), '#skF_3')!=k2_tarski('#skF_1', '#skF_2')), inference(splitLeft, [status(thm)], [c_64])).
% 8.84/3.22  tff(c_6078, plain, (k4_xboole_0(k2_tarski('#skF_1', '#skF_2'), '#skF_3')=k2_tarski('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_58])).
% 8.84/3.22  tff(c_6170, plain, $false, inference(negUnitSimplification, [status(thm)], [c_6081, c_6078])).
% 8.84/3.22  tff(c_6171, plain, (k4_xboole_0(k2_tarski('#skF_4', '#skF_5'), '#skF_6')=k2_tarski('#skF_4', '#skF_5')), inference(splitRight, [status(thm)], [c_64])).
% 8.84/3.22  tff(c_36, plain, (![A_27, B_28]: (r1_tarski(k4_xboole_0(A_27, B_28), k5_xboole_0(A_27, B_28)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 8.84/3.22  tff(c_6268, plain, (r1_tarski(k2_tarski('#skF_4', '#skF_5'), k5_xboole_0(k2_tarski('#skF_4', '#skF_5'), '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_6171, c_36])).
% 8.84/3.22  tff(c_6523, plain, (r2_hidden('#skF_5', k5_xboole_0(k2_tarski('#skF_4', '#skF_5'), '#skF_6'))), inference(resolution, [status(thm)], [c_6268, c_52])).
% 8.84/3.22  tff(c_7522, plain, (![A_376, C_377, B_378]: (~r2_hidden(A_376, C_377) | ~r2_hidden(A_376, B_378) | ~r2_hidden(A_376, k5_xboole_0(B_378, C_377)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 8.84/3.22  tff(c_7540, plain, (~r2_hidden('#skF_5', '#skF_6') | ~r2_hidden('#skF_5', k2_tarski('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_6523, c_7522])).
% 8.84/3.22  tff(c_7560, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6373, c_6080, c_7540])).
% 8.84/3.22  tff(c_7561, plain, (r2_hidden('#skF_4', '#skF_6')), inference(splitRight, [status(thm)], [c_6077])).
% 8.84/3.22  tff(c_7600, plain, (k4_xboole_0(k2_tarski('#skF_1', '#skF_2'), '#skF_3')!=k2_tarski('#skF_1', '#skF_2')), inference(splitLeft, [status(thm)], [c_64])).
% 8.84/3.22  tff(c_7654, plain, $false, inference(negUnitSimplification, [status(thm)], [c_7600, c_6078])).
% 8.84/3.22  tff(c_7655, plain, (k4_xboole_0(k2_tarski('#skF_4', '#skF_5'), '#skF_6')=k2_tarski('#skF_4', '#skF_5')), inference(splitRight, [status(thm)], [c_64])).
% 8.84/3.22  tff(c_7716, plain, (r1_tarski(k2_tarski('#skF_4', '#skF_5'), k5_xboole_0(k2_tarski('#skF_4', '#skF_5'), '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_7655, c_36])).
% 8.84/3.22  tff(c_8106, plain, (r2_hidden('#skF_4', k5_xboole_0(k2_tarski('#skF_4', '#skF_5'), '#skF_6'))), inference(resolution, [status(thm)], [c_7716, c_54])).
% 8.84/3.22  tff(c_8957, plain, (![A_455, C_456, B_457]: (~r2_hidden(A_455, C_456) | ~r2_hidden(A_455, B_457) | ~r2_hidden(A_455, k5_xboole_0(B_457, C_456)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 8.84/3.22  tff(c_8969, plain, (~r2_hidden('#skF_4', '#skF_6') | ~r2_hidden('#skF_4', k2_tarski('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_8106, c_8957])).
% 8.84/3.22  tff(c_8992, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_7825, c_7561, c_8969])).
% 8.84/3.22  tff(c_8993, plain, (r2_hidden('#skF_4', '#skF_6') | r2_hidden('#skF_5', '#skF_6')), inference(splitRight, [status(thm)], [c_62])).
% 8.84/3.22  tff(c_8995, plain, (r2_hidden('#skF_5', '#skF_6')), inference(splitLeft, [status(thm)], [c_8993])).
% 8.84/3.22  tff(c_8994, plain, (r2_hidden('#skF_1', '#skF_3')), inference(splitRight, [status(thm)], [c_62])).
% 8.84/3.22  tff(c_68, plain, (~r2_hidden('#skF_1', '#skF_3') | k4_xboole_0(k2_tarski('#skF_4', '#skF_5'), '#skF_6')=k2_tarski('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_99])).
% 8.84/3.22  tff(c_8997, plain, (k4_xboole_0(k2_tarski('#skF_4', '#skF_5'), '#skF_6')=k2_tarski('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_8994, c_68])).
% 8.84/3.22  tff(c_9010, plain, (r1_tarski(k2_tarski('#skF_4', '#skF_5'), k5_xboole_0(k2_tarski('#skF_4', '#skF_5'), '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_8997, c_36])).
% 8.84/3.22  tff(c_9347, plain, (r2_hidden('#skF_5', k5_xboole_0(k2_tarski('#skF_4', '#skF_5'), '#skF_6'))), inference(resolution, [status(thm)], [c_9010, c_52])).
% 8.84/3.22  tff(c_9754, plain, (![A_522, C_523, B_524]: (~r2_hidden(A_522, C_523) | ~r2_hidden(A_522, B_524) | ~r2_hidden(A_522, k5_xboole_0(B_524, C_523)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 8.84/3.22  tff(c_9757, plain, (~r2_hidden('#skF_5', '#skF_6') | ~r2_hidden('#skF_5', k2_tarski('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_9347, c_9754])).
% 8.84/3.22  tff(c_9773, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_9426, c_8995, c_9757])).
% 8.84/3.22  tff(c_9774, plain, (r2_hidden('#skF_4', '#skF_6')), inference(splitRight, [status(thm)], [c_8993])).
% 8.84/3.22  tff(c_9777, plain, (k4_xboole_0(k2_tarski('#skF_4', '#skF_5'), '#skF_6')=k2_tarski('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_8994, c_68])).
% 8.84/3.22  tff(c_9790, plain, (r1_tarski(k2_tarski('#skF_4', '#skF_5'), k5_xboole_0(k2_tarski('#skF_4', '#skF_5'), '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_9777, c_36])).
% 8.84/3.22  tff(c_10271, plain, (r2_hidden('#skF_4', k5_xboole_0(k2_tarski('#skF_4', '#skF_5'), '#skF_6'))), inference(resolution, [status(thm)], [c_9790, c_54])).
% 8.84/3.22  tff(c_11706, plain, (![A_641, C_642, B_643]: (~r2_hidden(A_641, C_642) | ~r2_hidden(A_641, B_643) | ~r2_hidden(A_641, k5_xboole_0(B_643, C_642)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 8.84/3.22  tff(c_11721, plain, (~r2_hidden('#skF_4', '#skF_6') | ~r2_hidden('#skF_4', k2_tarski('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_10271, c_11706])).
% 8.84/3.22  tff(c_11735, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_10206, c_9774, c_11721])).
% 8.84/3.22  tff(c_11736, plain, (r2_hidden('#skF_4', '#skF_6') | r2_hidden('#skF_5', '#skF_6')), inference(splitRight, [status(thm)], [c_60])).
% 8.84/3.22  tff(c_11738, plain, (r2_hidden('#skF_5', '#skF_6')), inference(splitLeft, [status(thm)], [c_11736])).
% 8.84/3.22  tff(c_11737, plain, (r2_hidden('#skF_2', '#skF_3')), inference(splitRight, [status(thm)], [c_60])).
% 8.84/3.22  tff(c_66, plain, (~r2_hidden('#skF_2', '#skF_3') | k4_xboole_0(k2_tarski('#skF_4', '#skF_5'), '#skF_6')=k2_tarski('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_99])).
% 8.84/3.22  tff(c_11852, plain, (k4_xboole_0(k2_tarski('#skF_4', '#skF_5'), '#skF_6')=k2_tarski('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_11737, c_66])).
% 8.84/3.22  tff(c_11865, plain, (r1_tarski(k2_tarski('#skF_4', '#skF_5'), k5_xboole_0(k2_tarski('#skF_4', '#skF_5'), '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_11852, c_36])).
% 8.84/3.22  tff(c_12288, plain, (r2_hidden('#skF_5', k5_xboole_0(k2_tarski('#skF_4', '#skF_5'), '#skF_6'))), inference(resolution, [status(thm)], [c_11865, c_52])).
% 8.84/3.22  tff(c_13907, plain, (![A_784, C_785, B_786]: (~r2_hidden(A_784, C_785) | ~r2_hidden(A_784, B_786) | ~r2_hidden(A_784, k5_xboole_0(B_786, C_785)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 8.84/3.22  tff(c_13925, plain, (~r2_hidden('#skF_5', '#skF_6') | ~r2_hidden('#skF_5', k2_tarski('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_12288, c_13907])).
% 8.84/3.22  tff(c_13943, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12335, c_11738, c_13925])).
% 8.84/3.22  tff(c_13944, plain, (r2_hidden('#skF_4', '#skF_6')), inference(splitRight, [status(thm)], [c_11736])).
% 8.84/3.22  tff(c_14054, plain, (k4_xboole_0(k2_tarski('#skF_4', '#skF_5'), '#skF_6')=k2_tarski('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_11737, c_66])).
% 8.84/3.22  tff(c_14067, plain, (r1_tarski(k2_tarski('#skF_4', '#skF_5'), k5_xboole_0(k2_tarski('#skF_4', '#skF_5'), '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_14054, c_36])).
% 8.84/3.22  tff(c_14543, plain, (r2_hidden('#skF_4', k5_xboole_0(k2_tarski('#skF_4', '#skF_5'), '#skF_6'))), inference(resolution, [status(thm)], [c_14067, c_54])).
% 8.84/3.22  tff(c_16146, plain, (![A_928, C_929, B_930]: (~r2_hidden(A_928, C_929) | ~r2_hidden(A_928, B_930) | ~r2_hidden(A_928, k5_xboole_0(B_930, C_929)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 8.84/3.22  tff(c_16164, plain, (~r2_hidden('#skF_4', '#skF_6') | ~r2_hidden('#skF_4', k2_tarski('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_14543, c_16146])).
% 8.84/3.22  tff(c_16179, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_14686, c_13944, c_16164])).
% 8.84/3.22  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.84/3.22  
% 8.84/3.22  Inference rules
% 8.84/3.22  ----------------------
% 8.84/3.22  #Ref     : 0
% 8.84/3.22  #Sup     : 4115
% 8.84/3.22  #Fact    : 0
% 8.84/3.22  #Define  : 0
% 8.84/3.22  #Split   : 16
% 8.84/3.22  #Chain   : 0
% 8.84/3.22  #Close   : 0
% 8.84/3.22  
% 8.84/3.22  Ordering : KBO
% 8.84/3.22  
% 8.84/3.22  Simplification rules
% 8.84/3.22  ----------------------
% 8.84/3.22  #Subsume      : 162
% 8.84/3.22  #Demod        : 2820
% 8.84/3.22  #Tautology    : 2070
% 8.84/3.22  #SimpNegUnit  : 8
% 8.84/3.22  #BackRed      : 21
% 8.84/3.22  
% 8.84/3.22  #Partial instantiations: 0
% 8.84/3.22  #Strategies tried      : 1
% 8.84/3.22  
% 8.84/3.22  Timing (in seconds)
% 8.84/3.22  ----------------------
% 8.84/3.23  Preprocessing        : 0.32
% 8.84/3.23  Parsing              : 0.17
% 8.84/3.23  CNF conversion       : 0.02
% 8.84/3.23  Main loop            : 2.14
% 8.84/3.23  Inferencing          : 0.60
% 8.84/3.23  Reduction            : 0.96
% 8.84/3.23  Demodulation         : 0.78
% 8.84/3.23  BG Simplification    : 0.07
% 8.84/3.23  Subsumption          : 0.34
% 8.84/3.23  Abstraction          : 0.08
% 8.84/3.23  MUC search           : 0.00
% 8.84/3.23  Cooper               : 0.00
% 8.84/3.23  Total                : 2.50
% 8.84/3.23  Index Insertion      : 0.00
% 8.84/3.23  Index Deletion       : 0.00
% 8.84/3.23  Index Matching       : 0.00
% 8.84/3.23  BG Taut test         : 0.00
%------------------------------------------------------------------------------

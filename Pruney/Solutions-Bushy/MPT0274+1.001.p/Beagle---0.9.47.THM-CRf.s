%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0274+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:36:01 EST 2020

% Result     : Theorem 2.02s
% Output     : CNFRefutation 2.02s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 146 expanded)
%              Number of leaves         :   18 (  54 expanded)
%              Depth                    :    5
%              Number of atoms          :   99 ( 262 expanded)
%              Number of equality atoms :   32 (  82 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k4_xboole_0 > k2_tarski > #nlpp > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

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

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(f_26,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_54,negated_conjecture,(
    ~ ! [A,B,C] :
        ( k4_xboole_0(k2_tarski(A,B),C) = k2_tarski(A,B)
      <=> ( ~ r2_hidden(A,C)
          & ~ r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_zfmisc_1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ~ ( ~ r2_hidden(A,B)
        & ~ r2_hidden(C,B)
        & ~ r1_xboole_0(k2_tarski(A,C),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_zfmisc_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ~ ( r1_xboole_0(k2_tarski(A,B),C)
        & r2_hidden(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_zfmisc_1)).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_tarski(B_2,A_1) = k2_tarski(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_16,plain,
    ( ~ r2_hidden('#skF_1','#skF_3')
    | r2_hidden('#skF_5','#skF_6')
    | r2_hidden('#skF_4','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_87,plain,(
    ~ r2_hidden('#skF_1','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_16])).

tff(c_14,plain,
    ( ~ r2_hidden('#skF_2','#skF_3')
    | r2_hidden('#skF_5','#skF_6')
    | r2_hidden('#skF_4','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_86,plain,(
    ~ r2_hidden('#skF_2','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_14])).

tff(c_89,plain,(
    ! [A_23,C_24,B_25] :
      ( r1_xboole_0(k2_tarski(A_23,C_24),B_25)
      | r2_hidden(C_24,B_25)
      | r2_hidden(A_23,B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_8,plain,(
    ! [A_9,B_10] :
      ( k4_xboole_0(A_9,B_10) = A_9
      | ~ r1_xboole_0(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_137,plain,(
    ! [A_38,C_39,B_40] :
      ( k4_xboole_0(k2_tarski(A_38,C_39),B_40) = k2_tarski(A_38,C_39)
      | r2_hidden(C_39,B_40)
      | r2_hidden(A_38,B_40) ) ),
    inference(resolution,[status(thm)],[c_89,c_8])).

tff(c_12,plain,
    ( k4_xboole_0(k2_tarski('#skF_1','#skF_2'),'#skF_3') != k2_tarski('#skF_1','#skF_2')
    | r2_hidden('#skF_5','#skF_6')
    | r2_hidden('#skF_4','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_115,plain,(
    k4_xboole_0(k2_tarski('#skF_1','#skF_2'),'#skF_3') != k2_tarski('#skF_1','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_12])).

tff(c_152,plain,
    ( r2_hidden('#skF_2','#skF_3')
    | r2_hidden('#skF_1','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_137,c_115])).

tff(c_170,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_87,c_86,c_152])).

tff(c_171,plain,
    ( r2_hidden('#skF_4','#skF_6')
    | r2_hidden('#skF_5','#skF_6') ),
    inference(splitRight,[status(thm)],[c_12])).

tff(c_173,plain,(
    r2_hidden('#skF_5','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_171])).

tff(c_172,plain,(
    k4_xboole_0(k2_tarski('#skF_1','#skF_2'),'#skF_3') = k2_tarski('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_12])).

tff(c_18,plain,
    ( k4_xboole_0(k2_tarski('#skF_1','#skF_2'),'#skF_3') != k2_tarski('#skF_1','#skF_2')
    | k4_xboole_0(k2_tarski('#skF_4','#skF_5'),'#skF_6') = k2_tarski('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_195,plain,(
    k4_xboole_0(k2_tarski('#skF_4','#skF_5'),'#skF_6') = k2_tarski('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_172,c_18])).

tff(c_10,plain,(
    ! [A_9,B_10] :
      ( r1_xboole_0(A_9,B_10)
      | k4_xboole_0(A_9,B_10) != A_9 ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_62,plain,(
    ! [A_17,C_18,B_19] :
      ( ~ r2_hidden(A_17,C_18)
      | ~ r1_xboole_0(k2_tarski(A_17,B_19),C_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_108,plain,(
    ! [A_26,B_27,B_28] :
      ( ~ r2_hidden(A_26,B_27)
      | k4_xboole_0(k2_tarski(A_26,B_28),B_27) != k2_tarski(A_26,B_28) ) ),
    inference(resolution,[status(thm)],[c_10,c_62])).

tff(c_111,plain,(
    ! [A_1,B_27,B_2] :
      ( ~ r2_hidden(A_1,B_27)
      | k4_xboole_0(k2_tarski(B_2,A_1),B_27) != k2_tarski(A_1,B_2) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_108])).

tff(c_199,plain,
    ( ~ r2_hidden('#skF_5','#skF_6')
    | k2_tarski('#skF_5','#skF_4') != k2_tarski('#skF_4','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_195,c_111])).

tff(c_207,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_173,c_199])).

tff(c_208,plain,(
    r2_hidden('#skF_4','#skF_6') ),
    inference(splitRight,[status(thm)],[c_171])).

tff(c_231,plain,(
    k4_xboole_0(k2_tarski('#skF_4','#skF_5'),'#skF_6') = k2_tarski('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_172,c_18])).

tff(c_73,plain,(
    ! [A_17,B_10,B_19] :
      ( ~ r2_hidden(A_17,B_10)
      | k4_xboole_0(k2_tarski(A_17,B_19),B_10) != k2_tarski(A_17,B_19) ) ),
    inference(resolution,[status(thm)],[c_10,c_62])).

tff(c_238,plain,(
    ~ r2_hidden('#skF_4','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_231,c_73])).

tff(c_246,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_208,c_238])).

tff(c_247,plain,
    ( r2_hidden('#skF_4','#skF_6')
    | r2_hidden('#skF_5','#skF_6') ),
    inference(splitRight,[status(thm)],[c_16])).

tff(c_249,plain,(
    r2_hidden('#skF_5','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_247])).

tff(c_248,plain,(
    r2_hidden('#skF_1','#skF_3') ),
    inference(splitRight,[status(thm)],[c_16])).

tff(c_22,plain,
    ( ~ r2_hidden('#skF_1','#skF_3')
    | k4_xboole_0(k2_tarski('#skF_4','#skF_5'),'#skF_6') = k2_tarski('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_251,plain,(
    k4_xboole_0(k2_tarski('#skF_4','#skF_5'),'#skF_6') = k2_tarski('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_248,c_22])).

tff(c_276,plain,(
    ! [A_50,B_51,B_52] :
      ( ~ r2_hidden(A_50,B_51)
      | k4_xboole_0(k2_tarski(A_50,B_52),B_51) != k2_tarski(A_50,B_52) ) ),
    inference(resolution,[status(thm)],[c_10,c_62])).

tff(c_287,plain,(
    ! [B_53,B_54,A_55] :
      ( ~ r2_hidden(B_53,B_54)
      | k4_xboole_0(k2_tarski(A_55,B_53),B_54) != k2_tarski(B_53,A_55) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_276])).

tff(c_290,plain,
    ( ~ r2_hidden('#skF_5','#skF_6')
    | k2_tarski('#skF_5','#skF_4') != k2_tarski('#skF_4','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_251,c_287])).

tff(c_299,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_249,c_290])).

tff(c_300,plain,(
    r2_hidden('#skF_4','#skF_6') ),
    inference(splitRight,[status(thm)],[c_247])).

tff(c_322,plain,(
    k4_xboole_0(k2_tarski('#skF_4','#skF_5'),'#skF_6') = k2_tarski('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_248,c_22])).

tff(c_328,plain,(
    ! [A_59,B_60,B_61] :
      ( ~ r2_hidden(A_59,B_60)
      | k4_xboole_0(k2_tarski(A_59,B_61),B_60) != k2_tarski(A_59,B_61) ) ),
    inference(resolution,[status(thm)],[c_10,c_62])).

tff(c_331,plain,(
    ~ r2_hidden('#skF_4','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_322,c_328])).

tff(c_341,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_300,c_331])).

tff(c_342,plain,
    ( r2_hidden('#skF_4','#skF_6')
    | r2_hidden('#skF_5','#skF_6') ),
    inference(splitRight,[status(thm)],[c_14])).

tff(c_344,plain,(
    r2_hidden('#skF_5','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_342])).

tff(c_343,plain,(
    r2_hidden('#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_14])).

tff(c_20,plain,
    ( ~ r2_hidden('#skF_2','#skF_3')
    | k4_xboole_0(k2_tarski('#skF_4','#skF_5'),'#skF_6') = k2_tarski('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_367,plain,(
    k4_xboole_0(k2_tarski('#skF_4','#skF_5'),'#skF_6') = k2_tarski('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_343,c_20])).

tff(c_372,plain,(
    ! [A_65,B_66,B_67] :
      ( ~ r2_hidden(A_65,B_66)
      | k4_xboole_0(k2_tarski(A_65,B_67),B_66) != k2_tarski(A_65,B_67) ) ),
    inference(resolution,[status(thm)],[c_10,c_62])).

tff(c_383,plain,(
    ! [B_68,B_69,A_70] :
      ( ~ r2_hidden(B_68,B_69)
      | k4_xboole_0(k2_tarski(A_70,B_68),B_69) != k2_tarski(B_68,A_70) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_372])).

tff(c_386,plain,
    ( ~ r2_hidden('#skF_5','#skF_6')
    | k2_tarski('#skF_5','#skF_4') != k2_tarski('#skF_4','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_367,c_383])).

tff(c_395,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_344,c_386])).

tff(c_396,plain,(
    r2_hidden('#skF_4','#skF_6') ),
    inference(splitRight,[status(thm)],[c_342])).

tff(c_421,plain,(
    k4_xboole_0(k2_tarski('#skF_4','#skF_5'),'#skF_6') = k2_tarski('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_343,c_20])).

tff(c_426,plain,(
    ! [A_74,B_75,B_76] :
      ( ~ r2_hidden(A_74,B_75)
      | k4_xboole_0(k2_tarski(A_74,B_76),B_75) != k2_tarski(A_74,B_76) ) ),
    inference(resolution,[status(thm)],[c_10,c_62])).

tff(c_429,plain,(
    ~ r2_hidden('#skF_4','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_421,c_426])).

tff(c_439,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_396,c_429])).

%------------------------------------------------------------------------------

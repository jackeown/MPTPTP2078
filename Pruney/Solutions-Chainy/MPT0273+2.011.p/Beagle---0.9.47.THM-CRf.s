%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:53:12 EST 2020

% Result     : Theorem 2.02s
% Output     : CNFRefutation 2.38s
% Verified   : 
% Statistics : Number of formulae       :  138 ( 408 expanded)
%              Number of leaves         :   16 ( 127 expanded)
%              Depth                    :    9
%              Number of atoms          :  195 ( 929 expanded)
%              Number of equality atoms :   82 ( 432 expanded)
%              Maximal formula depth    :    8 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k4_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

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

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(f_46,negated_conjecture,(
    ~ ! [A,B,C] :
        ( k4_xboole_0(k2_tarski(A,B),C) = k1_tarski(A)
      <=> ( ~ r2_hidden(A,C)
          & ( r2_hidden(B,C)
            | A = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_zfmisc_1)).

tff(f_27,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_36,axiom,(
    ! [A,B,C] :
      ( k4_xboole_0(k2_tarski(A,B),C) = k1_tarski(A)
    <=> ( ~ r2_hidden(A,C)
        & ( r2_hidden(B,C)
          | A = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l38_zfmisc_1)).

tff(c_22,plain,
    ( ~ r2_hidden('#skF_1','#skF_3')
    | ~ r2_hidden('#skF_5','#skF_6')
    | r2_hidden('#skF_4','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_40,plain,(
    ~ r2_hidden('#skF_5','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_22])).

tff(c_16,plain,
    ( ~ r2_hidden('#skF_1','#skF_3')
    | '#skF_5' != '#skF_4'
    | r2_hidden('#skF_4','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_39,plain,(
    '#skF_5' != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_16])).

tff(c_28,plain,
    ( ~ r2_hidden('#skF_1','#skF_3')
    | k4_xboole_0(k2_tarski('#skF_4','#skF_5'),'#skF_6') = k1_tarski('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_59,plain,(
    ~ r2_hidden('#skF_1','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_28])).

tff(c_2,plain,(
    ! [A_1] : k2_tarski(A_1,A_1) = k1_tarski(A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_8,plain,(
    ! [B_3,C_4] :
      ( k4_xboole_0(k2_tarski(B_3,B_3),C_4) = k1_tarski(B_3)
      | r2_hidden(B_3,C_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_29,plain,(
    ! [B_3,C_4] :
      ( k4_xboole_0(k1_tarski(B_3),C_4) = k1_tarski(B_3)
      | r2_hidden(B_3,C_4) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_8])).

tff(c_26,plain,
    ( '#skF_2' = '#skF_1'
    | r2_hidden('#skF_2','#skF_3')
    | k4_xboole_0(k2_tarski('#skF_4','#skF_5'),'#skF_6') = k1_tarski('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_65,plain,(
    k4_xboole_0(k2_tarski('#skF_4','#skF_5'),'#skF_6') = k1_tarski('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_26])).

tff(c_4,plain,(
    ! [B_3,A_2,C_4] :
      ( B_3 = A_2
      | r2_hidden(B_3,C_4)
      | k4_xboole_0(k2_tarski(A_2,B_3),C_4) != k1_tarski(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_69,plain,
    ( '#skF_5' = '#skF_4'
    | r2_hidden('#skF_5','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_65,c_4])).

tff(c_78,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_39,c_69])).

tff(c_80,plain,(
    k4_xboole_0(k2_tarski('#skF_4','#skF_5'),'#skF_6') != k1_tarski('#skF_4') ),
    inference(splitRight,[status(thm)],[c_26])).

tff(c_79,plain,
    ( r2_hidden('#skF_2','#skF_3')
    | '#skF_2' = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_26])).

tff(c_81,plain,(
    '#skF_2' = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_79])).

tff(c_24,plain,
    ( k4_xboole_0(k2_tarski('#skF_1','#skF_2'),'#skF_3') != k1_tarski('#skF_1')
    | k4_xboole_0(k2_tarski('#skF_4','#skF_5'),'#skF_6') = k1_tarski('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_111,plain,
    ( k4_xboole_0(k1_tarski('#skF_1'),'#skF_3') != k1_tarski('#skF_1')
    | k4_xboole_0(k2_tarski('#skF_4','#skF_5'),'#skF_6') = k1_tarski('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_81,c_24])).

tff(c_112,plain,(
    k4_xboole_0(k1_tarski('#skF_1'),'#skF_3') != k1_tarski('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_111])).

tff(c_115,plain,(
    r2_hidden('#skF_1','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_29,c_112])).

tff(c_119,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_59,c_115])).

tff(c_120,plain,(
    r2_hidden('#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_79])).

tff(c_10,plain,(
    ! [B_3,C_4,A_2] :
      ( ~ r2_hidden(B_3,C_4)
      | k4_xboole_0(k2_tarski(A_2,B_3),C_4) = k1_tarski(A_2)
      | r2_hidden(A_2,C_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_146,plain,(
    k4_xboole_0(k2_tarski('#skF_1','#skF_2'),'#skF_3') != k1_tarski('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_24])).

tff(c_149,plain,
    ( ~ r2_hidden('#skF_2','#skF_3')
    | r2_hidden('#skF_1','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_146])).

tff(c_152,plain,(
    r2_hidden('#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_120,c_149])).

tff(c_154,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_59,c_152])).

tff(c_155,plain,(
    k4_xboole_0(k2_tarski('#skF_4','#skF_5'),'#skF_6') = k1_tarski('#skF_4') ),
    inference(splitRight,[status(thm)],[c_28])).

tff(c_167,plain,(
    ! [B_22,A_23,C_24] :
      ( B_22 = A_23
      | r2_hidden(B_22,C_24)
      | k4_xboole_0(k2_tarski(A_23,B_22),C_24) != k1_tarski(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_170,plain,
    ( '#skF_5' = '#skF_4'
    | r2_hidden('#skF_5','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_155,c_167])).

tff(c_177,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_39,c_170])).

tff(c_178,plain,
    ( ~ r2_hidden('#skF_1','#skF_3')
    | r2_hidden('#skF_4','#skF_6') ),
    inference(splitRight,[status(thm)],[c_22])).

tff(c_180,plain,(
    ~ r2_hidden('#skF_1','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_178])).

tff(c_179,plain,(
    r2_hidden('#skF_5','#skF_6') ),
    inference(splitRight,[status(thm)],[c_22])).

tff(c_20,plain,
    ( '#skF_2' = '#skF_1'
    | r2_hidden('#skF_2','#skF_3')
    | ~ r2_hidden('#skF_5','#skF_6')
    | r2_hidden('#skF_4','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_200,plain,
    ( '#skF_2' = '#skF_1'
    | r2_hidden('#skF_2','#skF_3')
    | r2_hidden('#skF_4','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_179,c_20])).

tff(c_201,plain,(
    r2_hidden('#skF_4','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_200])).

tff(c_202,plain,(
    k4_xboole_0(k2_tarski('#skF_4','#skF_5'),'#skF_6') = k1_tarski('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_26])).

tff(c_6,plain,(
    ! [A_2,C_4,B_3] :
      ( ~ r2_hidden(A_2,C_4)
      | k4_xboole_0(k2_tarski(A_2,B_3),C_4) != k1_tarski(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_206,plain,(
    ~ r2_hidden('#skF_4','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_202,c_6])).

tff(c_212,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_201,c_206])).

tff(c_214,plain,(
    k4_xboole_0(k2_tarski('#skF_4','#skF_5'),'#skF_6') != k1_tarski('#skF_4') ),
    inference(splitRight,[status(thm)],[c_26])).

tff(c_213,plain,
    ( r2_hidden('#skF_2','#skF_3')
    | '#skF_2' = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_26])).

tff(c_215,plain,(
    '#skF_2' = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_213])).

tff(c_254,plain,
    ( k4_xboole_0(k1_tarski('#skF_1'),'#skF_3') != k1_tarski('#skF_1')
    | k4_xboole_0(k2_tarski('#skF_4','#skF_5'),'#skF_6') = k1_tarski('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_215,c_24])).

tff(c_255,plain,(
    k4_xboole_0(k1_tarski('#skF_1'),'#skF_3') != k1_tarski('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_214,c_254])).

tff(c_258,plain,(
    r2_hidden('#skF_1','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_29,c_255])).

tff(c_262,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_180,c_258])).

tff(c_263,plain,(
    r2_hidden('#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_213])).

tff(c_299,plain,(
    k4_xboole_0(k2_tarski('#skF_1','#skF_2'),'#skF_3') != k1_tarski('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_214,c_24])).

tff(c_302,plain,
    ( ~ r2_hidden('#skF_2','#skF_3')
    | r2_hidden('#skF_1','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_299])).

tff(c_305,plain,(
    r2_hidden('#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_263,c_302])).

tff(c_307,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_180,c_305])).

tff(c_309,plain,(
    ~ r2_hidden('#skF_4','#skF_6') ),
    inference(splitRight,[status(thm)],[c_200])).

tff(c_308,plain,
    ( r2_hidden('#skF_2','#skF_3')
    | '#skF_2' = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_200])).

tff(c_310,plain,(
    '#skF_2' = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_308])).

tff(c_18,plain,
    ( k4_xboole_0(k2_tarski('#skF_1','#skF_2'),'#skF_3') != k1_tarski('#skF_1')
    | ~ r2_hidden('#skF_5','#skF_6')
    | r2_hidden('#skF_4','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_325,plain,
    ( k4_xboole_0(k1_tarski('#skF_1'),'#skF_3') != k1_tarski('#skF_1')
    | r2_hidden('#skF_4','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_179,c_2,c_310,c_18])).

tff(c_326,plain,(
    k4_xboole_0(k1_tarski('#skF_1'),'#skF_3') != k1_tarski('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_309,c_325])).

tff(c_329,plain,(
    r2_hidden('#skF_1','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_29,c_326])).

tff(c_333,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_180,c_329])).

tff(c_334,plain,(
    r2_hidden('#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_308])).

tff(c_347,plain,(
    ! [B_50,C_51,A_52] :
      ( ~ r2_hidden(B_50,C_51)
      | k4_xboole_0(k2_tarski(A_52,B_50),C_51) = k1_tarski(A_52)
      | r2_hidden(A_52,C_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_345,plain,
    ( k4_xboole_0(k2_tarski('#skF_1','#skF_2'),'#skF_3') != k1_tarski('#skF_1')
    | r2_hidden('#skF_4','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_179,c_18])).

tff(c_346,plain,(
    k4_xboole_0(k2_tarski('#skF_1','#skF_2'),'#skF_3') != k1_tarski('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_309,c_345])).

tff(c_353,plain,
    ( ~ r2_hidden('#skF_2','#skF_3')
    | r2_hidden('#skF_1','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_347,c_346])).

tff(c_369,plain,(
    r2_hidden('#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_334,c_353])).

tff(c_371,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_180,c_369])).

tff(c_372,plain,(
    r2_hidden('#skF_4','#skF_6') ),
    inference(splitRight,[status(thm)],[c_178])).

tff(c_373,plain,(
    r2_hidden('#skF_1','#skF_3') ),
    inference(splitRight,[status(thm)],[c_178])).

tff(c_375,plain,(
    k4_xboole_0(k2_tarski('#skF_4','#skF_5'),'#skF_6') = k1_tarski('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_373,c_28])).

tff(c_390,plain,(
    ! [A_55,C_56,B_57] :
      ( ~ r2_hidden(A_55,C_56)
      | k4_xboole_0(k2_tarski(A_55,B_57),C_56) != k1_tarski(A_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_393,plain,(
    ~ r2_hidden('#skF_4','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_375,c_390])).

tff(c_400,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_372,c_393])).

tff(c_401,plain,
    ( ~ r2_hidden('#skF_1','#skF_3')
    | r2_hidden('#skF_4','#skF_6') ),
    inference(splitRight,[status(thm)],[c_16])).

tff(c_407,plain,(
    ~ r2_hidden('#skF_1','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_401])).

tff(c_402,plain,(
    '#skF_5' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_16])).

tff(c_14,plain,
    ( '#skF_2' = '#skF_1'
    | r2_hidden('#skF_2','#skF_3')
    | '#skF_5' != '#skF_4'
    | r2_hidden('#skF_4','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_420,plain,
    ( '#skF_2' = '#skF_1'
    | r2_hidden('#skF_2','#skF_3')
    | r2_hidden('#skF_4','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_402,c_14])).

tff(c_421,plain,(
    r2_hidden('#skF_4','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_420])).

tff(c_433,plain,
    ( '#skF_2' = '#skF_1'
    | r2_hidden('#skF_2','#skF_3')
    | k4_xboole_0(k1_tarski('#skF_4'),'#skF_6') = k1_tarski('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_402,c_26])).

tff(c_434,plain,(
    k4_xboole_0(k1_tarski('#skF_4'),'#skF_6') = k1_tarski('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_433])).

tff(c_422,plain,(
    ! [A_60,C_61,B_62] :
      ( ~ r2_hidden(A_60,C_61)
      | k4_xboole_0(k2_tarski(A_60,B_62),C_61) != k1_tarski(A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_425,plain,(
    ! [A_1,C_61] :
      ( ~ r2_hidden(A_1,C_61)
      | k4_xboole_0(k1_tarski(A_1),C_61) != k1_tarski(A_1) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_422])).

tff(c_438,plain,(
    ~ r2_hidden('#skF_4','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_434,c_425])).

tff(c_450,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_421,c_438])).

tff(c_452,plain,(
    k4_xboole_0(k1_tarski('#skF_4'),'#skF_6') != k1_tarski('#skF_4') ),
    inference(splitRight,[status(thm)],[c_433])).

tff(c_451,plain,
    ( r2_hidden('#skF_2','#skF_3')
    | '#skF_2' = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_433])).

tff(c_453,plain,(
    '#skF_2' = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_451])).

tff(c_492,plain,
    ( k4_xboole_0(k1_tarski('#skF_1'),'#skF_3') != k1_tarski('#skF_1')
    | k4_xboole_0(k1_tarski('#skF_4'),'#skF_6') = k1_tarski('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_402,c_2,c_453,c_24])).

tff(c_493,plain,(
    k4_xboole_0(k1_tarski('#skF_1'),'#skF_3') != k1_tarski('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_452,c_492])).

tff(c_496,plain,(
    r2_hidden('#skF_1','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_29,c_493])).

tff(c_500,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_407,c_496])).

tff(c_501,plain,(
    r2_hidden('#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_451])).

tff(c_537,plain,
    ( k4_xboole_0(k2_tarski('#skF_1','#skF_2'),'#skF_3') != k1_tarski('#skF_1')
    | k4_xboole_0(k1_tarski('#skF_4'),'#skF_6') = k1_tarski('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_402,c_24])).

tff(c_538,plain,(
    k4_xboole_0(k2_tarski('#skF_1','#skF_2'),'#skF_3') != k1_tarski('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_452,c_537])).

tff(c_541,plain,
    ( ~ r2_hidden('#skF_2','#skF_3')
    | r2_hidden('#skF_1','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_538])).

tff(c_544,plain,(
    r2_hidden('#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_501,c_541])).

tff(c_546,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_407,c_544])).

tff(c_548,plain,(
    ~ r2_hidden('#skF_4','#skF_6') ),
    inference(splitRight,[status(thm)],[c_420])).

tff(c_547,plain,
    ( r2_hidden('#skF_2','#skF_3')
    | '#skF_2' = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_420])).

tff(c_549,plain,(
    '#skF_2' = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_547])).

tff(c_12,plain,
    ( k4_xboole_0(k2_tarski('#skF_1','#skF_2'),'#skF_3') != k1_tarski('#skF_1')
    | '#skF_5' != '#skF_4'
    | r2_hidden('#skF_4','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_568,plain,
    ( k4_xboole_0(k1_tarski('#skF_1'),'#skF_3') != k1_tarski('#skF_1')
    | r2_hidden('#skF_4','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_402,c_2,c_549,c_12])).

tff(c_569,plain,(
    k4_xboole_0(k1_tarski('#skF_1'),'#skF_3') != k1_tarski('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_548,c_568])).

tff(c_572,plain,(
    r2_hidden('#skF_1','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_29,c_569])).

tff(c_576,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_407,c_572])).

tff(c_577,plain,(
    r2_hidden('#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_547])).

tff(c_600,plain,(
    ! [B_90,C_91,A_92] :
      ( ~ r2_hidden(B_90,C_91)
      | k4_xboole_0(k2_tarski(A_92,B_90),C_91) = k1_tarski(A_92)
      | r2_hidden(A_92,C_91) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_598,plain,
    ( k4_xboole_0(k2_tarski('#skF_1','#skF_2'),'#skF_3') != k1_tarski('#skF_1')
    | r2_hidden('#skF_4','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_402,c_12])).

tff(c_599,plain,(
    k4_xboole_0(k2_tarski('#skF_1','#skF_2'),'#skF_3') != k1_tarski('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_548,c_598])).

tff(c_606,plain,
    ( ~ r2_hidden('#skF_2','#skF_3')
    | r2_hidden('#skF_1','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_600,c_599])).

tff(c_622,plain,(
    r2_hidden('#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_577,c_606])).

tff(c_624,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_407,c_622])).

tff(c_625,plain,(
    r2_hidden('#skF_4','#skF_6') ),
    inference(splitRight,[status(thm)],[c_401])).

tff(c_626,plain,(
    r2_hidden('#skF_1','#skF_3') ),
    inference(splitRight,[status(thm)],[c_401])).

tff(c_638,plain,(
    k4_xboole_0(k1_tarski('#skF_4'),'#skF_6') = k1_tarski('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_402,c_626,c_28])).

tff(c_653,plain,(
    ! [A_95,C_96,B_97] :
      ( ~ r2_hidden(A_95,C_96)
      | k4_xboole_0(k2_tarski(A_95,B_97),C_96) != k1_tarski(A_95) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_659,plain,(
    ! [A_98,C_99] :
      ( ~ r2_hidden(A_98,C_99)
      | k4_xboole_0(k1_tarski(A_98),C_99) != k1_tarski(A_98) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_653])).

tff(c_662,plain,(
    ~ r2_hidden('#skF_4','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_638,c_659])).

tff(c_669,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_625,c_662])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:11:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.02/1.30  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.02/1.32  
% 2.02/1.32  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.02/1.32  %$ r2_hidden > k4_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.02/1.32  
% 2.02/1.32  %Foreground sorts:
% 2.02/1.32  
% 2.02/1.32  
% 2.02/1.32  %Background operators:
% 2.02/1.32  
% 2.02/1.32  
% 2.02/1.32  %Foreground operators:
% 2.02/1.32  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.02/1.32  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.02/1.32  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.02/1.32  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.02/1.32  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.02/1.32  tff('#skF_5', type, '#skF_5': $i).
% 2.02/1.32  tff('#skF_6', type, '#skF_6': $i).
% 2.02/1.32  tff('#skF_2', type, '#skF_2': $i).
% 2.02/1.32  tff('#skF_3', type, '#skF_3': $i).
% 2.02/1.32  tff('#skF_1', type, '#skF_1': $i).
% 2.02/1.32  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.02/1.32  tff('#skF_4', type, '#skF_4': $i).
% 2.02/1.32  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.02/1.32  
% 2.38/1.34  tff(f_46, negated_conjecture, ~(![A, B, C]: ((k4_xboole_0(k2_tarski(A, B), C) = k1_tarski(A)) <=> (~r2_hidden(A, C) & (r2_hidden(B, C) | (A = B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_zfmisc_1)).
% 2.38/1.34  tff(f_27, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 2.38/1.34  tff(f_36, axiom, (![A, B, C]: ((k4_xboole_0(k2_tarski(A, B), C) = k1_tarski(A)) <=> (~r2_hidden(A, C) & (r2_hidden(B, C) | (A = B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l38_zfmisc_1)).
% 2.38/1.34  tff(c_22, plain, (~r2_hidden('#skF_1', '#skF_3') | ~r2_hidden('#skF_5', '#skF_6') | r2_hidden('#skF_4', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.38/1.34  tff(c_40, plain, (~r2_hidden('#skF_5', '#skF_6')), inference(splitLeft, [status(thm)], [c_22])).
% 2.38/1.34  tff(c_16, plain, (~r2_hidden('#skF_1', '#skF_3') | '#skF_5'!='#skF_4' | r2_hidden('#skF_4', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.38/1.34  tff(c_39, plain, ('#skF_5'!='#skF_4'), inference(splitLeft, [status(thm)], [c_16])).
% 2.38/1.34  tff(c_28, plain, (~r2_hidden('#skF_1', '#skF_3') | k4_xboole_0(k2_tarski('#skF_4', '#skF_5'), '#skF_6')=k1_tarski('#skF_4')), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.38/1.34  tff(c_59, plain, (~r2_hidden('#skF_1', '#skF_3')), inference(splitLeft, [status(thm)], [c_28])).
% 2.38/1.34  tff(c_2, plain, (![A_1]: (k2_tarski(A_1, A_1)=k1_tarski(A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.38/1.34  tff(c_8, plain, (![B_3, C_4]: (k4_xboole_0(k2_tarski(B_3, B_3), C_4)=k1_tarski(B_3) | r2_hidden(B_3, C_4))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.38/1.34  tff(c_29, plain, (![B_3, C_4]: (k4_xboole_0(k1_tarski(B_3), C_4)=k1_tarski(B_3) | r2_hidden(B_3, C_4))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_8])).
% 2.38/1.34  tff(c_26, plain, ('#skF_2'='#skF_1' | r2_hidden('#skF_2', '#skF_3') | k4_xboole_0(k2_tarski('#skF_4', '#skF_5'), '#skF_6')=k1_tarski('#skF_4')), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.38/1.34  tff(c_65, plain, (k4_xboole_0(k2_tarski('#skF_4', '#skF_5'), '#skF_6')=k1_tarski('#skF_4')), inference(splitLeft, [status(thm)], [c_26])).
% 2.38/1.34  tff(c_4, plain, (![B_3, A_2, C_4]: (B_3=A_2 | r2_hidden(B_3, C_4) | k4_xboole_0(k2_tarski(A_2, B_3), C_4)!=k1_tarski(A_2))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.38/1.34  tff(c_69, plain, ('#skF_5'='#skF_4' | r2_hidden('#skF_5', '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_65, c_4])).
% 2.38/1.34  tff(c_78, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40, c_39, c_69])).
% 2.38/1.34  tff(c_80, plain, (k4_xboole_0(k2_tarski('#skF_4', '#skF_5'), '#skF_6')!=k1_tarski('#skF_4')), inference(splitRight, [status(thm)], [c_26])).
% 2.38/1.34  tff(c_79, plain, (r2_hidden('#skF_2', '#skF_3') | '#skF_2'='#skF_1'), inference(splitRight, [status(thm)], [c_26])).
% 2.38/1.34  tff(c_81, plain, ('#skF_2'='#skF_1'), inference(splitLeft, [status(thm)], [c_79])).
% 2.38/1.34  tff(c_24, plain, (k4_xboole_0(k2_tarski('#skF_1', '#skF_2'), '#skF_3')!=k1_tarski('#skF_1') | k4_xboole_0(k2_tarski('#skF_4', '#skF_5'), '#skF_6')=k1_tarski('#skF_4')), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.38/1.34  tff(c_111, plain, (k4_xboole_0(k1_tarski('#skF_1'), '#skF_3')!=k1_tarski('#skF_1') | k4_xboole_0(k2_tarski('#skF_4', '#skF_5'), '#skF_6')=k1_tarski('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_81, c_24])).
% 2.38/1.34  tff(c_112, plain, (k4_xboole_0(k1_tarski('#skF_1'), '#skF_3')!=k1_tarski('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_80, c_111])).
% 2.38/1.34  tff(c_115, plain, (r2_hidden('#skF_1', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_29, c_112])).
% 2.38/1.34  tff(c_119, plain, $false, inference(negUnitSimplification, [status(thm)], [c_59, c_115])).
% 2.38/1.34  tff(c_120, plain, (r2_hidden('#skF_2', '#skF_3')), inference(splitRight, [status(thm)], [c_79])).
% 2.38/1.34  tff(c_10, plain, (![B_3, C_4, A_2]: (~r2_hidden(B_3, C_4) | k4_xboole_0(k2_tarski(A_2, B_3), C_4)=k1_tarski(A_2) | r2_hidden(A_2, C_4))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.38/1.34  tff(c_146, plain, (k4_xboole_0(k2_tarski('#skF_1', '#skF_2'), '#skF_3')!=k1_tarski('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_80, c_24])).
% 2.38/1.34  tff(c_149, plain, (~r2_hidden('#skF_2', '#skF_3') | r2_hidden('#skF_1', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_10, c_146])).
% 2.38/1.34  tff(c_152, plain, (r2_hidden('#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_120, c_149])).
% 2.38/1.34  tff(c_154, plain, $false, inference(negUnitSimplification, [status(thm)], [c_59, c_152])).
% 2.38/1.34  tff(c_155, plain, (k4_xboole_0(k2_tarski('#skF_4', '#skF_5'), '#skF_6')=k1_tarski('#skF_4')), inference(splitRight, [status(thm)], [c_28])).
% 2.38/1.34  tff(c_167, plain, (![B_22, A_23, C_24]: (B_22=A_23 | r2_hidden(B_22, C_24) | k4_xboole_0(k2_tarski(A_23, B_22), C_24)!=k1_tarski(A_23))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.38/1.34  tff(c_170, plain, ('#skF_5'='#skF_4' | r2_hidden('#skF_5', '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_155, c_167])).
% 2.38/1.34  tff(c_177, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40, c_39, c_170])).
% 2.38/1.34  tff(c_178, plain, (~r2_hidden('#skF_1', '#skF_3') | r2_hidden('#skF_4', '#skF_6')), inference(splitRight, [status(thm)], [c_22])).
% 2.38/1.34  tff(c_180, plain, (~r2_hidden('#skF_1', '#skF_3')), inference(splitLeft, [status(thm)], [c_178])).
% 2.38/1.34  tff(c_179, plain, (r2_hidden('#skF_5', '#skF_6')), inference(splitRight, [status(thm)], [c_22])).
% 2.38/1.34  tff(c_20, plain, ('#skF_2'='#skF_1' | r2_hidden('#skF_2', '#skF_3') | ~r2_hidden('#skF_5', '#skF_6') | r2_hidden('#skF_4', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.38/1.34  tff(c_200, plain, ('#skF_2'='#skF_1' | r2_hidden('#skF_2', '#skF_3') | r2_hidden('#skF_4', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_179, c_20])).
% 2.38/1.34  tff(c_201, plain, (r2_hidden('#skF_4', '#skF_6')), inference(splitLeft, [status(thm)], [c_200])).
% 2.38/1.34  tff(c_202, plain, (k4_xboole_0(k2_tarski('#skF_4', '#skF_5'), '#skF_6')=k1_tarski('#skF_4')), inference(splitLeft, [status(thm)], [c_26])).
% 2.38/1.34  tff(c_6, plain, (![A_2, C_4, B_3]: (~r2_hidden(A_2, C_4) | k4_xboole_0(k2_tarski(A_2, B_3), C_4)!=k1_tarski(A_2))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.38/1.34  tff(c_206, plain, (~r2_hidden('#skF_4', '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_202, c_6])).
% 2.38/1.34  tff(c_212, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_201, c_206])).
% 2.38/1.34  tff(c_214, plain, (k4_xboole_0(k2_tarski('#skF_4', '#skF_5'), '#skF_6')!=k1_tarski('#skF_4')), inference(splitRight, [status(thm)], [c_26])).
% 2.38/1.34  tff(c_213, plain, (r2_hidden('#skF_2', '#skF_3') | '#skF_2'='#skF_1'), inference(splitRight, [status(thm)], [c_26])).
% 2.38/1.34  tff(c_215, plain, ('#skF_2'='#skF_1'), inference(splitLeft, [status(thm)], [c_213])).
% 2.38/1.34  tff(c_254, plain, (k4_xboole_0(k1_tarski('#skF_1'), '#skF_3')!=k1_tarski('#skF_1') | k4_xboole_0(k2_tarski('#skF_4', '#skF_5'), '#skF_6')=k1_tarski('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_215, c_24])).
% 2.38/1.34  tff(c_255, plain, (k4_xboole_0(k1_tarski('#skF_1'), '#skF_3')!=k1_tarski('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_214, c_254])).
% 2.38/1.34  tff(c_258, plain, (r2_hidden('#skF_1', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_29, c_255])).
% 2.38/1.34  tff(c_262, plain, $false, inference(negUnitSimplification, [status(thm)], [c_180, c_258])).
% 2.38/1.34  tff(c_263, plain, (r2_hidden('#skF_2', '#skF_3')), inference(splitRight, [status(thm)], [c_213])).
% 2.38/1.34  tff(c_299, plain, (k4_xboole_0(k2_tarski('#skF_1', '#skF_2'), '#skF_3')!=k1_tarski('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_214, c_24])).
% 2.38/1.34  tff(c_302, plain, (~r2_hidden('#skF_2', '#skF_3') | r2_hidden('#skF_1', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_10, c_299])).
% 2.38/1.34  tff(c_305, plain, (r2_hidden('#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_263, c_302])).
% 2.38/1.34  tff(c_307, plain, $false, inference(negUnitSimplification, [status(thm)], [c_180, c_305])).
% 2.38/1.34  tff(c_309, plain, (~r2_hidden('#skF_4', '#skF_6')), inference(splitRight, [status(thm)], [c_200])).
% 2.38/1.34  tff(c_308, plain, (r2_hidden('#skF_2', '#skF_3') | '#skF_2'='#skF_1'), inference(splitRight, [status(thm)], [c_200])).
% 2.38/1.34  tff(c_310, plain, ('#skF_2'='#skF_1'), inference(splitLeft, [status(thm)], [c_308])).
% 2.38/1.34  tff(c_18, plain, (k4_xboole_0(k2_tarski('#skF_1', '#skF_2'), '#skF_3')!=k1_tarski('#skF_1') | ~r2_hidden('#skF_5', '#skF_6') | r2_hidden('#skF_4', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.38/1.34  tff(c_325, plain, (k4_xboole_0(k1_tarski('#skF_1'), '#skF_3')!=k1_tarski('#skF_1') | r2_hidden('#skF_4', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_179, c_2, c_310, c_18])).
% 2.38/1.34  tff(c_326, plain, (k4_xboole_0(k1_tarski('#skF_1'), '#skF_3')!=k1_tarski('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_309, c_325])).
% 2.38/1.34  tff(c_329, plain, (r2_hidden('#skF_1', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_29, c_326])).
% 2.38/1.34  tff(c_333, plain, $false, inference(negUnitSimplification, [status(thm)], [c_180, c_329])).
% 2.38/1.34  tff(c_334, plain, (r2_hidden('#skF_2', '#skF_3')), inference(splitRight, [status(thm)], [c_308])).
% 2.38/1.34  tff(c_347, plain, (![B_50, C_51, A_52]: (~r2_hidden(B_50, C_51) | k4_xboole_0(k2_tarski(A_52, B_50), C_51)=k1_tarski(A_52) | r2_hidden(A_52, C_51))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.38/1.34  tff(c_345, plain, (k4_xboole_0(k2_tarski('#skF_1', '#skF_2'), '#skF_3')!=k1_tarski('#skF_1') | r2_hidden('#skF_4', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_179, c_18])).
% 2.38/1.34  tff(c_346, plain, (k4_xboole_0(k2_tarski('#skF_1', '#skF_2'), '#skF_3')!=k1_tarski('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_309, c_345])).
% 2.38/1.34  tff(c_353, plain, (~r2_hidden('#skF_2', '#skF_3') | r2_hidden('#skF_1', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_347, c_346])).
% 2.38/1.34  tff(c_369, plain, (r2_hidden('#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_334, c_353])).
% 2.38/1.34  tff(c_371, plain, $false, inference(negUnitSimplification, [status(thm)], [c_180, c_369])).
% 2.38/1.34  tff(c_372, plain, (r2_hidden('#skF_4', '#skF_6')), inference(splitRight, [status(thm)], [c_178])).
% 2.38/1.34  tff(c_373, plain, (r2_hidden('#skF_1', '#skF_3')), inference(splitRight, [status(thm)], [c_178])).
% 2.38/1.34  tff(c_375, plain, (k4_xboole_0(k2_tarski('#skF_4', '#skF_5'), '#skF_6')=k1_tarski('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_373, c_28])).
% 2.38/1.34  tff(c_390, plain, (![A_55, C_56, B_57]: (~r2_hidden(A_55, C_56) | k4_xboole_0(k2_tarski(A_55, B_57), C_56)!=k1_tarski(A_55))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.38/1.34  tff(c_393, plain, (~r2_hidden('#skF_4', '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_375, c_390])).
% 2.38/1.34  tff(c_400, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_372, c_393])).
% 2.38/1.34  tff(c_401, plain, (~r2_hidden('#skF_1', '#skF_3') | r2_hidden('#skF_4', '#skF_6')), inference(splitRight, [status(thm)], [c_16])).
% 2.38/1.34  tff(c_407, plain, (~r2_hidden('#skF_1', '#skF_3')), inference(splitLeft, [status(thm)], [c_401])).
% 2.38/1.34  tff(c_402, plain, ('#skF_5'='#skF_4'), inference(splitRight, [status(thm)], [c_16])).
% 2.38/1.34  tff(c_14, plain, ('#skF_2'='#skF_1' | r2_hidden('#skF_2', '#skF_3') | '#skF_5'!='#skF_4' | r2_hidden('#skF_4', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.38/1.34  tff(c_420, plain, ('#skF_2'='#skF_1' | r2_hidden('#skF_2', '#skF_3') | r2_hidden('#skF_4', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_402, c_14])).
% 2.38/1.34  tff(c_421, plain, (r2_hidden('#skF_4', '#skF_6')), inference(splitLeft, [status(thm)], [c_420])).
% 2.38/1.34  tff(c_433, plain, ('#skF_2'='#skF_1' | r2_hidden('#skF_2', '#skF_3') | k4_xboole_0(k1_tarski('#skF_4'), '#skF_6')=k1_tarski('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_402, c_26])).
% 2.38/1.34  tff(c_434, plain, (k4_xboole_0(k1_tarski('#skF_4'), '#skF_6')=k1_tarski('#skF_4')), inference(splitLeft, [status(thm)], [c_433])).
% 2.38/1.34  tff(c_422, plain, (![A_60, C_61, B_62]: (~r2_hidden(A_60, C_61) | k4_xboole_0(k2_tarski(A_60, B_62), C_61)!=k1_tarski(A_60))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.38/1.34  tff(c_425, plain, (![A_1, C_61]: (~r2_hidden(A_1, C_61) | k4_xboole_0(k1_tarski(A_1), C_61)!=k1_tarski(A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_422])).
% 2.38/1.34  tff(c_438, plain, (~r2_hidden('#skF_4', '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_434, c_425])).
% 2.38/1.34  tff(c_450, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_421, c_438])).
% 2.38/1.34  tff(c_452, plain, (k4_xboole_0(k1_tarski('#skF_4'), '#skF_6')!=k1_tarski('#skF_4')), inference(splitRight, [status(thm)], [c_433])).
% 2.38/1.34  tff(c_451, plain, (r2_hidden('#skF_2', '#skF_3') | '#skF_2'='#skF_1'), inference(splitRight, [status(thm)], [c_433])).
% 2.38/1.34  tff(c_453, plain, ('#skF_2'='#skF_1'), inference(splitLeft, [status(thm)], [c_451])).
% 2.38/1.34  tff(c_492, plain, (k4_xboole_0(k1_tarski('#skF_1'), '#skF_3')!=k1_tarski('#skF_1') | k4_xboole_0(k1_tarski('#skF_4'), '#skF_6')=k1_tarski('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_402, c_2, c_453, c_24])).
% 2.38/1.34  tff(c_493, plain, (k4_xboole_0(k1_tarski('#skF_1'), '#skF_3')!=k1_tarski('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_452, c_492])).
% 2.38/1.34  tff(c_496, plain, (r2_hidden('#skF_1', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_29, c_493])).
% 2.38/1.34  tff(c_500, plain, $false, inference(negUnitSimplification, [status(thm)], [c_407, c_496])).
% 2.38/1.34  tff(c_501, plain, (r2_hidden('#skF_2', '#skF_3')), inference(splitRight, [status(thm)], [c_451])).
% 2.38/1.34  tff(c_537, plain, (k4_xboole_0(k2_tarski('#skF_1', '#skF_2'), '#skF_3')!=k1_tarski('#skF_1') | k4_xboole_0(k1_tarski('#skF_4'), '#skF_6')=k1_tarski('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_402, c_24])).
% 2.38/1.34  tff(c_538, plain, (k4_xboole_0(k2_tarski('#skF_1', '#skF_2'), '#skF_3')!=k1_tarski('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_452, c_537])).
% 2.38/1.34  tff(c_541, plain, (~r2_hidden('#skF_2', '#skF_3') | r2_hidden('#skF_1', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_10, c_538])).
% 2.38/1.34  tff(c_544, plain, (r2_hidden('#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_501, c_541])).
% 2.38/1.34  tff(c_546, plain, $false, inference(negUnitSimplification, [status(thm)], [c_407, c_544])).
% 2.38/1.34  tff(c_548, plain, (~r2_hidden('#skF_4', '#skF_6')), inference(splitRight, [status(thm)], [c_420])).
% 2.38/1.34  tff(c_547, plain, (r2_hidden('#skF_2', '#skF_3') | '#skF_2'='#skF_1'), inference(splitRight, [status(thm)], [c_420])).
% 2.38/1.34  tff(c_549, plain, ('#skF_2'='#skF_1'), inference(splitLeft, [status(thm)], [c_547])).
% 2.38/1.34  tff(c_12, plain, (k4_xboole_0(k2_tarski('#skF_1', '#skF_2'), '#skF_3')!=k1_tarski('#skF_1') | '#skF_5'!='#skF_4' | r2_hidden('#skF_4', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.38/1.34  tff(c_568, plain, (k4_xboole_0(k1_tarski('#skF_1'), '#skF_3')!=k1_tarski('#skF_1') | r2_hidden('#skF_4', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_402, c_2, c_549, c_12])).
% 2.38/1.34  tff(c_569, plain, (k4_xboole_0(k1_tarski('#skF_1'), '#skF_3')!=k1_tarski('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_548, c_568])).
% 2.38/1.34  tff(c_572, plain, (r2_hidden('#skF_1', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_29, c_569])).
% 2.38/1.34  tff(c_576, plain, $false, inference(negUnitSimplification, [status(thm)], [c_407, c_572])).
% 2.38/1.34  tff(c_577, plain, (r2_hidden('#skF_2', '#skF_3')), inference(splitRight, [status(thm)], [c_547])).
% 2.38/1.34  tff(c_600, plain, (![B_90, C_91, A_92]: (~r2_hidden(B_90, C_91) | k4_xboole_0(k2_tarski(A_92, B_90), C_91)=k1_tarski(A_92) | r2_hidden(A_92, C_91))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.38/1.34  tff(c_598, plain, (k4_xboole_0(k2_tarski('#skF_1', '#skF_2'), '#skF_3')!=k1_tarski('#skF_1') | r2_hidden('#skF_4', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_402, c_12])).
% 2.38/1.34  tff(c_599, plain, (k4_xboole_0(k2_tarski('#skF_1', '#skF_2'), '#skF_3')!=k1_tarski('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_548, c_598])).
% 2.38/1.34  tff(c_606, plain, (~r2_hidden('#skF_2', '#skF_3') | r2_hidden('#skF_1', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_600, c_599])).
% 2.38/1.34  tff(c_622, plain, (r2_hidden('#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_577, c_606])).
% 2.38/1.34  tff(c_624, plain, $false, inference(negUnitSimplification, [status(thm)], [c_407, c_622])).
% 2.38/1.34  tff(c_625, plain, (r2_hidden('#skF_4', '#skF_6')), inference(splitRight, [status(thm)], [c_401])).
% 2.38/1.34  tff(c_626, plain, (r2_hidden('#skF_1', '#skF_3')), inference(splitRight, [status(thm)], [c_401])).
% 2.38/1.34  tff(c_638, plain, (k4_xboole_0(k1_tarski('#skF_4'), '#skF_6')=k1_tarski('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_402, c_626, c_28])).
% 2.38/1.34  tff(c_653, plain, (![A_95, C_96, B_97]: (~r2_hidden(A_95, C_96) | k4_xboole_0(k2_tarski(A_95, B_97), C_96)!=k1_tarski(A_95))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.38/1.34  tff(c_659, plain, (![A_98, C_99]: (~r2_hidden(A_98, C_99) | k4_xboole_0(k1_tarski(A_98), C_99)!=k1_tarski(A_98))), inference(superposition, [status(thm), theory('equality')], [c_2, c_653])).
% 2.38/1.34  tff(c_662, plain, (~r2_hidden('#skF_4', '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_638, c_659])).
% 2.38/1.34  tff(c_669, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_625, c_662])).
% 2.38/1.34  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.38/1.34  
% 2.38/1.34  Inference rules
% 2.38/1.34  ----------------------
% 2.38/1.34  #Ref     : 0
% 2.38/1.34  #Sup     : 126
% 2.38/1.34  #Fact    : 0
% 2.38/1.34  #Define  : 0
% 2.38/1.34  #Split   : 15
% 2.38/1.34  #Chain   : 0
% 2.38/1.34  #Close   : 0
% 2.38/1.34  
% 2.38/1.34  Ordering : KBO
% 2.38/1.34  
% 2.38/1.34  Simplification rules
% 2.38/1.34  ----------------------
% 2.38/1.34  #Subsume      : 26
% 2.38/1.34  #Demod        : 98
% 2.38/1.34  #Tautology    : 92
% 2.38/1.34  #SimpNegUnit  : 31
% 2.38/1.34  #BackRed      : 0
% 2.38/1.34  
% 2.38/1.34  #Partial instantiations: 0
% 2.38/1.34  #Strategies tried      : 1
% 2.38/1.34  
% 2.38/1.34  Timing (in seconds)
% 2.38/1.34  ----------------------
% 2.38/1.35  Preprocessing        : 0.28
% 2.38/1.35  Parsing              : 0.14
% 2.38/1.35  CNF conversion       : 0.02
% 2.38/1.35  Main loop            : 0.29
% 2.38/1.35  Inferencing          : 0.11
% 2.38/1.35  Reduction            : 0.08
% 2.38/1.35  Demodulation         : 0.06
% 2.38/1.35  BG Simplification    : 0.02
% 2.38/1.35  Subsumption          : 0.05
% 2.38/1.35  Abstraction          : 0.02
% 2.38/1.35  MUC search           : 0.00
% 2.38/1.35  Cooper               : 0.00
% 2.38/1.35  Total                : 0.62
% 2.38/1.35  Index Insertion      : 0.00
% 2.38/1.35  Index Deletion       : 0.00
% 2.38/1.35  Index Matching       : 0.00
% 2.38/1.35  BG Taut test         : 0.00
%------------------------------------------------------------------------------

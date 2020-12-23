%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0273+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:36:01 EST 2020

% Result     : Theorem 2.17s
% Output     : CNFRefutation 2.36s
% Verified   : 
% Statistics : Number of formulae       :  133 ( 395 expanded)
%              Number of leaves         :   15 ( 117 expanded)
%              Depth                    :    9
%              Number of atoms          :  186 ( 947 expanded)
%              Number of equality atoms :   76 ( 411 expanded)
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

tff(f_43,negated_conjecture,(
    ~ ! [A,B,C] :
        ( k4_xboole_0(k2_tarski(A,B),C) = k1_tarski(A)
      <=> ( ~ r2_hidden(A,C)
          & ( r2_hidden(B,C)
            | A = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_zfmisc_1)).

tff(f_33,axiom,(
    ! [A,B,C] :
      ( k4_xboole_0(k2_tarski(A,B),C) = k1_tarski(A)
    <=> ( ~ r2_hidden(A,C)
        & ( r2_hidden(B,C)
          | A = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l38_zfmisc_1)).

tff(c_20,plain,
    ( ~ r2_hidden('#skF_1','#skF_3')
    | ~ r2_hidden('#skF_5','#skF_6')
    | r2_hidden('#skF_4','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_28,plain,(
    ~ r2_hidden('#skF_5','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_20])).

tff(c_14,plain,
    ( ~ r2_hidden('#skF_1','#skF_3')
    | '#skF_5' != '#skF_4'
    | r2_hidden('#skF_4','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_27,plain,(
    '#skF_5' != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_14])).

tff(c_26,plain,
    ( ~ r2_hidden('#skF_1','#skF_3')
    | k4_xboole_0(k2_tarski('#skF_4','#skF_5'),'#skF_6') = k1_tarski('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_43,plain,(
    ~ r2_hidden('#skF_1','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_26])).

tff(c_6,plain,(
    ! [B_2,C_3] :
      ( k4_xboole_0(k2_tarski(B_2,B_2),C_3) = k1_tarski(B_2)
      | r2_hidden(B_2,C_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_24,plain,
    ( '#skF_2' = '#skF_1'
    | r2_hidden('#skF_2','#skF_3')
    | k4_xboole_0(k2_tarski('#skF_4','#skF_5'),'#skF_6') = k1_tarski('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_50,plain,(
    k4_xboole_0(k2_tarski('#skF_4','#skF_5'),'#skF_6') = k1_tarski('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_24])).

tff(c_2,plain,(
    ! [B_2,A_1,C_3] :
      ( B_2 = A_1
      | r2_hidden(B_2,C_3)
      | k4_xboole_0(k2_tarski(A_1,B_2),C_3) != k1_tarski(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_54,plain,
    ( '#skF_5' = '#skF_4'
    | r2_hidden('#skF_5','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_2])).

tff(c_63,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_27,c_54])).

tff(c_65,plain,(
    k4_xboole_0(k2_tarski('#skF_4','#skF_5'),'#skF_6') != k1_tarski('#skF_4') ),
    inference(splitRight,[status(thm)],[c_24])).

tff(c_64,plain,
    ( r2_hidden('#skF_2','#skF_3')
    | '#skF_2' = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_24])).

tff(c_66,plain,(
    '#skF_2' = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_64])).

tff(c_22,plain,
    ( k4_xboole_0(k2_tarski('#skF_1','#skF_2'),'#skF_3') != k1_tarski('#skF_1')
    | k4_xboole_0(k2_tarski('#skF_4','#skF_5'),'#skF_6') = k1_tarski('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_102,plain,
    ( k4_xboole_0(k2_tarski('#skF_1','#skF_1'),'#skF_3') != k1_tarski('#skF_1')
    | k4_xboole_0(k2_tarski('#skF_4','#skF_5'),'#skF_6') = k1_tarski('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_22])).

tff(c_103,plain,(
    k4_xboole_0(k2_tarski('#skF_1','#skF_1'),'#skF_3') != k1_tarski('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_65,c_102])).

tff(c_109,plain,(
    r2_hidden('#skF_1','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_103])).

tff(c_115,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_43,c_109])).

tff(c_116,plain,(
    r2_hidden('#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_8,plain,(
    ! [B_2,C_3,A_1] :
      ( ~ r2_hidden(B_2,C_3)
      | k4_xboole_0(k2_tarski(A_1,B_2),C_3) = k1_tarski(A_1)
      | r2_hidden(A_1,C_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_148,plain,(
    k4_xboole_0(k2_tarski('#skF_1','#skF_2'),'#skF_3') != k1_tarski('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_65,c_22])).

tff(c_151,plain,
    ( ~ r2_hidden('#skF_2','#skF_3')
    | r2_hidden('#skF_1','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_148])).

tff(c_154,plain,(
    r2_hidden('#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_116,c_151])).

tff(c_156,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_43,c_154])).

tff(c_157,plain,(
    k4_xboole_0(k2_tarski('#skF_4','#skF_5'),'#skF_6') = k1_tarski('#skF_4') ),
    inference(splitRight,[status(thm)],[c_26])).

tff(c_169,plain,(
    ! [B_18,A_19,C_20] :
      ( B_18 = A_19
      | r2_hidden(B_18,C_20)
      | k4_xboole_0(k2_tarski(A_19,B_18),C_20) != k1_tarski(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_172,plain,
    ( '#skF_5' = '#skF_4'
    | r2_hidden('#skF_5','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_157,c_169])).

tff(c_179,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_27,c_172])).

tff(c_180,plain,
    ( ~ r2_hidden('#skF_1','#skF_3')
    | r2_hidden('#skF_4','#skF_6') ),
    inference(splitRight,[status(thm)],[c_20])).

tff(c_182,plain,(
    ~ r2_hidden('#skF_1','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_180])).

tff(c_181,plain,(
    r2_hidden('#skF_5','#skF_6') ),
    inference(splitRight,[status(thm)],[c_20])).

tff(c_18,plain,
    ( '#skF_2' = '#skF_1'
    | r2_hidden('#skF_2','#skF_3')
    | ~ r2_hidden('#skF_5','#skF_6')
    | r2_hidden('#skF_4','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_198,plain,
    ( '#skF_2' = '#skF_1'
    | r2_hidden('#skF_2','#skF_3')
    | r2_hidden('#skF_4','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_181,c_18])).

tff(c_199,plain,(
    r2_hidden('#skF_4','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_198])).

tff(c_200,plain,(
    k4_xboole_0(k2_tarski('#skF_4','#skF_5'),'#skF_6') = k1_tarski('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_24])).

tff(c_4,plain,(
    ! [A_1,C_3,B_2] :
      ( ~ r2_hidden(A_1,C_3)
      | k4_xboole_0(k2_tarski(A_1,B_2),C_3) != k1_tarski(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_204,plain,(
    ~ r2_hidden('#skF_4','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_200,c_4])).

tff(c_210,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_199,c_204])).

tff(c_212,plain,(
    k4_xboole_0(k2_tarski('#skF_4','#skF_5'),'#skF_6') != k1_tarski('#skF_4') ),
    inference(splitRight,[status(thm)],[c_24])).

tff(c_211,plain,
    ( r2_hidden('#skF_2','#skF_3')
    | '#skF_2' = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_24])).

tff(c_213,plain,(
    '#skF_2' = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_211])).

tff(c_227,plain,
    ( k4_xboole_0(k2_tarski('#skF_1','#skF_1'),'#skF_3') != k1_tarski('#skF_1')
    | k4_xboole_0(k2_tarski('#skF_4','#skF_5'),'#skF_6') = k1_tarski('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_213,c_22])).

tff(c_228,plain,(
    k4_xboole_0(k2_tarski('#skF_1','#skF_1'),'#skF_3') != k1_tarski('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_212,c_227])).

tff(c_231,plain,(
    r2_hidden('#skF_1','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_228])).

tff(c_235,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_182,c_231])).

tff(c_236,plain,(
    r2_hidden('#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_211])).

tff(c_279,plain,(
    k4_xboole_0(k2_tarski('#skF_1','#skF_2'),'#skF_3') != k1_tarski('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_212,c_22])).

tff(c_282,plain,
    ( ~ r2_hidden('#skF_2','#skF_3')
    | r2_hidden('#skF_1','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_279])).

tff(c_285,plain,(
    r2_hidden('#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_236,c_282])).

tff(c_287,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_182,c_285])).

tff(c_289,plain,(
    ~ r2_hidden('#skF_4','#skF_6') ),
    inference(splitRight,[status(thm)],[c_198])).

tff(c_288,plain,
    ( r2_hidden('#skF_2','#skF_3')
    | '#skF_2' = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_198])).

tff(c_291,plain,(
    '#skF_2' = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_288])).

tff(c_16,plain,
    ( k4_xboole_0(k2_tarski('#skF_1','#skF_2'),'#skF_3') != k1_tarski('#skF_1')
    | ~ r2_hidden('#skF_5','#skF_6')
    | r2_hidden('#skF_4','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_359,plain,
    ( k4_xboole_0(k2_tarski('#skF_1','#skF_1'),'#skF_3') != k1_tarski('#skF_1')
    | r2_hidden('#skF_4','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_181,c_291,c_16])).

tff(c_360,plain,(
    k4_xboole_0(k2_tarski('#skF_1','#skF_1'),'#skF_3') != k1_tarski('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_289,c_359])).

tff(c_366,plain,(
    r2_hidden('#skF_1','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_360])).

tff(c_372,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_182,c_366])).

tff(c_373,plain,(
    r2_hidden('#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_288])).

tff(c_399,plain,(
    ! [B_44,C_45,A_46] :
      ( ~ r2_hidden(B_44,C_45)
      | k4_xboole_0(k2_tarski(A_46,B_44),C_45) = k1_tarski(A_46)
      | r2_hidden(A_46,C_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_397,plain,
    ( k4_xboole_0(k2_tarski('#skF_1','#skF_2'),'#skF_3') != k1_tarski('#skF_1')
    | r2_hidden('#skF_4','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_181,c_16])).

tff(c_398,plain,(
    k4_xboole_0(k2_tarski('#skF_1','#skF_2'),'#skF_3') != k1_tarski('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_289,c_397])).

tff(c_405,plain,
    ( ~ r2_hidden('#skF_2','#skF_3')
    | r2_hidden('#skF_1','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_399,c_398])).

tff(c_431,plain,(
    r2_hidden('#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_373,c_405])).

tff(c_433,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_182,c_431])).

tff(c_434,plain,(
    r2_hidden('#skF_4','#skF_6') ),
    inference(splitRight,[status(thm)],[c_180])).

tff(c_435,plain,(
    r2_hidden('#skF_1','#skF_3') ),
    inference(splitRight,[status(thm)],[c_180])).

tff(c_438,plain,(
    k4_xboole_0(k2_tarski('#skF_4','#skF_5'),'#skF_6') = k1_tarski('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_435,c_26])).

tff(c_443,plain,(
    ! [A_47,C_48,B_49] :
      ( ~ r2_hidden(A_47,C_48)
      | k4_xboole_0(k2_tarski(A_47,B_49),C_48) != k1_tarski(A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_446,plain,(
    ~ r2_hidden('#skF_4','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_438,c_443])).

tff(c_450,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_434,c_446])).

tff(c_452,plain,(
    '#skF_5' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_14])).

tff(c_453,plain,(
    ~ r2_hidden('#skF_5','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_20])).

tff(c_458,plain,(
    ~ r2_hidden('#skF_4','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_452,c_453])).

tff(c_451,plain,
    ( ~ r2_hidden('#skF_1','#skF_3')
    | r2_hidden('#skF_4','#skF_6') ),
    inference(splitRight,[status(thm)],[c_14])).

tff(c_459,plain,(
    ~ r2_hidden('#skF_1','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_458,c_451])).

tff(c_12,plain,
    ( '#skF_2' = '#skF_1'
    | r2_hidden('#skF_2','#skF_3')
    | '#skF_5' != '#skF_4'
    | r2_hidden('#skF_4','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_470,plain,
    ( '#skF_2' = '#skF_1'
    | r2_hidden('#skF_2','#skF_3')
    | r2_hidden('#skF_4','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_452,c_12])).

tff(c_471,plain,
    ( '#skF_2' = '#skF_1'
    | r2_hidden('#skF_2','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_458,c_470])).

tff(c_472,plain,(
    r2_hidden('#skF_2','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_471])).

tff(c_493,plain,(
    ! [B_58,C_59,A_60] :
      ( ~ r2_hidden(B_58,C_59)
      | k4_xboole_0(k2_tarski(A_60,B_58),C_59) = k1_tarski(A_60)
      | r2_hidden(A_60,C_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_10,plain,
    ( k4_xboole_0(k2_tarski('#skF_1','#skF_2'),'#skF_3') != k1_tarski('#skF_1')
    | '#skF_5' != '#skF_4'
    | r2_hidden('#skF_4','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_483,plain,
    ( k4_xboole_0(k2_tarski('#skF_1','#skF_2'),'#skF_3') != k1_tarski('#skF_1')
    | r2_hidden('#skF_4','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_452,c_10])).

tff(c_484,plain,(
    k4_xboole_0(k2_tarski('#skF_1','#skF_2'),'#skF_3') != k1_tarski('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_458,c_483])).

tff(c_502,plain,
    ( ~ r2_hidden('#skF_2','#skF_3')
    | r2_hidden('#skF_1','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_493,c_484])).

tff(c_520,plain,(
    r2_hidden('#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_472,c_502])).

tff(c_522,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_459,c_520])).

tff(c_523,plain,(
    '#skF_2' = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_471])).

tff(c_541,plain,
    ( k4_xboole_0(k2_tarski('#skF_1','#skF_1'),'#skF_3') != k1_tarski('#skF_1')
    | r2_hidden('#skF_4','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_452,c_523,c_10])).

tff(c_542,plain,(
    k4_xboole_0(k2_tarski('#skF_1','#skF_1'),'#skF_3') != k1_tarski('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_458,c_541])).

tff(c_545,plain,(
    r2_hidden('#skF_1','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_542])).

tff(c_549,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_459,c_545])).

tff(c_551,plain,(
    r2_hidden('#skF_5','#skF_6') ),
    inference(splitRight,[status(thm)],[c_20])).

tff(c_556,plain,(
    r2_hidden('#skF_4','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_452,c_551])).

tff(c_573,plain,
    ( ~ r2_hidden('#skF_1','#skF_3')
    | k4_xboole_0(k2_tarski('#skF_4','#skF_4'),'#skF_6') = k1_tarski('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_452,c_26])).

tff(c_574,plain,(
    ~ r2_hidden('#skF_1','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_573])).

tff(c_579,plain,
    ( '#skF_2' = '#skF_1'
    | r2_hidden('#skF_2','#skF_3')
    | k4_xboole_0(k2_tarski('#skF_4','#skF_4'),'#skF_6') = k1_tarski('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_452,c_24])).

tff(c_580,plain,(
    k4_xboole_0(k2_tarski('#skF_4','#skF_4'),'#skF_6') = k1_tarski('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_579])).

tff(c_584,plain,(
    ~ r2_hidden('#skF_4','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_580,c_4])).

tff(c_596,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_556,c_584])).

tff(c_598,plain,(
    k4_xboole_0(k2_tarski('#skF_4','#skF_4'),'#skF_6') != k1_tarski('#skF_4') ),
    inference(splitRight,[status(thm)],[c_579])).

tff(c_597,plain,
    ( r2_hidden('#skF_2','#skF_3')
    | '#skF_2' = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_579])).

tff(c_599,plain,(
    '#skF_2' = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_597])).

tff(c_619,plain,
    ( k4_xboole_0(k2_tarski('#skF_1','#skF_1'),'#skF_3') != k1_tarski('#skF_1')
    | k4_xboole_0(k2_tarski('#skF_4','#skF_4'),'#skF_6') = k1_tarski('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_452,c_599,c_22])).

tff(c_620,plain,(
    k4_xboole_0(k2_tarski('#skF_1','#skF_1'),'#skF_3') != k1_tarski('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_598,c_619])).

tff(c_623,plain,(
    r2_hidden('#skF_1','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_620])).

tff(c_627,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_574,c_623])).

tff(c_628,plain,(
    r2_hidden('#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_597])).

tff(c_677,plain,
    ( k4_xboole_0(k2_tarski('#skF_1','#skF_2'),'#skF_3') != k1_tarski('#skF_1')
    | k4_xboole_0(k2_tarski('#skF_4','#skF_4'),'#skF_6') = k1_tarski('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_452,c_22])).

tff(c_678,plain,(
    k4_xboole_0(k2_tarski('#skF_1','#skF_2'),'#skF_3') != k1_tarski('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_598,c_677])).

tff(c_681,plain,
    ( ~ r2_hidden('#skF_2','#skF_3')
    | r2_hidden('#skF_1','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_678])).

tff(c_684,plain,(
    r2_hidden('#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_628,c_681])).

tff(c_686,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_574,c_684])).

tff(c_687,plain,(
    k4_xboole_0(k2_tarski('#skF_4','#skF_4'),'#skF_6') = k1_tarski('#skF_4') ),
    inference(splitRight,[status(thm)],[c_573])).

tff(c_694,plain,(
    ~ r2_hidden('#skF_4','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_687,c_4])).

tff(c_706,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_556,c_694])).

%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0913+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:37:04 EST 2020

% Result     : Theorem 2.69s
% Output     : CNFRefutation 2.82s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 176 expanded)
%              Number of leaves         :   24 (  65 expanded)
%              Depth                    :    9
%              Number of atoms          :  117 ( 364 expanded)
%              Number of equality atoms :    4 (  20 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k3_zfmisc_1 > k3_mcart_1 > k4_tarski > k2_zfmisc_1 > #nlpp > #skF_11 > #skF_7 > #skF_10 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_9 > #skF_8 > #skF_4 > #skF_12

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_11',type,(
    '#skF_11': $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k3_mcart_1,type,(
    k3_mcart_1: ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_10',type,(
    '#skF_10': $i )).

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

tff('#skF_12',type,(
    '#skF_12': $i )).

tff(f_43,negated_conjecture,(
    ~ ! [A,B,C,D,E,F] :
        ( r2_hidden(k3_mcart_1(A,B,C),k3_zfmisc_1(D,E,F))
      <=> ( r2_hidden(A,D)
          & r2_hidden(B,E)
          & r2_hidden(C,F) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_mcart_1)).

tff(f_26,axiom,(
    ! [A,B,C] : k3_mcart_1(A,B,C) = k4_tarski(k4_tarski(A,B),C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_mcart_1)).

tff(f_28,axiom,(
    ! [A,B,C] : k3_zfmisc_1(A,B,C) = k2_zfmisc_1(k2_zfmisc_1(A,B),C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).

tff(f_34,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,D))
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_zfmisc_1)).

tff(c_16,plain,
    ( r2_hidden('#skF_2','#skF_5')
    | ~ r2_hidden('#skF_9','#skF_12')
    | ~ r2_hidden('#skF_8','#skF_11')
    | ~ r2_hidden('#skF_7','#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_81,plain,(
    ~ r2_hidden('#skF_7','#skF_10') ),
    inference(splitLeft,[status(thm)],[c_16])).

tff(c_24,plain,
    ( r2_hidden('#skF_2','#skF_5')
    | r2_hidden(k3_mcart_1('#skF_7','#skF_8','#skF_9'),k3_zfmisc_1('#skF_10','#skF_11','#skF_12')) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_75,plain,(
    r2_hidden(k3_mcart_1('#skF_7','#skF_8','#skF_9'),k3_zfmisc_1('#skF_10','#skF_11','#skF_12')) ),
    inference(splitLeft,[status(thm)],[c_24])).

tff(c_2,plain,(
    ! [A_1,B_2,C_3] : k4_tarski(k4_tarski(A_1,B_2),C_3) = k3_mcart_1(A_1,B_2,C_3) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_4,plain,(
    ! [A_4,B_5,C_6] : k2_zfmisc_1(k2_zfmisc_1(A_4,B_5),C_6) = k3_zfmisc_1(A_4,B_5,C_6) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_64,plain,(
    ! [A_21,C_22,B_23,D_24] :
      ( r2_hidden(A_21,C_22)
      | ~ r2_hidden(k4_tarski(A_21,B_23),k2_zfmisc_1(C_22,D_24)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_151,plain,(
    ! [B_59,A_58,B_61,A_62,C_60] :
      ( r2_hidden(A_58,k2_zfmisc_1(A_62,B_59))
      | ~ r2_hidden(k4_tarski(A_58,B_61),k3_zfmisc_1(A_62,B_59,C_60)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_64])).

tff(c_192,plain,(
    ! [A_74,C_78,B_73,B_75,A_77,C_76] :
      ( r2_hidden(k4_tarski(A_77,B_75),k2_zfmisc_1(A_74,B_73))
      | ~ r2_hidden(k3_mcart_1(A_77,B_75,C_76),k3_zfmisc_1(A_74,B_73,C_78)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_151])).

tff(c_204,plain,(
    r2_hidden(k4_tarski('#skF_7','#skF_8'),k2_zfmisc_1('#skF_10','#skF_11')) ),
    inference(resolution,[status(thm)],[c_75,c_192])).

tff(c_10,plain,(
    ! [A_7,C_9,B_8,D_10] :
      ( r2_hidden(A_7,C_9)
      | ~ r2_hidden(k4_tarski(A_7,B_8),k2_zfmisc_1(C_9,D_10)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_207,plain,(
    r2_hidden('#skF_7','#skF_10') ),
    inference(resolution,[status(thm)],[c_204,c_10])).

tff(c_214,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_81,c_207])).

tff(c_216,plain,(
    r2_hidden('#skF_7','#skF_10') ),
    inference(splitRight,[status(thm)],[c_16])).

tff(c_215,plain,
    ( ~ r2_hidden('#skF_8','#skF_11')
    | ~ r2_hidden('#skF_9','#skF_12')
    | r2_hidden('#skF_2','#skF_5') ),
    inference(splitRight,[status(thm)],[c_16])).

tff(c_217,plain,(
    ~ r2_hidden('#skF_9','#skF_12') ),
    inference(splitLeft,[status(thm)],[c_215])).

tff(c_57,plain,(
    ! [B_17,D_18,A_19,C_20] :
      ( r2_hidden(B_17,D_18)
      | ~ r2_hidden(k4_tarski(A_19,B_17),k2_zfmisc_1(C_20,D_18)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_76,plain,(
    ! [D_30,C_33,B_32,A_34,C_31] :
      ( r2_hidden(C_33,D_30)
      | ~ r2_hidden(k3_mcart_1(A_34,B_32,C_33),k2_zfmisc_1(C_31,D_30)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_57])).

tff(c_259,plain,(
    ! [B_87,A_88,A_92,C_91,B_89,C_90] :
      ( r2_hidden(C_91,C_90)
      | ~ r2_hidden(k3_mcart_1(A_88,B_87,C_91),k3_zfmisc_1(A_92,B_89,C_90)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_76])).

tff(c_268,plain,(
    r2_hidden('#skF_9','#skF_12') ),
    inference(resolution,[status(thm)],[c_75,c_259])).

tff(c_272,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_217,c_268])).

tff(c_273,plain,
    ( ~ r2_hidden('#skF_8','#skF_11')
    | r2_hidden('#skF_2','#skF_5') ),
    inference(splitRight,[status(thm)],[c_215])).

tff(c_275,plain,(
    ~ r2_hidden('#skF_8','#skF_11') ),
    inference(splitLeft,[status(thm)],[c_273])).

tff(c_344,plain,(
    ! [A_111,B_114,A_115,C_113,B_112] :
      ( r2_hidden(A_111,k2_zfmisc_1(A_115,B_112))
      | ~ r2_hidden(k4_tarski(A_111,B_114),k3_zfmisc_1(A_115,B_112,C_113)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_64])).

tff(c_393,plain,(
    ! [A_134,C_133,B_132,B_135,A_136,C_131] :
      ( r2_hidden(k4_tarski(A_134,B_132),k2_zfmisc_1(A_136,B_135))
      | ~ r2_hidden(k3_mcart_1(A_134,B_132,C_133),k3_zfmisc_1(A_136,B_135,C_131)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_344])).

tff(c_405,plain,(
    r2_hidden(k4_tarski('#skF_7','#skF_8'),k2_zfmisc_1('#skF_10','#skF_11')) ),
    inference(resolution,[status(thm)],[c_75,c_393])).

tff(c_8,plain,(
    ! [B_8,D_10,A_7,C_9] :
      ( r2_hidden(B_8,D_10)
      | ~ r2_hidden(k4_tarski(A_7,B_8),k2_zfmisc_1(C_9,D_10)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_411,plain,(
    r2_hidden('#skF_8','#skF_11') ),
    inference(resolution,[status(thm)],[c_405,c_8])).

tff(c_417,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_275,c_411])).

tff(c_419,plain,(
    r2_hidden('#skF_8','#skF_11') ),
    inference(splitRight,[status(thm)],[c_273])).

tff(c_274,plain,(
    r2_hidden('#skF_9','#skF_12') ),
    inference(splitRight,[status(thm)],[c_215])).

tff(c_18,plain,
    ( r2_hidden('#skF_1','#skF_4')
    | ~ r2_hidden('#skF_9','#skF_12')
    | ~ r2_hidden('#skF_8','#skF_11')
    | ~ r2_hidden('#skF_7','#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_424,plain,(
    r2_hidden('#skF_1','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_216,c_419,c_274,c_18])).

tff(c_418,plain,(
    r2_hidden('#skF_2','#skF_5') ),
    inference(splitRight,[status(thm)],[c_273])).

tff(c_6,plain,(
    ! [A_7,B_8,C_9,D_10] :
      ( r2_hidden(k4_tarski(A_7,B_8),k2_zfmisc_1(C_9,D_10))
      | ~ r2_hidden(B_8,D_10)
      | ~ r2_hidden(A_7,C_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_14,plain,
    ( r2_hidden('#skF_3','#skF_6')
    | ~ r2_hidden('#skF_9','#skF_12')
    | ~ r2_hidden('#skF_8','#skF_11')
    | ~ r2_hidden('#skF_7','#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_421,plain,(
    r2_hidden('#skF_3','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_216,c_419,c_274,c_14])).

tff(c_473,plain,(
    ! [A_151,B_152,C_153,D_154] :
      ( r2_hidden(k4_tarski(A_151,B_152),k2_zfmisc_1(C_153,D_154))
      | ~ r2_hidden(B_152,D_154)
      | ~ r2_hidden(A_151,C_153) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_521,plain,(
    ! [A_174,B_171,C_172,A_173,B_170] :
      ( r2_hidden(k4_tarski(A_173,B_170),k3_zfmisc_1(A_174,B_171,C_172))
      | ~ r2_hidden(B_170,C_172)
      | ~ r2_hidden(A_173,k2_zfmisc_1(A_174,B_171)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_473])).

tff(c_560,plain,(
    ! [C_182,A_181,B_183,C_185,A_186,B_184] :
      ( r2_hidden(k3_mcart_1(A_186,B_183,C_185),k3_zfmisc_1(A_181,B_184,C_182))
      | ~ r2_hidden(C_185,C_182)
      | ~ r2_hidden(k4_tarski(A_186,B_183),k2_zfmisc_1(A_181,B_184)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_521])).

tff(c_12,plain,
    ( ~ r2_hidden(k3_mcart_1('#skF_1','#skF_2','#skF_3'),k3_zfmisc_1('#skF_4','#skF_5','#skF_6'))
    | ~ r2_hidden('#skF_9','#skF_12')
    | ~ r2_hidden('#skF_8','#skF_11')
    | ~ r2_hidden('#skF_7','#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_442,plain,(
    ~ r2_hidden(k3_mcart_1('#skF_1','#skF_2','#skF_3'),k3_zfmisc_1('#skF_4','#skF_5','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_216,c_419,c_274,c_12])).

tff(c_569,plain,
    ( ~ r2_hidden('#skF_3','#skF_6')
    | ~ r2_hidden(k4_tarski('#skF_1','#skF_2'),k2_zfmisc_1('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_560,c_442])).

tff(c_580,plain,(
    ~ r2_hidden(k4_tarski('#skF_1','#skF_2'),k2_zfmisc_1('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_421,c_569])).

tff(c_585,plain,
    ( ~ r2_hidden('#skF_2','#skF_5')
    | ~ r2_hidden('#skF_1','#skF_4') ),
    inference(resolution,[status(thm)],[c_6,c_580])).

tff(c_589,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_424,c_418,c_585])).

tff(c_591,plain,(
    ~ r2_hidden(k3_mcart_1('#skF_7','#skF_8','#skF_9'),k3_zfmisc_1('#skF_10','#skF_11','#skF_12')) ),
    inference(splitRight,[status(thm)],[c_24])).

tff(c_26,plain,
    ( r2_hidden('#skF_1','#skF_4')
    | r2_hidden(k3_mcart_1('#skF_7','#skF_8','#skF_9'),k3_zfmisc_1('#skF_10','#skF_11','#skF_12')) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_597,plain,(
    r2_hidden('#skF_1','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_591,c_26])).

tff(c_590,plain,(
    r2_hidden('#skF_2','#skF_5') ),
    inference(splitRight,[status(thm)],[c_24])).

tff(c_22,plain,
    ( r2_hidden('#skF_3','#skF_6')
    | r2_hidden(k3_mcart_1('#skF_7','#skF_8','#skF_9'),k3_zfmisc_1('#skF_10','#skF_11','#skF_12')) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_592,plain,(
    r2_hidden('#skF_3','#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_591,c_22])).

tff(c_601,plain,(
    ! [A_192,B_193,C_194,D_195] :
      ( r2_hidden(k4_tarski(A_192,B_193),k2_zfmisc_1(C_194,D_195))
      | ~ r2_hidden(B_193,D_195)
      | ~ r2_hidden(A_192,C_194) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_674,plain,(
    ! [C_221,A_224,B_220,A_222,B_223] :
      ( r2_hidden(k4_tarski(A_222,B_223),k3_zfmisc_1(A_224,B_220,C_221))
      | ~ r2_hidden(B_223,C_221)
      | ~ r2_hidden(A_222,k2_zfmisc_1(A_224,B_220)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_601])).

tff(c_715,plain,(
    ! [A_241,B_240,B_238,C_236,A_237,C_239] :
      ( r2_hidden(k3_mcart_1(A_241,B_238,C_239),k3_zfmisc_1(A_237,B_240,C_236))
      | ~ r2_hidden(C_239,C_236)
      | ~ r2_hidden(k4_tarski(A_241,B_238),k2_zfmisc_1(A_237,B_240)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_674])).

tff(c_20,plain,
    ( ~ r2_hidden(k3_mcart_1('#skF_1','#skF_2','#skF_3'),k3_zfmisc_1('#skF_4','#skF_5','#skF_6'))
    | r2_hidden(k3_mcart_1('#skF_7','#skF_8','#skF_9'),k3_zfmisc_1('#skF_10','#skF_11','#skF_12')) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_649,plain,(
    ~ r2_hidden(k3_mcart_1('#skF_1','#skF_2','#skF_3'),k3_zfmisc_1('#skF_4','#skF_5','#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_591,c_20])).

tff(c_724,plain,
    ( ~ r2_hidden('#skF_3','#skF_6')
    | ~ r2_hidden(k4_tarski('#skF_1','#skF_2'),k2_zfmisc_1('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_715,c_649])).

tff(c_738,plain,(
    ~ r2_hidden(k4_tarski('#skF_1','#skF_2'),k2_zfmisc_1('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_592,c_724])).

tff(c_744,plain,
    ( ~ r2_hidden('#skF_2','#skF_5')
    | ~ r2_hidden('#skF_1','#skF_4') ),
    inference(resolution,[status(thm)],[c_6,c_738])).

tff(c_748,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_597,c_590,c_744])).

%------------------------------------------------------------------------------

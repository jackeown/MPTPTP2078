%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:10:08 EST 2020

% Result     : Theorem 2.69s
% Output     : CNFRefutation 2.84s
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

tff(f_44,negated_conjecture,(
    ~ ! [A,B,C,D,E,F] :
        ( r2_hidden(k3_mcart_1(A,B,C),k3_zfmisc_1(D,E,F))
      <=> ( r2_hidden(A,D)
          & r2_hidden(B,E)
          & r2_hidden(C,F) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_mcart_1)).

tff(f_35,axiom,(
    ! [A,B,C] : k3_zfmisc_1(A,B,C) = k2_zfmisc_1(k2_zfmisc_1(A,B),C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).

tff(f_33,axiom,(
    ! [A,B,C] : k3_mcart_1(A,B,C) = k4_tarski(k4_tarski(A,B),C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_mcart_1)).

tff(f_31,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,D))
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).

tff(c_14,plain,
    ( r2_hidden('#skF_3','#skF_6')
    | ~ r2_hidden('#skF_9','#skF_12')
    | ~ r2_hidden('#skF_8','#skF_11')
    | ~ r2_hidden('#skF_7','#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_80,plain,(
    ~ r2_hidden('#skF_7','#skF_10') ),
    inference(splitLeft,[status(thm)],[c_14])).

tff(c_24,plain,
    ( r2_hidden('#skF_2','#skF_5')
    | r2_hidden(k3_mcart_1('#skF_7','#skF_8','#skF_9'),k3_zfmisc_1('#skF_10','#skF_11','#skF_12')) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_75,plain,(
    r2_hidden(k3_mcart_1('#skF_7','#skF_8','#skF_9'),k3_zfmisc_1('#skF_10','#skF_11','#skF_12')) ),
    inference(splitLeft,[status(thm)],[c_24])).

tff(c_10,plain,(
    ! [A_8,B_9,C_10] : k2_zfmisc_1(k2_zfmisc_1(A_8,B_9),C_10) = k3_zfmisc_1(A_8,B_9,C_10) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_8,plain,(
    ! [A_5,B_6,C_7] : k4_tarski(k4_tarski(A_5,B_6),C_7) = k3_mcart_1(A_5,B_6,C_7) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_57,plain,(
    ! [A_17,C_18,B_19,D_20] :
      ( r2_hidden(A_17,C_18)
      | ~ r2_hidden(k4_tarski(A_17,B_19),k2_zfmisc_1(C_18,D_20)) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_145,plain,(
    ! [A_56,C_57,D_53,C_55,B_54] :
      ( r2_hidden(k4_tarski(A_56,B_54),C_57)
      | ~ r2_hidden(k3_mcart_1(A_56,B_54,C_55),k2_zfmisc_1(C_57,D_53)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_57])).

tff(c_195,plain,(
    ! [A_74,A_76,B_78,B_75,C_73,C_77] :
      ( r2_hidden(k4_tarski(A_76,B_78),k2_zfmisc_1(A_74,B_75))
      | ~ r2_hidden(k3_mcart_1(A_76,B_78,C_73),k3_zfmisc_1(A_74,B_75,C_77)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_145])).

tff(c_207,plain,(
    r2_hidden(k4_tarski('#skF_7','#skF_8'),k2_zfmisc_1('#skF_10','#skF_11')) ),
    inference(resolution,[status(thm)],[c_75,c_195])).

tff(c_6,plain,(
    ! [A_1,C_3,B_2,D_4] :
      ( r2_hidden(A_1,C_3)
      | ~ r2_hidden(k4_tarski(A_1,B_2),k2_zfmisc_1(C_3,D_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_213,plain,(
    r2_hidden('#skF_7','#skF_10') ),
    inference(resolution,[status(thm)],[c_207,c_6])).

tff(c_218,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_213])).

tff(c_220,plain,(
    r2_hidden('#skF_7','#skF_10') ),
    inference(splitRight,[status(thm)],[c_14])).

tff(c_219,plain,
    ( ~ r2_hidden('#skF_8','#skF_11')
    | ~ r2_hidden('#skF_9','#skF_12')
    | r2_hidden('#skF_3','#skF_6') ),
    inference(splitRight,[status(thm)],[c_14])).

tff(c_221,plain,(
    ~ r2_hidden('#skF_9','#skF_12') ),
    inference(splitLeft,[status(thm)],[c_219])).

tff(c_64,plain,(
    ! [B_21,D_22,A_23,C_24] :
      ( r2_hidden(B_21,D_22)
      | ~ r2_hidden(k4_tarski(A_23,B_21),k2_zfmisc_1(C_24,D_22)) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_71,plain,(
    ! [D_29,C_25,A_28,C_27,B_26] :
      ( r2_hidden(C_27,D_29)
      | ~ r2_hidden(k3_mcart_1(A_28,B_26,C_27),k2_zfmisc_1(C_25,D_29)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_64])).

tff(c_263,plain,(
    ! [A_87,C_89,C_92,A_88,B_91,B_90] :
      ( r2_hidden(C_89,C_92)
      | ~ r2_hidden(k3_mcart_1(A_87,B_90,C_89),k3_zfmisc_1(A_88,B_91,C_92)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_71])).

tff(c_272,plain,(
    r2_hidden('#skF_9','#skF_12') ),
    inference(resolution,[status(thm)],[c_75,c_263])).

tff(c_276,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_221,c_272])).

tff(c_277,plain,
    ( ~ r2_hidden('#skF_8','#skF_11')
    | r2_hidden('#skF_3','#skF_6') ),
    inference(splitRight,[status(thm)],[c_219])).

tff(c_279,plain,(
    ~ r2_hidden('#skF_8','#skF_11') ),
    inference(splitLeft,[status(thm)],[c_277])).

tff(c_357,plain,(
    ! [D_116,A_119,C_120,C_118,B_117] :
      ( r2_hidden(k4_tarski(A_119,B_117),C_120)
      | ~ r2_hidden(k3_mcart_1(A_119,B_117,C_118),k2_zfmisc_1(C_120,D_116)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_57])).

tff(c_397,plain,(
    ! [A_134,C_132,C_136,A_133,B_131,B_135] :
      ( r2_hidden(k4_tarski(A_134,B_131),k2_zfmisc_1(A_133,B_135))
      | ~ r2_hidden(k3_mcart_1(A_134,B_131,C_132),k3_zfmisc_1(A_133,B_135,C_136)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_357])).

tff(c_409,plain,(
    r2_hidden(k4_tarski('#skF_7','#skF_8'),k2_zfmisc_1('#skF_10','#skF_11')) ),
    inference(resolution,[status(thm)],[c_75,c_397])).

tff(c_4,plain,(
    ! [B_2,D_4,A_1,C_3] :
      ( r2_hidden(B_2,D_4)
      | ~ r2_hidden(k4_tarski(A_1,B_2),k2_zfmisc_1(C_3,D_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_412,plain,(
    r2_hidden('#skF_8','#skF_11') ),
    inference(resolution,[status(thm)],[c_409,c_4])).

tff(c_419,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_279,c_412])).

tff(c_421,plain,(
    r2_hidden('#skF_8','#skF_11') ),
    inference(splitRight,[status(thm)],[c_277])).

tff(c_278,plain,(
    r2_hidden('#skF_9','#skF_12') ),
    inference(splitRight,[status(thm)],[c_219])).

tff(c_18,plain,
    ( r2_hidden('#skF_1','#skF_4')
    | ~ r2_hidden('#skF_9','#skF_12')
    | ~ r2_hidden('#skF_8','#skF_11')
    | ~ r2_hidden('#skF_7','#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_423,plain,(
    r2_hidden('#skF_1','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_220,c_421,c_278,c_18])).

tff(c_16,plain,
    ( r2_hidden('#skF_2','#skF_5')
    | ~ r2_hidden('#skF_9','#skF_12')
    | ~ r2_hidden('#skF_8','#skF_11')
    | ~ r2_hidden('#skF_7','#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_427,plain,(
    r2_hidden('#skF_2','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_220,c_421,c_278,c_16])).

tff(c_2,plain,(
    ! [A_1,B_2,C_3,D_4] :
      ( r2_hidden(k4_tarski(A_1,B_2),k2_zfmisc_1(C_3,D_4))
      | ~ r2_hidden(B_2,D_4)
      | ~ r2_hidden(A_1,C_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_420,plain,(
    r2_hidden('#skF_3','#skF_6') ),
    inference(splitRight,[status(thm)],[c_277])).

tff(c_462,plain,(
    ! [A_145,B_146,C_147,D_148] :
      ( r2_hidden(k4_tarski(A_145,B_146),k2_zfmisc_1(C_147,D_148))
      | ~ r2_hidden(B_146,D_148)
      | ~ r2_hidden(A_145,C_147) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_506,plain,(
    ! [C_169,A_166,A_165,B_167,B_168] :
      ( r2_hidden(k4_tarski(A_166,B_167),k3_zfmisc_1(A_165,B_168,C_169))
      | ~ r2_hidden(B_167,C_169)
      | ~ r2_hidden(A_166,k2_zfmisc_1(A_165,B_168)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_462])).

tff(c_563,plain,(
    ! [C_185,C_181,A_186,A_183,B_182,B_184] :
      ( r2_hidden(k3_mcart_1(A_186,B_182,C_185),k3_zfmisc_1(A_183,B_184,C_181))
      | ~ r2_hidden(C_185,C_181)
      | ~ r2_hidden(k4_tarski(A_186,B_182),k2_zfmisc_1(A_183,B_184)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_506])).

tff(c_12,plain,
    ( ~ r2_hidden(k3_mcart_1('#skF_1','#skF_2','#skF_3'),k3_zfmisc_1('#skF_4','#skF_5','#skF_6'))
    | ~ r2_hidden('#skF_9','#skF_12')
    | ~ r2_hidden('#skF_8','#skF_11')
    | ~ r2_hidden('#skF_7','#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_562,plain,(
    ~ r2_hidden(k3_mcart_1('#skF_1','#skF_2','#skF_3'),k3_zfmisc_1('#skF_4','#skF_5','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_220,c_421,c_278,c_12])).

tff(c_566,plain,
    ( ~ r2_hidden('#skF_3','#skF_6')
    | ~ r2_hidden(k4_tarski('#skF_1','#skF_2'),k2_zfmisc_1('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_563,c_562])).

tff(c_581,plain,(
    ~ r2_hidden(k4_tarski('#skF_1','#skF_2'),k2_zfmisc_1('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_420,c_566])).

tff(c_588,plain,
    ( ~ r2_hidden('#skF_2','#skF_5')
    | ~ r2_hidden('#skF_1','#skF_4') ),
    inference(resolution,[status(thm)],[c_2,c_581])).

tff(c_592,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_423,c_427,c_588])).

tff(c_594,plain,(
    ~ r2_hidden(k3_mcart_1('#skF_7','#skF_8','#skF_9'),k3_zfmisc_1('#skF_10','#skF_11','#skF_12')) ),
    inference(splitRight,[status(thm)],[c_24])).

tff(c_26,plain,
    ( r2_hidden('#skF_1','#skF_4')
    | r2_hidden(k3_mcart_1('#skF_7','#skF_8','#skF_9'),k3_zfmisc_1('#skF_10','#skF_11','#skF_12')) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_600,plain,(
    r2_hidden('#skF_1','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_594,c_26])).

tff(c_593,plain,(
    r2_hidden('#skF_2','#skF_5') ),
    inference(splitRight,[status(thm)],[c_24])).

tff(c_22,plain,
    ( r2_hidden('#skF_3','#skF_6')
    | r2_hidden(k3_mcart_1('#skF_7','#skF_8','#skF_9'),k3_zfmisc_1('#skF_10','#skF_11','#skF_12')) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_601,plain,(
    r2_hidden('#skF_3','#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_594,c_22])).

tff(c_644,plain,(
    ! [A_206,B_207,C_208,D_209] :
      ( r2_hidden(k4_tarski(A_206,B_207),k2_zfmisc_1(C_208,D_209))
      | ~ r2_hidden(B_207,D_209)
      | ~ r2_hidden(A_206,C_208) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_692,plain,(
    ! [B_225,B_228,C_229,A_226,A_227] :
      ( r2_hidden(k4_tarski(A_226,B_225),k3_zfmisc_1(A_227,B_228,C_229))
      | ~ r2_hidden(B_225,C_229)
      | ~ r2_hidden(A_226,k2_zfmisc_1(A_227,B_228)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_644])).

tff(c_717,plain,(
    ! [A_241,A_239,B_238,C_237,B_236,C_240] :
      ( r2_hidden(k3_mcart_1(A_241,B_238,C_240),k3_zfmisc_1(A_239,B_236,C_237))
      | ~ r2_hidden(C_240,C_237)
      | ~ r2_hidden(k4_tarski(A_241,B_238),k2_zfmisc_1(A_239,B_236)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_692])).

tff(c_20,plain,
    ( ~ r2_hidden(k3_mcart_1('#skF_1','#skF_2','#skF_3'),k3_zfmisc_1('#skF_4','#skF_5','#skF_6'))
    | r2_hidden(k3_mcart_1('#skF_7','#skF_8','#skF_9'),k3_zfmisc_1('#skF_10','#skF_11','#skF_12')) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_691,plain,(
    ~ r2_hidden(k3_mcart_1('#skF_1','#skF_2','#skF_3'),k3_zfmisc_1('#skF_4','#skF_5','#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_594,c_20])).

tff(c_723,plain,
    ( ~ r2_hidden('#skF_3','#skF_6')
    | ~ r2_hidden(k4_tarski('#skF_1','#skF_2'),k2_zfmisc_1('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_717,c_691])).

tff(c_739,plain,(
    ~ r2_hidden(k4_tarski('#skF_1','#skF_2'),k2_zfmisc_1('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_601,c_723])).

tff(c_746,plain,
    ( ~ r2_hidden('#skF_2','#skF_5')
    | ~ r2_hidden('#skF_1','#skF_4') ),
    inference(resolution,[status(thm)],[c_2,c_739])).

tff(c_750,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_600,c_593,c_746])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 10:40:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.69/1.48  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.69/1.49  
% 2.69/1.49  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.84/1.49  %$ r2_hidden > k3_zfmisc_1 > k3_mcart_1 > k4_tarski > k2_zfmisc_1 > #nlpp > #skF_11 > #skF_7 > #skF_10 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_9 > #skF_8 > #skF_4 > #skF_12
% 2.84/1.49  
% 2.84/1.49  %Foreground sorts:
% 2.84/1.49  
% 2.84/1.49  
% 2.84/1.49  %Background operators:
% 2.84/1.49  
% 2.84/1.49  
% 2.84/1.49  %Foreground operators:
% 2.84/1.49  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.84/1.49  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.84/1.49  tff('#skF_11', type, '#skF_11': $i).
% 2.84/1.49  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.84/1.49  tff(k3_mcart_1, type, k3_mcart_1: ($i * $i * $i) > $i).
% 2.84/1.49  tff('#skF_7', type, '#skF_7': $i).
% 2.84/1.49  tff('#skF_10', type, '#skF_10': $i).
% 2.84/1.49  tff('#skF_5', type, '#skF_5': $i).
% 2.84/1.49  tff('#skF_6', type, '#skF_6': $i).
% 2.84/1.49  tff('#skF_2', type, '#skF_2': $i).
% 2.84/1.49  tff('#skF_3', type, '#skF_3': $i).
% 2.84/1.49  tff('#skF_1', type, '#skF_1': $i).
% 2.84/1.49  tff('#skF_9', type, '#skF_9': $i).
% 2.84/1.49  tff(k3_zfmisc_1, type, k3_zfmisc_1: ($i * $i * $i) > $i).
% 2.84/1.49  tff('#skF_8', type, '#skF_8': $i).
% 2.84/1.49  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.84/1.49  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.84/1.49  tff('#skF_4', type, '#skF_4': $i).
% 2.84/1.49  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.84/1.49  tff('#skF_12', type, '#skF_12': $i).
% 2.84/1.49  
% 2.84/1.51  tff(f_44, negated_conjecture, ~(![A, B, C, D, E, F]: (r2_hidden(k3_mcart_1(A, B, C), k3_zfmisc_1(D, E, F)) <=> ((r2_hidden(A, D) & r2_hidden(B, E)) & r2_hidden(C, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_mcart_1)).
% 2.84/1.51  tff(f_35, axiom, (![A, B, C]: (k3_zfmisc_1(A, B, C) = k2_zfmisc_1(k2_zfmisc_1(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_zfmisc_1)).
% 2.84/1.51  tff(f_33, axiom, (![A, B, C]: (k3_mcart_1(A, B, C) = k4_tarski(k4_tarski(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_mcart_1)).
% 2.84/1.51  tff(f_31, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, D)) <=> (r2_hidden(A, C) & r2_hidden(B, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 2.84/1.51  tff(c_14, plain, (r2_hidden('#skF_3', '#skF_6') | ~r2_hidden('#skF_9', '#skF_12') | ~r2_hidden('#skF_8', '#skF_11') | ~r2_hidden('#skF_7', '#skF_10')), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.84/1.51  tff(c_80, plain, (~r2_hidden('#skF_7', '#skF_10')), inference(splitLeft, [status(thm)], [c_14])).
% 2.84/1.51  tff(c_24, plain, (r2_hidden('#skF_2', '#skF_5') | r2_hidden(k3_mcart_1('#skF_7', '#skF_8', '#skF_9'), k3_zfmisc_1('#skF_10', '#skF_11', '#skF_12'))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.84/1.51  tff(c_75, plain, (r2_hidden(k3_mcart_1('#skF_7', '#skF_8', '#skF_9'), k3_zfmisc_1('#skF_10', '#skF_11', '#skF_12'))), inference(splitLeft, [status(thm)], [c_24])).
% 2.84/1.51  tff(c_10, plain, (![A_8, B_9, C_10]: (k2_zfmisc_1(k2_zfmisc_1(A_8, B_9), C_10)=k3_zfmisc_1(A_8, B_9, C_10))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.84/1.51  tff(c_8, plain, (![A_5, B_6, C_7]: (k4_tarski(k4_tarski(A_5, B_6), C_7)=k3_mcart_1(A_5, B_6, C_7))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.84/1.51  tff(c_57, plain, (![A_17, C_18, B_19, D_20]: (r2_hidden(A_17, C_18) | ~r2_hidden(k4_tarski(A_17, B_19), k2_zfmisc_1(C_18, D_20)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.84/1.51  tff(c_145, plain, (![A_56, C_57, D_53, C_55, B_54]: (r2_hidden(k4_tarski(A_56, B_54), C_57) | ~r2_hidden(k3_mcart_1(A_56, B_54, C_55), k2_zfmisc_1(C_57, D_53)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_57])).
% 2.84/1.51  tff(c_195, plain, (![A_74, A_76, B_78, B_75, C_73, C_77]: (r2_hidden(k4_tarski(A_76, B_78), k2_zfmisc_1(A_74, B_75)) | ~r2_hidden(k3_mcart_1(A_76, B_78, C_73), k3_zfmisc_1(A_74, B_75, C_77)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_145])).
% 2.84/1.51  tff(c_207, plain, (r2_hidden(k4_tarski('#skF_7', '#skF_8'), k2_zfmisc_1('#skF_10', '#skF_11'))), inference(resolution, [status(thm)], [c_75, c_195])).
% 2.84/1.51  tff(c_6, plain, (![A_1, C_3, B_2, D_4]: (r2_hidden(A_1, C_3) | ~r2_hidden(k4_tarski(A_1, B_2), k2_zfmisc_1(C_3, D_4)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.84/1.51  tff(c_213, plain, (r2_hidden('#skF_7', '#skF_10')), inference(resolution, [status(thm)], [c_207, c_6])).
% 2.84/1.51  tff(c_218, plain, $false, inference(negUnitSimplification, [status(thm)], [c_80, c_213])).
% 2.84/1.51  tff(c_220, plain, (r2_hidden('#skF_7', '#skF_10')), inference(splitRight, [status(thm)], [c_14])).
% 2.84/1.51  tff(c_219, plain, (~r2_hidden('#skF_8', '#skF_11') | ~r2_hidden('#skF_9', '#skF_12') | r2_hidden('#skF_3', '#skF_6')), inference(splitRight, [status(thm)], [c_14])).
% 2.84/1.51  tff(c_221, plain, (~r2_hidden('#skF_9', '#skF_12')), inference(splitLeft, [status(thm)], [c_219])).
% 2.84/1.51  tff(c_64, plain, (![B_21, D_22, A_23, C_24]: (r2_hidden(B_21, D_22) | ~r2_hidden(k4_tarski(A_23, B_21), k2_zfmisc_1(C_24, D_22)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.84/1.51  tff(c_71, plain, (![D_29, C_25, A_28, C_27, B_26]: (r2_hidden(C_27, D_29) | ~r2_hidden(k3_mcart_1(A_28, B_26, C_27), k2_zfmisc_1(C_25, D_29)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_64])).
% 2.84/1.51  tff(c_263, plain, (![A_87, C_89, C_92, A_88, B_91, B_90]: (r2_hidden(C_89, C_92) | ~r2_hidden(k3_mcart_1(A_87, B_90, C_89), k3_zfmisc_1(A_88, B_91, C_92)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_71])).
% 2.84/1.51  tff(c_272, plain, (r2_hidden('#skF_9', '#skF_12')), inference(resolution, [status(thm)], [c_75, c_263])).
% 2.84/1.51  tff(c_276, plain, $false, inference(negUnitSimplification, [status(thm)], [c_221, c_272])).
% 2.84/1.51  tff(c_277, plain, (~r2_hidden('#skF_8', '#skF_11') | r2_hidden('#skF_3', '#skF_6')), inference(splitRight, [status(thm)], [c_219])).
% 2.84/1.51  tff(c_279, plain, (~r2_hidden('#skF_8', '#skF_11')), inference(splitLeft, [status(thm)], [c_277])).
% 2.84/1.51  tff(c_357, plain, (![D_116, A_119, C_120, C_118, B_117]: (r2_hidden(k4_tarski(A_119, B_117), C_120) | ~r2_hidden(k3_mcart_1(A_119, B_117, C_118), k2_zfmisc_1(C_120, D_116)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_57])).
% 2.84/1.51  tff(c_397, plain, (![A_134, C_132, C_136, A_133, B_131, B_135]: (r2_hidden(k4_tarski(A_134, B_131), k2_zfmisc_1(A_133, B_135)) | ~r2_hidden(k3_mcart_1(A_134, B_131, C_132), k3_zfmisc_1(A_133, B_135, C_136)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_357])).
% 2.84/1.51  tff(c_409, plain, (r2_hidden(k4_tarski('#skF_7', '#skF_8'), k2_zfmisc_1('#skF_10', '#skF_11'))), inference(resolution, [status(thm)], [c_75, c_397])).
% 2.84/1.51  tff(c_4, plain, (![B_2, D_4, A_1, C_3]: (r2_hidden(B_2, D_4) | ~r2_hidden(k4_tarski(A_1, B_2), k2_zfmisc_1(C_3, D_4)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.84/1.51  tff(c_412, plain, (r2_hidden('#skF_8', '#skF_11')), inference(resolution, [status(thm)], [c_409, c_4])).
% 2.84/1.51  tff(c_419, plain, $false, inference(negUnitSimplification, [status(thm)], [c_279, c_412])).
% 2.84/1.51  tff(c_421, plain, (r2_hidden('#skF_8', '#skF_11')), inference(splitRight, [status(thm)], [c_277])).
% 2.84/1.51  tff(c_278, plain, (r2_hidden('#skF_9', '#skF_12')), inference(splitRight, [status(thm)], [c_219])).
% 2.84/1.51  tff(c_18, plain, (r2_hidden('#skF_1', '#skF_4') | ~r2_hidden('#skF_9', '#skF_12') | ~r2_hidden('#skF_8', '#skF_11') | ~r2_hidden('#skF_7', '#skF_10')), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.84/1.51  tff(c_423, plain, (r2_hidden('#skF_1', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_220, c_421, c_278, c_18])).
% 2.84/1.51  tff(c_16, plain, (r2_hidden('#skF_2', '#skF_5') | ~r2_hidden('#skF_9', '#skF_12') | ~r2_hidden('#skF_8', '#skF_11') | ~r2_hidden('#skF_7', '#skF_10')), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.84/1.51  tff(c_427, plain, (r2_hidden('#skF_2', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_220, c_421, c_278, c_16])).
% 2.84/1.51  tff(c_2, plain, (![A_1, B_2, C_3, D_4]: (r2_hidden(k4_tarski(A_1, B_2), k2_zfmisc_1(C_3, D_4)) | ~r2_hidden(B_2, D_4) | ~r2_hidden(A_1, C_3))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.84/1.51  tff(c_420, plain, (r2_hidden('#skF_3', '#skF_6')), inference(splitRight, [status(thm)], [c_277])).
% 2.84/1.51  tff(c_462, plain, (![A_145, B_146, C_147, D_148]: (r2_hidden(k4_tarski(A_145, B_146), k2_zfmisc_1(C_147, D_148)) | ~r2_hidden(B_146, D_148) | ~r2_hidden(A_145, C_147))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.84/1.51  tff(c_506, plain, (![C_169, A_166, A_165, B_167, B_168]: (r2_hidden(k4_tarski(A_166, B_167), k3_zfmisc_1(A_165, B_168, C_169)) | ~r2_hidden(B_167, C_169) | ~r2_hidden(A_166, k2_zfmisc_1(A_165, B_168)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_462])).
% 2.84/1.51  tff(c_563, plain, (![C_185, C_181, A_186, A_183, B_182, B_184]: (r2_hidden(k3_mcart_1(A_186, B_182, C_185), k3_zfmisc_1(A_183, B_184, C_181)) | ~r2_hidden(C_185, C_181) | ~r2_hidden(k4_tarski(A_186, B_182), k2_zfmisc_1(A_183, B_184)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_506])).
% 2.84/1.51  tff(c_12, plain, (~r2_hidden(k3_mcart_1('#skF_1', '#skF_2', '#skF_3'), k3_zfmisc_1('#skF_4', '#skF_5', '#skF_6')) | ~r2_hidden('#skF_9', '#skF_12') | ~r2_hidden('#skF_8', '#skF_11') | ~r2_hidden('#skF_7', '#skF_10')), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.84/1.51  tff(c_562, plain, (~r2_hidden(k3_mcart_1('#skF_1', '#skF_2', '#skF_3'), k3_zfmisc_1('#skF_4', '#skF_5', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_220, c_421, c_278, c_12])).
% 2.84/1.51  tff(c_566, plain, (~r2_hidden('#skF_3', '#skF_6') | ~r2_hidden(k4_tarski('#skF_1', '#skF_2'), k2_zfmisc_1('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_563, c_562])).
% 2.84/1.51  tff(c_581, plain, (~r2_hidden(k4_tarski('#skF_1', '#skF_2'), k2_zfmisc_1('#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_420, c_566])).
% 2.84/1.51  tff(c_588, plain, (~r2_hidden('#skF_2', '#skF_5') | ~r2_hidden('#skF_1', '#skF_4')), inference(resolution, [status(thm)], [c_2, c_581])).
% 2.84/1.51  tff(c_592, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_423, c_427, c_588])).
% 2.84/1.51  tff(c_594, plain, (~r2_hidden(k3_mcart_1('#skF_7', '#skF_8', '#skF_9'), k3_zfmisc_1('#skF_10', '#skF_11', '#skF_12'))), inference(splitRight, [status(thm)], [c_24])).
% 2.84/1.51  tff(c_26, plain, (r2_hidden('#skF_1', '#skF_4') | r2_hidden(k3_mcart_1('#skF_7', '#skF_8', '#skF_9'), k3_zfmisc_1('#skF_10', '#skF_11', '#skF_12'))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.84/1.51  tff(c_600, plain, (r2_hidden('#skF_1', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_594, c_26])).
% 2.84/1.51  tff(c_593, plain, (r2_hidden('#skF_2', '#skF_5')), inference(splitRight, [status(thm)], [c_24])).
% 2.84/1.51  tff(c_22, plain, (r2_hidden('#skF_3', '#skF_6') | r2_hidden(k3_mcart_1('#skF_7', '#skF_8', '#skF_9'), k3_zfmisc_1('#skF_10', '#skF_11', '#skF_12'))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.84/1.51  tff(c_601, plain, (r2_hidden('#skF_3', '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_594, c_22])).
% 2.84/1.51  tff(c_644, plain, (![A_206, B_207, C_208, D_209]: (r2_hidden(k4_tarski(A_206, B_207), k2_zfmisc_1(C_208, D_209)) | ~r2_hidden(B_207, D_209) | ~r2_hidden(A_206, C_208))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.84/1.51  tff(c_692, plain, (![B_225, B_228, C_229, A_226, A_227]: (r2_hidden(k4_tarski(A_226, B_225), k3_zfmisc_1(A_227, B_228, C_229)) | ~r2_hidden(B_225, C_229) | ~r2_hidden(A_226, k2_zfmisc_1(A_227, B_228)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_644])).
% 2.84/1.51  tff(c_717, plain, (![A_241, A_239, B_238, C_237, B_236, C_240]: (r2_hidden(k3_mcart_1(A_241, B_238, C_240), k3_zfmisc_1(A_239, B_236, C_237)) | ~r2_hidden(C_240, C_237) | ~r2_hidden(k4_tarski(A_241, B_238), k2_zfmisc_1(A_239, B_236)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_692])).
% 2.84/1.51  tff(c_20, plain, (~r2_hidden(k3_mcart_1('#skF_1', '#skF_2', '#skF_3'), k3_zfmisc_1('#skF_4', '#skF_5', '#skF_6')) | r2_hidden(k3_mcart_1('#skF_7', '#skF_8', '#skF_9'), k3_zfmisc_1('#skF_10', '#skF_11', '#skF_12'))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.84/1.51  tff(c_691, plain, (~r2_hidden(k3_mcart_1('#skF_1', '#skF_2', '#skF_3'), k3_zfmisc_1('#skF_4', '#skF_5', '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_594, c_20])).
% 2.84/1.51  tff(c_723, plain, (~r2_hidden('#skF_3', '#skF_6') | ~r2_hidden(k4_tarski('#skF_1', '#skF_2'), k2_zfmisc_1('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_717, c_691])).
% 2.84/1.51  tff(c_739, plain, (~r2_hidden(k4_tarski('#skF_1', '#skF_2'), k2_zfmisc_1('#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_601, c_723])).
% 2.84/1.51  tff(c_746, plain, (~r2_hidden('#skF_2', '#skF_5') | ~r2_hidden('#skF_1', '#skF_4')), inference(resolution, [status(thm)], [c_2, c_739])).
% 2.84/1.51  tff(c_750, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_600, c_593, c_746])).
% 2.84/1.51  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.84/1.51  
% 2.84/1.51  Inference rules
% 2.84/1.51  ----------------------
% 2.84/1.51  #Ref     : 0
% 2.84/1.51  #Sup     : 163
% 2.84/1.51  #Fact    : 0
% 2.84/1.51  #Define  : 0
% 2.84/1.51  #Split   : 6
% 2.84/1.51  #Chain   : 0
% 2.84/1.51  #Close   : 0
% 2.84/1.51  
% 2.84/1.51  Ordering : KBO
% 2.84/1.51  
% 2.84/1.51  Simplification rules
% 2.84/1.51  ----------------------
% 2.84/1.51  #Subsume      : 65
% 2.84/1.51  #Demod        : 100
% 2.84/1.51  #Tautology    : 87
% 2.84/1.51  #SimpNegUnit  : 6
% 2.84/1.51  #BackRed      : 0
% 2.84/1.51  
% 2.84/1.51  #Partial instantiations: 0
% 2.84/1.51  #Strategies tried      : 1
% 2.84/1.51  
% 2.84/1.51  Timing (in seconds)
% 2.84/1.51  ----------------------
% 2.84/1.51  Preprocessing        : 0.29
% 2.84/1.51  Parsing              : 0.15
% 2.84/1.51  CNF conversion       : 0.02
% 2.84/1.51  Main loop            : 0.39
% 2.84/1.51  Inferencing          : 0.17
% 2.84/1.51  Reduction            : 0.10
% 2.84/1.52  Demodulation         : 0.07
% 2.84/1.52  BG Simplification    : 0.02
% 2.84/1.52  Subsumption          : 0.07
% 2.84/1.52  Abstraction          : 0.02
% 2.84/1.52  MUC search           : 0.00
% 2.84/1.52  Cooper               : 0.00
% 2.84/1.52  Total                : 0.71
% 2.84/1.52  Index Insertion      : 0.00
% 2.84/1.52  Index Deletion       : 0.00
% 2.84/1.52  Index Matching       : 0.00
% 2.84/1.52  BG Taut test         : 0.00
%------------------------------------------------------------------------------

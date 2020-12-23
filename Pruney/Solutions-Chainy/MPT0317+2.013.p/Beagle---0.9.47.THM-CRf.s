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
% DateTime   : Thu Dec  3 09:54:01 EST 2020

% Result     : Theorem 2.55s
% Output     : CNFRefutation 2.79s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 202 expanded)
%              Number of leaves         :   21 (  73 expanded)
%              Depth                    :    6
%              Number of atoms          :  111 ( 389 expanded)
%              Number of equality atoms :   18 (  93 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k2_enumset1 > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_tarski > #nlpp > k1_tarski > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_8 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

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

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(f_50,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,k1_tarski(D)))
      <=> ( r2_hidden(A,C)
          & B = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t129_zfmisc_1)).

tff(f_37,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,D))
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).

tff(f_43,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(k1_tarski(C),D))
    <=> ( A = C
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t128_zfmisc_1)).

tff(c_22,plain,
    ( '#skF_2' = '#skF_4'
    | '#skF_6' != '#skF_8'
    | ~ r2_hidden('#skF_5','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_40,plain,(
    ~ r2_hidden('#skF_5','#skF_7') ),
    inference(splitLeft,[status(thm)],[c_22])).

tff(c_28,plain,
    ( '#skF_2' = '#skF_4'
    | r2_hidden(k4_tarski('#skF_5','#skF_6'),k2_zfmisc_1('#skF_7',k1_tarski('#skF_8'))) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_62,plain,(
    r2_hidden(k4_tarski('#skF_5','#skF_6'),k2_zfmisc_1('#skF_7',k1_tarski('#skF_8'))) ),
    inference(splitLeft,[status(thm)],[c_28])).

tff(c_12,plain,(
    ! [A_7,C_9,B_8,D_10] :
      ( r2_hidden(A_7,C_9)
      | ~ r2_hidden(k4_tarski(A_7,B_8),k2_zfmisc_1(C_9,D_10)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_68,plain,(
    r2_hidden('#skF_5','#skF_7') ),
    inference(resolution,[status(thm)],[c_62,c_12])).

tff(c_73,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_68])).

tff(c_75,plain,(
    ~ r2_hidden(k4_tarski('#skF_5','#skF_6'),k2_zfmisc_1('#skF_7',k1_tarski('#skF_8'))) ),
    inference(splitRight,[status(thm)],[c_28])).

tff(c_30,plain,
    ( r2_hidden('#skF_1','#skF_3')
    | r2_hidden(k4_tarski('#skF_5','#skF_6'),k2_zfmisc_1('#skF_7',k1_tarski('#skF_8'))) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_103,plain,(
    r2_hidden('#skF_1','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_75,c_30])).

tff(c_80,plain,(
    ! [C_33,B_34,D_35] :
      ( r2_hidden(k4_tarski(C_33,B_34),k2_zfmisc_1(k1_tarski(C_33),D_35))
      | ~ r2_hidden(B_34,D_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_91,plain,(
    ! [C_33,B_34,D_35] :
      ( r2_hidden(C_33,k1_tarski(C_33))
      | ~ r2_hidden(B_34,D_35) ) ),
    inference(resolution,[status(thm)],[c_80,c_12])).

tff(c_94,plain,(
    ! [B_34,D_35] : ~ r2_hidden(B_34,D_35) ),
    inference(splitLeft,[status(thm)],[c_91])).

tff(c_95,plain,(
    r2_hidden('#skF_1','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_75,c_30])).

tff(c_100,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_95])).

tff(c_101,plain,(
    ! [C_33] : r2_hidden(C_33,k1_tarski(C_33)) ),
    inference(splitRight,[status(thm)],[c_91])).

tff(c_8,plain,(
    ! [A_7,B_8,C_9,D_10] :
      ( r2_hidden(k4_tarski(A_7,B_8),k2_zfmisc_1(C_9,D_10))
      | ~ r2_hidden(B_8,D_10)
      | ~ r2_hidden(A_7,C_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_74,plain,(
    '#skF_2' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_28])).

tff(c_26,plain,
    ( ~ r2_hidden(k4_tarski('#skF_1','#skF_2'),k2_zfmisc_1('#skF_3',k1_tarski('#skF_4')))
    | r2_hidden(k4_tarski('#skF_5','#skF_6'),k2_zfmisc_1('#skF_7',k1_tarski('#skF_8'))) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_138,plain,
    ( ~ r2_hidden(k4_tarski('#skF_1','#skF_4'),k2_zfmisc_1('#skF_3',k1_tarski('#skF_4')))
    | r2_hidden(k4_tarski('#skF_5','#skF_6'),k2_zfmisc_1('#skF_7',k1_tarski('#skF_8'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_26])).

tff(c_139,plain,(
    ~ r2_hidden(k4_tarski('#skF_1','#skF_4'),k2_zfmisc_1('#skF_3',k1_tarski('#skF_4'))) ),
    inference(negUnitSimplification,[status(thm)],[c_75,c_138])).

tff(c_142,plain,
    ( ~ r2_hidden('#skF_4',k1_tarski('#skF_4'))
    | ~ r2_hidden('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_8,c_139])).

tff(c_146,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_101,c_142])).

tff(c_148,plain,(
    r2_hidden('#skF_5','#skF_7') ),
    inference(splitRight,[status(thm)],[c_22])).

tff(c_147,plain,
    ( '#skF_6' != '#skF_8'
    | '#skF_2' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_22])).

tff(c_149,plain,(
    '#skF_6' != '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_147])).

tff(c_170,plain,(
    r2_hidden(k4_tarski('#skF_5','#skF_6'),k2_zfmisc_1('#skF_7',k1_tarski('#skF_8'))) ),
    inference(splitLeft,[status(thm)],[c_28])).

tff(c_177,plain,(
    ! [B_52,D_53,A_54,C_55] :
      ( r2_hidden(B_52,D_53)
      | ~ r2_hidden(k4_tarski(A_54,B_52),k2_zfmisc_1(C_55,D_53)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_181,plain,(
    r2_hidden('#skF_6',k1_tarski('#skF_8')) ),
    inference(resolution,[status(thm)],[c_170,c_177])).

tff(c_209,plain,(
    ! [A_64,B_65,C_66,D_67] :
      ( r2_hidden(k4_tarski(A_64,B_65),k2_zfmisc_1(C_66,D_67))
      | ~ r2_hidden(B_65,D_67)
      | ~ r2_hidden(A_64,C_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_18,plain,(
    ! [C_13,A_11,B_12,D_14] :
      ( C_13 = A_11
      | ~ r2_hidden(k4_tarski(A_11,B_12),k2_zfmisc_1(k1_tarski(C_13),D_14)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_220,plain,(
    ! [C_13,A_64,B_65,D_67] :
      ( C_13 = A_64
      | ~ r2_hidden(B_65,D_67)
      | ~ r2_hidden(A_64,k1_tarski(C_13)) ) ),
    inference(resolution,[status(thm)],[c_209,c_18])).

tff(c_223,plain,(
    ! [B_65,D_67] : ~ r2_hidden(B_65,D_67) ),
    inference(splitLeft,[status(thm)],[c_220])).

tff(c_183,plain,(
    ! [C_60,B_61,D_62] :
      ( r2_hidden(k4_tarski(C_60,B_61),k2_zfmisc_1(k1_tarski(C_60),D_62))
      | ~ r2_hidden(B_61,D_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_196,plain,(
    ! [C_60,B_61,D_62] :
      ( r2_hidden(C_60,k1_tarski(C_60))
      | ~ r2_hidden(B_61,D_62) ) ),
    inference(resolution,[status(thm)],[c_183,c_12])).

tff(c_197,plain,(
    ! [B_61,D_62] : ~ r2_hidden(B_61,D_62) ),
    inference(splitLeft,[status(thm)],[c_196])).

tff(c_205,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_197,c_181])).

tff(c_206,plain,(
    ! [C_60] : r2_hidden(C_60,k1_tarski(C_60)) ),
    inference(splitRight,[status(thm)],[c_196])).

tff(c_234,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_223,c_206])).

tff(c_236,plain,(
    ! [C_68,A_69] :
      ( C_68 = A_69
      | ~ r2_hidden(A_69,k1_tarski(C_68)) ) ),
    inference(splitRight,[status(thm)],[c_220])).

tff(c_242,plain,(
    '#skF_6' = '#skF_8' ),
    inference(resolution,[status(thm)],[c_181,c_236])).

tff(c_248,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_149,c_242])).

tff(c_250,plain,(
    ~ r2_hidden(k4_tarski('#skF_5','#skF_6'),k2_zfmisc_1('#skF_7',k1_tarski('#skF_8'))) ),
    inference(splitRight,[status(thm)],[c_28])).

tff(c_255,plain,(
    r2_hidden(k4_tarski('#skF_5','#skF_6'),k2_zfmisc_1('#skF_7',k1_tarski('#skF_8'))) ),
    inference(splitLeft,[status(thm)],[c_30])).

tff(c_256,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_250,c_255])).

tff(c_257,plain,(
    r2_hidden('#skF_1','#skF_3') ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_262,plain,(
    ! [C_82,B_83,D_84] :
      ( r2_hidden(k4_tarski(C_82,B_83),k2_zfmisc_1(k1_tarski(C_82),D_84))
      | ~ r2_hidden(B_83,D_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_272,plain,(
    ! [C_82,B_83,D_84] :
      ( r2_hidden(C_82,k1_tarski(C_82))
      | ~ r2_hidden(B_83,D_84) ) ),
    inference(resolution,[status(thm)],[c_262,c_12])).

tff(c_278,plain,(
    ! [B_83,D_84] : ~ r2_hidden(B_83,D_84) ),
    inference(splitLeft,[status(thm)],[c_272])).

tff(c_284,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_278,c_257])).

tff(c_285,plain,(
    ! [C_82] : r2_hidden(C_82,k1_tarski(C_82)) ),
    inference(splitRight,[status(thm)],[c_272])).

tff(c_249,plain,(
    '#skF_2' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_28])).

tff(c_307,plain,
    ( ~ r2_hidden(k4_tarski('#skF_1','#skF_4'),k2_zfmisc_1('#skF_3',k1_tarski('#skF_4')))
    | r2_hidden(k4_tarski('#skF_5','#skF_6'),k2_zfmisc_1('#skF_7',k1_tarski('#skF_8'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_249,c_26])).

tff(c_308,plain,(
    ~ r2_hidden(k4_tarski('#skF_1','#skF_4'),k2_zfmisc_1('#skF_3',k1_tarski('#skF_4'))) ),
    inference(negUnitSimplification,[status(thm)],[c_250,c_307])).

tff(c_311,plain,
    ( ~ r2_hidden('#skF_4',k1_tarski('#skF_4'))
    | ~ r2_hidden('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_8,c_308])).

tff(c_315,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_257,c_285,c_311])).

tff(c_317,plain,(
    '#skF_6' = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_147])).

tff(c_24,plain,
    ( r2_hidden('#skF_1','#skF_3')
    | '#skF_6' != '#skF_8'
    | ~ r2_hidden('#skF_5','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_336,plain,(
    r2_hidden('#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_148,c_317,c_24])).

tff(c_350,plain,(
    ! [C_107,B_108,D_109] :
      ( r2_hidden(k4_tarski(C_107,B_108),k2_zfmisc_1(k1_tarski(C_107),D_109))
      | ~ r2_hidden(B_108,D_109) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_363,plain,(
    ! [C_107,B_108,D_109] :
      ( r2_hidden(C_107,k1_tarski(C_107))
      | ~ r2_hidden(B_108,D_109) ) ),
    inference(resolution,[status(thm)],[c_350,c_12])).

tff(c_364,plain,(
    ! [B_108,D_109] : ~ r2_hidden(B_108,D_109) ),
    inference(splitLeft,[status(thm)],[c_363])).

tff(c_370,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_364,c_336])).

tff(c_371,plain,(
    ! [C_107] : r2_hidden(C_107,k1_tarski(C_107)) ),
    inference(splitRight,[status(thm)],[c_363])).

tff(c_316,plain,(
    '#skF_2' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_147])).

tff(c_20,plain,
    ( ~ r2_hidden(k4_tarski('#skF_1','#skF_2'),k2_zfmisc_1('#skF_3',k1_tarski('#skF_4')))
    | '#skF_6' != '#skF_8'
    | ~ r2_hidden('#skF_5','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_405,plain,(
    ~ r2_hidden(k4_tarski('#skF_1','#skF_4'),k2_zfmisc_1('#skF_3',k1_tarski('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_148,c_317,c_316,c_20])).

tff(c_408,plain,
    ( ~ r2_hidden('#skF_4',k1_tarski('#skF_4'))
    | ~ r2_hidden('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_8,c_405])).

tff(c_412,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_336,c_371,c_408])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 15:04:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.55/1.64  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.55/1.65  
% 2.55/1.65  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.55/1.66  %$ r2_hidden > k2_enumset1 > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_tarski > #nlpp > k1_tarski > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_8 > #skF_4
% 2.55/1.66  
% 2.55/1.66  %Foreground sorts:
% 2.55/1.66  
% 2.55/1.66  
% 2.55/1.66  %Background operators:
% 2.55/1.66  
% 2.55/1.66  
% 2.55/1.66  %Foreground operators:
% 2.55/1.66  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.55/1.66  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.55/1.66  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.55/1.66  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.55/1.66  tff('#skF_7', type, '#skF_7': $i).
% 2.55/1.66  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.55/1.66  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.55/1.66  tff('#skF_5', type, '#skF_5': $i).
% 2.55/1.66  tff('#skF_6', type, '#skF_6': $i).
% 2.55/1.66  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.55/1.66  tff('#skF_2', type, '#skF_2': $i).
% 2.55/1.66  tff('#skF_3', type, '#skF_3': $i).
% 2.55/1.66  tff('#skF_1', type, '#skF_1': $i).
% 2.55/1.66  tff('#skF_8', type, '#skF_8': $i).
% 2.55/1.66  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.55/1.66  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.55/1.66  tff('#skF_4', type, '#skF_4': $i).
% 2.55/1.66  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.55/1.66  
% 2.79/1.69  tff(f_50, negated_conjecture, ~(![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, k1_tarski(D))) <=> (r2_hidden(A, C) & (B = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t129_zfmisc_1)).
% 2.79/1.69  tff(f_37, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, D)) <=> (r2_hidden(A, C) & r2_hidden(B, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 2.79/1.69  tff(f_43, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(k1_tarski(C), D)) <=> ((A = C) & r2_hidden(B, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t128_zfmisc_1)).
% 2.79/1.69  tff(c_22, plain, ('#skF_2'='#skF_4' | '#skF_6'!='#skF_8' | ~r2_hidden('#skF_5', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.79/1.69  tff(c_40, plain, (~r2_hidden('#skF_5', '#skF_7')), inference(splitLeft, [status(thm)], [c_22])).
% 2.79/1.69  tff(c_28, plain, ('#skF_2'='#skF_4' | r2_hidden(k4_tarski('#skF_5', '#skF_6'), k2_zfmisc_1('#skF_7', k1_tarski('#skF_8')))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.79/1.69  tff(c_62, plain, (r2_hidden(k4_tarski('#skF_5', '#skF_6'), k2_zfmisc_1('#skF_7', k1_tarski('#skF_8')))), inference(splitLeft, [status(thm)], [c_28])).
% 2.79/1.69  tff(c_12, plain, (![A_7, C_9, B_8, D_10]: (r2_hidden(A_7, C_9) | ~r2_hidden(k4_tarski(A_7, B_8), k2_zfmisc_1(C_9, D_10)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.79/1.69  tff(c_68, plain, (r2_hidden('#skF_5', '#skF_7')), inference(resolution, [status(thm)], [c_62, c_12])).
% 2.79/1.69  tff(c_73, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40, c_68])).
% 2.79/1.69  tff(c_75, plain, (~r2_hidden(k4_tarski('#skF_5', '#skF_6'), k2_zfmisc_1('#skF_7', k1_tarski('#skF_8')))), inference(splitRight, [status(thm)], [c_28])).
% 2.79/1.69  tff(c_30, plain, (r2_hidden('#skF_1', '#skF_3') | r2_hidden(k4_tarski('#skF_5', '#skF_6'), k2_zfmisc_1('#skF_7', k1_tarski('#skF_8')))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.79/1.69  tff(c_103, plain, (r2_hidden('#skF_1', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_75, c_30])).
% 2.79/1.69  tff(c_80, plain, (![C_33, B_34, D_35]: (r2_hidden(k4_tarski(C_33, B_34), k2_zfmisc_1(k1_tarski(C_33), D_35)) | ~r2_hidden(B_34, D_35))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.79/1.69  tff(c_91, plain, (![C_33, B_34, D_35]: (r2_hidden(C_33, k1_tarski(C_33)) | ~r2_hidden(B_34, D_35))), inference(resolution, [status(thm)], [c_80, c_12])).
% 2.79/1.69  tff(c_94, plain, (![B_34, D_35]: (~r2_hidden(B_34, D_35))), inference(splitLeft, [status(thm)], [c_91])).
% 2.79/1.69  tff(c_95, plain, (r2_hidden('#skF_1', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_75, c_30])).
% 2.79/1.69  tff(c_100, plain, $false, inference(negUnitSimplification, [status(thm)], [c_94, c_95])).
% 2.79/1.69  tff(c_101, plain, (![C_33]: (r2_hidden(C_33, k1_tarski(C_33)))), inference(splitRight, [status(thm)], [c_91])).
% 2.79/1.69  tff(c_8, plain, (![A_7, B_8, C_9, D_10]: (r2_hidden(k4_tarski(A_7, B_8), k2_zfmisc_1(C_9, D_10)) | ~r2_hidden(B_8, D_10) | ~r2_hidden(A_7, C_9))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.79/1.69  tff(c_74, plain, ('#skF_2'='#skF_4'), inference(splitRight, [status(thm)], [c_28])).
% 2.79/1.69  tff(c_26, plain, (~r2_hidden(k4_tarski('#skF_1', '#skF_2'), k2_zfmisc_1('#skF_3', k1_tarski('#skF_4'))) | r2_hidden(k4_tarski('#skF_5', '#skF_6'), k2_zfmisc_1('#skF_7', k1_tarski('#skF_8')))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.79/1.69  tff(c_138, plain, (~r2_hidden(k4_tarski('#skF_1', '#skF_4'), k2_zfmisc_1('#skF_3', k1_tarski('#skF_4'))) | r2_hidden(k4_tarski('#skF_5', '#skF_6'), k2_zfmisc_1('#skF_7', k1_tarski('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_26])).
% 2.79/1.69  tff(c_139, plain, (~r2_hidden(k4_tarski('#skF_1', '#skF_4'), k2_zfmisc_1('#skF_3', k1_tarski('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_75, c_138])).
% 2.79/1.69  tff(c_142, plain, (~r2_hidden('#skF_4', k1_tarski('#skF_4')) | ~r2_hidden('#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_8, c_139])).
% 2.79/1.69  tff(c_146, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_103, c_101, c_142])).
% 2.79/1.69  tff(c_148, plain, (r2_hidden('#skF_5', '#skF_7')), inference(splitRight, [status(thm)], [c_22])).
% 2.79/1.69  tff(c_147, plain, ('#skF_6'!='#skF_8' | '#skF_2'='#skF_4'), inference(splitRight, [status(thm)], [c_22])).
% 2.79/1.69  tff(c_149, plain, ('#skF_6'!='#skF_8'), inference(splitLeft, [status(thm)], [c_147])).
% 2.79/1.69  tff(c_170, plain, (r2_hidden(k4_tarski('#skF_5', '#skF_6'), k2_zfmisc_1('#skF_7', k1_tarski('#skF_8')))), inference(splitLeft, [status(thm)], [c_28])).
% 2.79/1.69  tff(c_177, plain, (![B_52, D_53, A_54, C_55]: (r2_hidden(B_52, D_53) | ~r2_hidden(k4_tarski(A_54, B_52), k2_zfmisc_1(C_55, D_53)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.79/1.69  tff(c_181, plain, (r2_hidden('#skF_6', k1_tarski('#skF_8'))), inference(resolution, [status(thm)], [c_170, c_177])).
% 2.79/1.69  tff(c_209, plain, (![A_64, B_65, C_66, D_67]: (r2_hidden(k4_tarski(A_64, B_65), k2_zfmisc_1(C_66, D_67)) | ~r2_hidden(B_65, D_67) | ~r2_hidden(A_64, C_66))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.79/1.69  tff(c_18, plain, (![C_13, A_11, B_12, D_14]: (C_13=A_11 | ~r2_hidden(k4_tarski(A_11, B_12), k2_zfmisc_1(k1_tarski(C_13), D_14)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.79/1.69  tff(c_220, plain, (![C_13, A_64, B_65, D_67]: (C_13=A_64 | ~r2_hidden(B_65, D_67) | ~r2_hidden(A_64, k1_tarski(C_13)))), inference(resolution, [status(thm)], [c_209, c_18])).
% 2.79/1.69  tff(c_223, plain, (![B_65, D_67]: (~r2_hidden(B_65, D_67))), inference(splitLeft, [status(thm)], [c_220])).
% 2.79/1.69  tff(c_183, plain, (![C_60, B_61, D_62]: (r2_hidden(k4_tarski(C_60, B_61), k2_zfmisc_1(k1_tarski(C_60), D_62)) | ~r2_hidden(B_61, D_62))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.79/1.69  tff(c_196, plain, (![C_60, B_61, D_62]: (r2_hidden(C_60, k1_tarski(C_60)) | ~r2_hidden(B_61, D_62))), inference(resolution, [status(thm)], [c_183, c_12])).
% 2.79/1.69  tff(c_197, plain, (![B_61, D_62]: (~r2_hidden(B_61, D_62))), inference(splitLeft, [status(thm)], [c_196])).
% 2.79/1.69  tff(c_205, plain, $false, inference(negUnitSimplification, [status(thm)], [c_197, c_181])).
% 2.79/1.69  tff(c_206, plain, (![C_60]: (r2_hidden(C_60, k1_tarski(C_60)))), inference(splitRight, [status(thm)], [c_196])).
% 2.79/1.69  tff(c_234, plain, $false, inference(negUnitSimplification, [status(thm)], [c_223, c_206])).
% 2.79/1.69  tff(c_236, plain, (![C_68, A_69]: (C_68=A_69 | ~r2_hidden(A_69, k1_tarski(C_68)))), inference(splitRight, [status(thm)], [c_220])).
% 2.79/1.69  tff(c_242, plain, ('#skF_6'='#skF_8'), inference(resolution, [status(thm)], [c_181, c_236])).
% 2.79/1.69  tff(c_248, plain, $false, inference(negUnitSimplification, [status(thm)], [c_149, c_242])).
% 2.79/1.69  tff(c_250, plain, (~r2_hidden(k4_tarski('#skF_5', '#skF_6'), k2_zfmisc_1('#skF_7', k1_tarski('#skF_8')))), inference(splitRight, [status(thm)], [c_28])).
% 2.79/1.69  tff(c_255, plain, (r2_hidden(k4_tarski('#skF_5', '#skF_6'), k2_zfmisc_1('#skF_7', k1_tarski('#skF_8')))), inference(splitLeft, [status(thm)], [c_30])).
% 2.79/1.69  tff(c_256, plain, $false, inference(negUnitSimplification, [status(thm)], [c_250, c_255])).
% 2.79/1.69  tff(c_257, plain, (r2_hidden('#skF_1', '#skF_3')), inference(splitRight, [status(thm)], [c_30])).
% 2.79/1.69  tff(c_262, plain, (![C_82, B_83, D_84]: (r2_hidden(k4_tarski(C_82, B_83), k2_zfmisc_1(k1_tarski(C_82), D_84)) | ~r2_hidden(B_83, D_84))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.79/1.69  tff(c_272, plain, (![C_82, B_83, D_84]: (r2_hidden(C_82, k1_tarski(C_82)) | ~r2_hidden(B_83, D_84))), inference(resolution, [status(thm)], [c_262, c_12])).
% 2.79/1.69  tff(c_278, plain, (![B_83, D_84]: (~r2_hidden(B_83, D_84))), inference(splitLeft, [status(thm)], [c_272])).
% 2.79/1.69  tff(c_284, plain, $false, inference(negUnitSimplification, [status(thm)], [c_278, c_257])).
% 2.79/1.69  tff(c_285, plain, (![C_82]: (r2_hidden(C_82, k1_tarski(C_82)))), inference(splitRight, [status(thm)], [c_272])).
% 2.79/1.69  tff(c_249, plain, ('#skF_2'='#skF_4'), inference(splitRight, [status(thm)], [c_28])).
% 2.79/1.69  tff(c_307, plain, (~r2_hidden(k4_tarski('#skF_1', '#skF_4'), k2_zfmisc_1('#skF_3', k1_tarski('#skF_4'))) | r2_hidden(k4_tarski('#skF_5', '#skF_6'), k2_zfmisc_1('#skF_7', k1_tarski('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_249, c_26])).
% 2.79/1.69  tff(c_308, plain, (~r2_hidden(k4_tarski('#skF_1', '#skF_4'), k2_zfmisc_1('#skF_3', k1_tarski('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_250, c_307])).
% 2.79/1.69  tff(c_311, plain, (~r2_hidden('#skF_4', k1_tarski('#skF_4')) | ~r2_hidden('#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_8, c_308])).
% 2.79/1.69  tff(c_315, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_257, c_285, c_311])).
% 2.79/1.69  tff(c_317, plain, ('#skF_6'='#skF_8'), inference(splitRight, [status(thm)], [c_147])).
% 2.79/1.69  tff(c_24, plain, (r2_hidden('#skF_1', '#skF_3') | '#skF_6'!='#skF_8' | ~r2_hidden('#skF_5', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.79/1.69  tff(c_336, plain, (r2_hidden('#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_148, c_317, c_24])).
% 2.79/1.69  tff(c_350, plain, (![C_107, B_108, D_109]: (r2_hidden(k4_tarski(C_107, B_108), k2_zfmisc_1(k1_tarski(C_107), D_109)) | ~r2_hidden(B_108, D_109))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.79/1.69  tff(c_363, plain, (![C_107, B_108, D_109]: (r2_hidden(C_107, k1_tarski(C_107)) | ~r2_hidden(B_108, D_109))), inference(resolution, [status(thm)], [c_350, c_12])).
% 2.79/1.69  tff(c_364, plain, (![B_108, D_109]: (~r2_hidden(B_108, D_109))), inference(splitLeft, [status(thm)], [c_363])).
% 2.79/1.69  tff(c_370, plain, $false, inference(negUnitSimplification, [status(thm)], [c_364, c_336])).
% 2.79/1.69  tff(c_371, plain, (![C_107]: (r2_hidden(C_107, k1_tarski(C_107)))), inference(splitRight, [status(thm)], [c_363])).
% 2.79/1.69  tff(c_316, plain, ('#skF_2'='#skF_4'), inference(splitRight, [status(thm)], [c_147])).
% 2.79/1.69  tff(c_20, plain, (~r2_hidden(k4_tarski('#skF_1', '#skF_2'), k2_zfmisc_1('#skF_3', k1_tarski('#skF_4'))) | '#skF_6'!='#skF_8' | ~r2_hidden('#skF_5', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.79/1.69  tff(c_405, plain, (~r2_hidden(k4_tarski('#skF_1', '#skF_4'), k2_zfmisc_1('#skF_3', k1_tarski('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_148, c_317, c_316, c_20])).
% 2.79/1.69  tff(c_408, plain, (~r2_hidden('#skF_4', k1_tarski('#skF_4')) | ~r2_hidden('#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_8, c_405])).
% 2.79/1.69  tff(c_412, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_336, c_371, c_408])).
% 2.79/1.69  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.79/1.69  
% 2.79/1.69  Inference rules
% 2.79/1.69  ----------------------
% 2.79/1.69  #Ref     : 0
% 2.79/1.69  #Sup     : 59
% 2.79/1.69  #Fact    : 0
% 2.79/1.69  #Define  : 0
% 2.79/1.69  #Split   : 12
% 2.79/1.69  #Chain   : 0
% 2.79/1.69  #Close   : 0
% 2.79/1.69  
% 2.79/1.69  Ordering : KBO
% 2.79/1.69  
% 2.79/1.69  Simplification rules
% 2.79/1.69  ----------------------
% 2.79/1.69  #Subsume      : 44
% 2.79/1.69  #Demod        : 26
% 2.79/1.69  #Tautology    : 46
% 2.79/1.69  #SimpNegUnit  : 48
% 2.79/1.69  #BackRed      : 17
% 2.79/1.69  
% 2.79/1.69  #Partial instantiations: 0
% 2.79/1.69  #Strategies tried      : 1
% 2.79/1.69  
% 2.79/1.69  Timing (in seconds)
% 2.79/1.69  ----------------------
% 2.79/1.70  Preprocessing        : 0.48
% 2.79/1.70  Parsing              : 0.24
% 2.79/1.70  CNF conversion       : 0.03
% 2.79/1.70  Main loop            : 0.38
% 2.79/1.70  Inferencing          : 0.14
% 2.79/1.70  Reduction            : 0.11
% 2.79/1.70  Demodulation         : 0.06
% 2.79/1.70  BG Simplification    : 0.02
% 2.79/1.70  Subsumption          : 0.07
% 2.79/1.70  Abstraction          : 0.02
% 2.79/1.70  MUC search           : 0.00
% 2.79/1.70  Cooper               : 0.00
% 2.79/1.70  Total                : 0.93
% 2.79/1.70  Index Insertion      : 0.00
% 2.79/1.70  Index Deletion       : 0.00
% 2.79/1.70  Index Matching       : 0.00
% 2.79/1.70  BG Taut test         : 0.00
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0239+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:35:57 EST 2020

% Result     : Theorem 1.86s
% Output     : CNFRefutation 2.09s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 147 expanded)
%              Number of leaves         :   20 (  57 expanded)
%              Depth                    :    9
%              Number of atoms          :   79 ( 276 expanded)
%              Number of equality atoms :   31 ( 159 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k4_tarski > k2_zfmisc_1 > #nlpp > k1_tarski > #skF_7 > #skF_10 > #skF_5 > #skF_6 > #skF_3 > #skF_9 > #skF_8 > #skF_4 > #skF_2 > #skF_1

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

tff('#skF_10',type,(
    '#skF_10': $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_31,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(f_37,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,D))
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).

tff(f_44,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(k1_tarski(C),k1_tarski(D)))
      <=> ( A = C
          & B = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_zfmisc_1)).

tff(c_4,plain,(
    ! [C_5] : r2_hidden(C_5,k1_tarski(C_5)) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_289,plain,(
    ! [A_79,B_80,C_81,D_82] :
      ( r2_hidden(k4_tarski(A_79,B_80),k2_zfmisc_1(C_81,D_82))
      | ~ r2_hidden(B_80,D_82)
      | ~ r2_hidden(A_79,C_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_14,plain,(
    ! [A_6,B_7,C_8,D_9] :
      ( r2_hidden(k4_tarski(A_6,B_7),k2_zfmisc_1(C_8,D_9))
      | ~ r2_hidden(B_7,D_9)
      | ~ r2_hidden(A_6,C_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_22,plain,
    ( '#skF_6' = '#skF_4'
    | '#skF_10' != '#skF_8'
    | '#skF_7' != '#skF_9' ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_32,plain,(
    '#skF_7' != '#skF_9' ),
    inference(splitLeft,[status(thm)],[c_22])).

tff(c_28,plain,
    ( '#skF_6' = '#skF_4'
    | r2_hidden(k4_tarski('#skF_7','#skF_8'),k2_zfmisc_1(k1_tarski('#skF_9'),k1_tarski('#skF_10'))) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_42,plain,(
    r2_hidden(k4_tarski('#skF_7','#skF_8'),k2_zfmisc_1(k1_tarski('#skF_9'),k1_tarski('#skF_10'))) ),
    inference(splitLeft,[status(thm)],[c_28])).

tff(c_18,plain,(
    ! [A_6,C_8,B_7,D_9] :
      ( r2_hidden(A_6,C_8)
      | ~ r2_hidden(k4_tarski(A_6,B_7),k2_zfmisc_1(C_8,D_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_51,plain,(
    r2_hidden('#skF_7',k1_tarski('#skF_9')) ),
    inference(resolution,[status(thm)],[c_42,c_18])).

tff(c_2,plain,(
    ! [C_5,A_1] :
      ( C_5 = A_1
      | ~ r2_hidden(C_5,k1_tarski(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_65,plain,(
    '#skF_7' = '#skF_9' ),
    inference(resolution,[status(thm)],[c_51,c_2])).

tff(c_69,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_65])).

tff(c_71,plain,(
    ~ r2_hidden(k4_tarski('#skF_7','#skF_8'),k2_zfmisc_1(k1_tarski('#skF_9'),k1_tarski('#skF_10'))) ),
    inference(splitRight,[status(thm)],[c_28])).

tff(c_30,plain,
    ( '#skF_5' = '#skF_3'
    | r2_hidden(k4_tarski('#skF_7','#skF_8'),k2_zfmisc_1(k1_tarski('#skF_9'),k1_tarski('#skF_10'))) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_76,plain,(
    '#skF_5' = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_71,c_30])).

tff(c_70,plain,(
    '#skF_6' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_28])).

tff(c_26,plain,
    ( ~ r2_hidden(k4_tarski('#skF_3','#skF_4'),k2_zfmisc_1(k1_tarski('#skF_5'),k1_tarski('#skF_6')))
    | r2_hidden(k4_tarski('#skF_7','#skF_8'),k2_zfmisc_1(k1_tarski('#skF_9'),k1_tarski('#skF_10'))) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_132,plain,
    ( ~ r2_hidden(k4_tarski('#skF_3','#skF_4'),k2_zfmisc_1(k1_tarski('#skF_3'),k1_tarski('#skF_4')))
    | r2_hidden(k4_tarski('#skF_7','#skF_8'),k2_zfmisc_1(k1_tarski('#skF_9'),k1_tarski('#skF_10'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_70,c_26])).

tff(c_133,plain,(
    ~ r2_hidden(k4_tarski('#skF_3','#skF_4'),k2_zfmisc_1(k1_tarski('#skF_3'),k1_tarski('#skF_4'))) ),
    inference(negUnitSimplification,[status(thm)],[c_71,c_132])).

tff(c_136,plain,
    ( ~ r2_hidden('#skF_4',k1_tarski('#skF_4'))
    | ~ r2_hidden('#skF_3',k1_tarski('#skF_3')) ),
    inference(resolution,[status(thm)],[c_14,c_133])).

tff(c_140,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_4,c_136])).

tff(c_142,plain,(
    '#skF_7' = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_22])).

tff(c_141,plain,
    ( '#skF_10' != '#skF_8'
    | '#skF_6' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_22])).

tff(c_147,plain,(
    '#skF_10' != '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_141])).

tff(c_158,plain,
    ( '#skF_6' = '#skF_4'
    | r2_hidden(k4_tarski('#skF_9','#skF_8'),k2_zfmisc_1(k1_tarski('#skF_9'),k1_tarski('#skF_10'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_142,c_28])).

tff(c_159,plain,(
    r2_hidden(k4_tarski('#skF_9','#skF_8'),k2_zfmisc_1(k1_tarski('#skF_9'),k1_tarski('#skF_10'))) ),
    inference(splitLeft,[status(thm)],[c_158])).

tff(c_16,plain,(
    ! [B_7,D_9,A_6,C_8] :
      ( r2_hidden(B_7,D_9)
      | ~ r2_hidden(k4_tarski(A_6,B_7),k2_zfmisc_1(C_8,D_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_166,plain,(
    r2_hidden('#skF_8',k1_tarski('#skF_10')) ),
    inference(resolution,[status(thm)],[c_159,c_16])).

tff(c_172,plain,(
    '#skF_10' = '#skF_8' ),
    inference(resolution,[status(thm)],[c_166,c_2])).

tff(c_176,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_147,c_172])).

tff(c_178,plain,(
    ~ r2_hidden(k4_tarski('#skF_9','#skF_8'),k2_zfmisc_1(k1_tarski('#skF_9'),k1_tarski('#skF_10'))) ),
    inference(splitRight,[status(thm)],[c_158])).

tff(c_183,plain,
    ( '#skF_5' = '#skF_3'
    | r2_hidden(k4_tarski('#skF_9','#skF_8'),k2_zfmisc_1(k1_tarski('#skF_9'),k1_tarski('#skF_10'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_142,c_30])).

tff(c_184,plain,(
    '#skF_5' = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_178,c_183])).

tff(c_177,plain,(
    '#skF_6' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_158])).

tff(c_244,plain,
    ( ~ r2_hidden(k4_tarski('#skF_3','#skF_4'),k2_zfmisc_1(k1_tarski('#skF_3'),k1_tarski('#skF_4')))
    | r2_hidden(k4_tarski('#skF_9','#skF_8'),k2_zfmisc_1(k1_tarski('#skF_9'),k1_tarski('#skF_10'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_142,c_184,c_177,c_26])).

tff(c_245,plain,(
    ~ r2_hidden(k4_tarski('#skF_3','#skF_4'),k2_zfmisc_1(k1_tarski('#skF_3'),k1_tarski('#skF_4'))) ),
    inference(negUnitSimplification,[status(thm)],[c_178,c_244])).

tff(c_248,plain,
    ( ~ r2_hidden('#skF_4',k1_tarski('#skF_4'))
    | ~ r2_hidden('#skF_3',k1_tarski('#skF_3')) ),
    inference(resolution,[status(thm)],[c_14,c_245])).

tff(c_252,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_4,c_248])).

tff(c_254,plain,(
    '#skF_10' = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_141])).

tff(c_24,plain,
    ( '#skF_5' = '#skF_3'
    | '#skF_10' != '#skF_8'
    | '#skF_7' != '#skF_9' ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_264,plain,(
    '#skF_5' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_142,c_254,c_24])).

tff(c_253,plain,(
    '#skF_6' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_141])).

tff(c_20,plain,
    ( ~ r2_hidden(k4_tarski('#skF_3','#skF_4'),k2_zfmisc_1(k1_tarski('#skF_5'),k1_tarski('#skF_6')))
    | '#skF_10' != '#skF_8'
    | '#skF_7' != '#skF_9' ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_281,plain,(
    ~ r2_hidden(k4_tarski('#skF_3','#skF_4'),k2_zfmisc_1(k1_tarski('#skF_3'),k1_tarski('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_142,c_254,c_264,c_253,c_20])).

tff(c_292,plain,
    ( ~ r2_hidden('#skF_4',k1_tarski('#skF_4'))
    | ~ r2_hidden('#skF_3',k1_tarski('#skF_3')) ),
    inference(resolution,[status(thm)],[c_289,c_281])).

tff(c_302,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_4,c_292])).

%------------------------------------------------------------------------------

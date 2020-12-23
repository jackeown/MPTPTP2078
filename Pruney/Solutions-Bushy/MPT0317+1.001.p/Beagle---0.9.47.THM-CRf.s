%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0317+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:36:05 EST 2020

% Result     : Theorem 1.47s
% Output     : CNFRefutation 1.47s
% Verified   : 
% Statistics : Number of formulae       :   65 ( 119 expanded)
%              Number of leaves         :   20 (  48 expanded)
%              Depth                    :    6
%              Number of atoms          :   74 ( 213 expanded)
%              Number of equality atoms :   17 (  69 expanded)
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

tff(f_44,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,k1_tarski(D)))
      <=> ( r2_hidden(A,C)
          & B = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t129_zfmisc_1)).

tff(f_37,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,D))
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(c_22,plain,
    ( '#skF_6' = '#skF_4'
    | '#skF_10' != '#skF_8'
    | ~ r2_hidden('#skF_7','#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_38,plain,(
    ~ r2_hidden('#skF_7','#skF_9') ),
    inference(splitLeft,[status(thm)],[c_22])).

tff(c_28,plain,
    ( '#skF_6' = '#skF_4'
    | r2_hidden(k4_tarski('#skF_7','#skF_8'),k2_zfmisc_1('#skF_9',k1_tarski('#skF_10'))) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_41,plain,(
    r2_hidden(k4_tarski('#skF_7','#skF_8'),k2_zfmisc_1('#skF_9',k1_tarski('#skF_10'))) ),
    inference(splitLeft,[status(thm)],[c_28])).

tff(c_18,plain,(
    ! [A_6,C_8,B_7,D_9] :
      ( r2_hidden(A_6,C_8)
      | ~ r2_hidden(k4_tarski(A_6,B_7),k2_zfmisc_1(C_8,D_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_44,plain,(
    r2_hidden('#skF_7','#skF_9') ),
    inference(resolution,[status(thm)],[c_41,c_18])).

tff(c_51,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_44])).

tff(c_53,plain,(
    ~ r2_hidden(k4_tarski('#skF_7','#skF_8'),k2_zfmisc_1('#skF_9',k1_tarski('#skF_10'))) ),
    inference(splitRight,[status(thm)],[c_28])).

tff(c_30,plain,
    ( r2_hidden('#skF_3','#skF_5')
    | r2_hidden(k4_tarski('#skF_7','#skF_8'),k2_zfmisc_1('#skF_9',k1_tarski('#skF_10'))) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_54,plain,(
    r2_hidden(k4_tarski('#skF_7','#skF_8'),k2_zfmisc_1('#skF_9',k1_tarski('#skF_10'))) ),
    inference(splitLeft,[status(thm)],[c_30])).

tff(c_59,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_53,c_54])).

tff(c_60,plain,(
    r2_hidden('#skF_3','#skF_5') ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_4,plain,(
    ! [C_5] : r2_hidden(C_5,k1_tarski(C_5)) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_14,plain,(
    ! [A_6,B_7,C_8,D_9] :
      ( r2_hidden(k4_tarski(A_6,B_7),k2_zfmisc_1(C_8,D_9))
      | ~ r2_hidden(B_7,D_9)
      | ~ r2_hidden(A_6,C_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_61,plain,(
    ~ r2_hidden(k4_tarski('#skF_7','#skF_8'),k2_zfmisc_1('#skF_9',k1_tarski('#skF_10'))) ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_52,plain,(
    '#skF_6' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_28])).

tff(c_26,plain,
    ( ~ r2_hidden(k4_tarski('#skF_3','#skF_4'),k2_zfmisc_1('#skF_5',k1_tarski('#skF_6')))
    | r2_hidden(k4_tarski('#skF_7','#skF_8'),k2_zfmisc_1('#skF_9',k1_tarski('#skF_10'))) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_117,plain,
    ( ~ r2_hidden(k4_tarski('#skF_3','#skF_4'),k2_zfmisc_1('#skF_5',k1_tarski('#skF_4')))
    | r2_hidden(k4_tarski('#skF_7','#skF_8'),k2_zfmisc_1('#skF_9',k1_tarski('#skF_10'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_26])).

tff(c_118,plain,(
    ~ r2_hidden(k4_tarski('#skF_3','#skF_4'),k2_zfmisc_1('#skF_5',k1_tarski('#skF_4'))) ),
    inference(negUnitSimplification,[status(thm)],[c_61,c_117])).

tff(c_121,plain,
    ( ~ r2_hidden('#skF_4',k1_tarski('#skF_4'))
    | ~ r2_hidden('#skF_3','#skF_5') ),
    inference(resolution,[status(thm)],[c_14,c_118])).

tff(c_125,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_4,c_121])).

tff(c_127,plain,(
    r2_hidden('#skF_7','#skF_9') ),
    inference(splitRight,[status(thm)],[c_22])).

tff(c_126,plain,
    ( '#skF_10' != '#skF_8'
    | '#skF_6' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_22])).

tff(c_128,plain,(
    '#skF_10' != '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_126])).

tff(c_131,plain,(
    r2_hidden(k4_tarski('#skF_7','#skF_8'),k2_zfmisc_1('#skF_9',k1_tarski('#skF_10'))) ),
    inference(splitLeft,[status(thm)],[c_28])).

tff(c_138,plain,(
    ! [B_39,D_40,A_41,C_42] :
      ( r2_hidden(B_39,D_40)
      | ~ r2_hidden(k4_tarski(A_41,B_39),k2_zfmisc_1(C_42,D_40)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_142,plain,(
    r2_hidden('#skF_8',k1_tarski('#skF_10')) ),
    inference(resolution,[status(thm)],[c_131,c_138])).

tff(c_2,plain,(
    ! [C_5,A_1] :
      ( C_5 = A_1
      | ~ r2_hidden(C_5,k1_tarski(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_145,plain,(
    '#skF_10' = '#skF_8' ),
    inference(resolution,[status(thm)],[c_142,c_2])).

tff(c_149,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_128,c_145])).

tff(c_151,plain,(
    ~ r2_hidden(k4_tarski('#skF_7','#skF_8'),k2_zfmisc_1('#skF_9',k1_tarski('#skF_10'))) ),
    inference(splitRight,[status(thm)],[c_28])).

tff(c_158,plain,(
    r2_hidden('#skF_3','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_151,c_30])).

tff(c_150,plain,(
    '#skF_6' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_28])).

tff(c_190,plain,
    ( ~ r2_hidden(k4_tarski('#skF_3','#skF_4'),k2_zfmisc_1('#skF_5',k1_tarski('#skF_4')))
    | r2_hidden(k4_tarski('#skF_7','#skF_8'),k2_zfmisc_1('#skF_9',k1_tarski('#skF_10'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_150,c_26])).

tff(c_191,plain,(
    ~ r2_hidden(k4_tarski('#skF_3','#skF_4'),k2_zfmisc_1('#skF_5',k1_tarski('#skF_4'))) ),
    inference(negUnitSimplification,[status(thm)],[c_151,c_190])).

tff(c_194,plain,
    ( ~ r2_hidden('#skF_4',k1_tarski('#skF_4'))
    | ~ r2_hidden('#skF_3','#skF_5') ),
    inference(resolution,[status(thm)],[c_14,c_191])).

tff(c_198,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_158,c_4,c_194])).

tff(c_200,plain,(
    '#skF_10' = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_126])).

tff(c_24,plain,
    ( r2_hidden('#skF_3','#skF_5')
    | '#skF_10' != '#skF_8'
    | ~ r2_hidden('#skF_7','#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_210,plain,(
    r2_hidden('#skF_3','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_127,c_200,c_24])).

tff(c_199,plain,(
    '#skF_6' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_126])).

tff(c_20,plain,
    ( ~ r2_hidden(k4_tarski('#skF_3','#skF_4'),k2_zfmisc_1('#skF_5',k1_tarski('#skF_6')))
    | '#skF_10' != '#skF_8'
    | ~ r2_hidden('#skF_7','#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_233,plain,(
    ~ r2_hidden(k4_tarski('#skF_3','#skF_4'),k2_zfmisc_1('#skF_5',k1_tarski('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_127,c_200,c_199,c_20])).

tff(c_236,plain,
    ( ~ r2_hidden('#skF_4',k1_tarski('#skF_4'))
    | ~ r2_hidden('#skF_3','#skF_5') ),
    inference(resolution,[status(thm)],[c_14,c_233])).

tff(c_240,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_210,c_4,c_236])).

%------------------------------------------------------------------------------

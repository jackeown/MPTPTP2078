%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0316+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:36:05 EST 2020

% Result     : Theorem 2.00s
% Output     : CNFRefutation 2.00s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 138 expanded)
%              Number of leaves         :   20 (  53 expanded)
%              Depth                    :    8
%              Number of atoms          :   75 ( 258 expanded)
%              Number of equality atoms :   17 (  93 expanded)
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(f_44,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(k1_tarski(C),D))
      <=> ( A = C
          & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t128_zfmisc_1)).

tff(f_37,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,D))
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).

tff(c_4,plain,(
    ! [C_5] : r2_hidden(C_5,k1_tarski(C_5)) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_24,plain,
    ( '#skF_5' = '#skF_3'
    | ~ r2_hidden('#skF_8','#skF_10')
    | '#skF_7' != '#skF_9' ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_38,plain,(
    '#skF_7' != '#skF_9' ),
    inference(splitLeft,[status(thm)],[c_24])).

tff(c_30,plain,
    ( '#skF_5' = '#skF_3'
    | r2_hidden(k4_tarski('#skF_7','#skF_8'),k2_zfmisc_1(k1_tarski('#skF_9'),'#skF_10')) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_41,plain,(
    r2_hidden(k4_tarski('#skF_7','#skF_8'),k2_zfmisc_1(k1_tarski('#skF_9'),'#skF_10')) ),
    inference(splitLeft,[status(thm)],[c_30])).

tff(c_18,plain,(
    ! [A_6,C_8,B_7,D_9] :
      ( r2_hidden(A_6,C_8)
      | ~ r2_hidden(k4_tarski(A_6,B_7),k2_zfmisc_1(C_8,D_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_48,plain,(
    r2_hidden('#skF_7',k1_tarski('#skF_9')) ),
    inference(resolution,[status(thm)],[c_41,c_18])).

tff(c_2,plain,(
    ! [C_5,A_1] :
      ( C_5 = A_1
      | ~ r2_hidden(C_5,k1_tarski(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_53,plain,(
    '#skF_7' = '#skF_9' ),
    inference(resolution,[status(thm)],[c_48,c_2])).

tff(c_57,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_53])).

tff(c_59,plain,(
    ~ r2_hidden(k4_tarski('#skF_7','#skF_8'),k2_zfmisc_1(k1_tarski('#skF_9'),'#skF_10')) ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_28,plain,
    ( r2_hidden('#skF_4','#skF_6')
    | r2_hidden(k4_tarski('#skF_7','#skF_8'),k2_zfmisc_1(k1_tarski('#skF_9'),'#skF_10')) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_65,plain,(
    r2_hidden('#skF_4','#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_59,c_28])).

tff(c_14,plain,(
    ! [A_6,B_7,C_8,D_9] :
      ( r2_hidden(k4_tarski(A_6,B_7),k2_zfmisc_1(C_8,D_9))
      | ~ r2_hidden(B_7,D_9)
      | ~ r2_hidden(A_6,C_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_58,plain,(
    '#skF_5' = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_26,plain,
    ( ~ r2_hidden(k4_tarski('#skF_3','#skF_4'),k2_zfmisc_1(k1_tarski('#skF_5'),'#skF_6'))
    | r2_hidden(k4_tarski('#skF_7','#skF_8'),k2_zfmisc_1(k1_tarski('#skF_9'),'#skF_10')) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_117,plain,
    ( ~ r2_hidden(k4_tarski('#skF_3','#skF_4'),k2_zfmisc_1(k1_tarski('#skF_3'),'#skF_6'))
    | r2_hidden(k4_tarski('#skF_7','#skF_8'),k2_zfmisc_1(k1_tarski('#skF_9'),'#skF_10')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_26])).

tff(c_118,plain,(
    ~ r2_hidden(k4_tarski('#skF_3','#skF_4'),k2_zfmisc_1(k1_tarski('#skF_3'),'#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_59,c_117])).

tff(c_121,plain,
    ( ~ r2_hidden('#skF_4','#skF_6')
    | ~ r2_hidden('#skF_3',k1_tarski('#skF_3')) ),
    inference(resolution,[status(thm)],[c_14,c_118])).

tff(c_125,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_65,c_121])).

tff(c_127,plain,(
    '#skF_7' = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_24])).

tff(c_126,plain,
    ( ~ r2_hidden('#skF_8','#skF_10')
    | '#skF_5' = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_24])).

tff(c_132,plain,(
    ~ r2_hidden('#skF_8','#skF_10') ),
    inference(splitLeft,[status(thm)],[c_126])).

tff(c_135,plain,
    ( '#skF_5' = '#skF_3'
    | r2_hidden(k4_tarski('#skF_9','#skF_8'),k2_zfmisc_1(k1_tarski('#skF_9'),'#skF_10')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_127,c_30])).

tff(c_136,plain,(
    r2_hidden(k4_tarski('#skF_9','#skF_8'),k2_zfmisc_1(k1_tarski('#skF_9'),'#skF_10')) ),
    inference(splitLeft,[status(thm)],[c_135])).

tff(c_143,plain,(
    ! [B_39,D_40,A_41,C_42] :
      ( r2_hidden(B_39,D_40)
      | ~ r2_hidden(k4_tarski(A_41,B_39),k2_zfmisc_1(C_42,D_40)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_146,plain,(
    r2_hidden('#skF_8','#skF_10') ),
    inference(resolution,[status(thm)],[c_136,c_143])).

tff(c_150,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_132,c_146])).

tff(c_152,plain,(
    ~ r2_hidden(k4_tarski('#skF_9','#skF_8'),k2_zfmisc_1(k1_tarski('#skF_9'),'#skF_10')) ),
    inference(splitRight,[status(thm)],[c_135])).

tff(c_160,plain,
    ( r2_hidden('#skF_4','#skF_6')
    | r2_hidden(k4_tarski('#skF_9','#skF_8'),k2_zfmisc_1(k1_tarski('#skF_9'),'#skF_10')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_127,c_28])).

tff(c_161,plain,(
    r2_hidden('#skF_4','#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_152,c_160])).

tff(c_151,plain,(
    '#skF_5' = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_135])).

tff(c_215,plain,
    ( ~ r2_hidden(k4_tarski('#skF_3','#skF_4'),k2_zfmisc_1(k1_tarski('#skF_3'),'#skF_6'))
    | r2_hidden(k4_tarski('#skF_9','#skF_8'),k2_zfmisc_1(k1_tarski('#skF_9'),'#skF_10')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_127,c_151,c_26])).

tff(c_216,plain,(
    ~ r2_hidden(k4_tarski('#skF_3','#skF_4'),k2_zfmisc_1(k1_tarski('#skF_3'),'#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_152,c_215])).

tff(c_219,plain,
    ( ~ r2_hidden('#skF_4','#skF_6')
    | ~ r2_hidden('#skF_3',k1_tarski('#skF_3')) ),
    inference(resolution,[status(thm)],[c_14,c_216])).

tff(c_223,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_161,c_219])).

tff(c_225,plain,(
    r2_hidden('#skF_8','#skF_10') ),
    inference(splitRight,[status(thm)],[c_126])).

tff(c_22,plain,
    ( r2_hidden('#skF_4','#skF_6')
    | ~ r2_hidden('#skF_8','#skF_10')
    | '#skF_7' != '#skF_9' ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_231,plain,(
    r2_hidden('#skF_4','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_127,c_225,c_22])).

tff(c_224,plain,(
    '#skF_5' = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_126])).

tff(c_20,plain,
    ( ~ r2_hidden(k4_tarski('#skF_3','#skF_4'),k2_zfmisc_1(k1_tarski('#skF_5'),'#skF_6'))
    | ~ r2_hidden('#skF_8','#skF_10')
    | '#skF_7' != '#skF_9' ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_254,plain,(
    ~ r2_hidden(k4_tarski('#skF_3','#skF_4'),k2_zfmisc_1(k1_tarski('#skF_3'),'#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_127,c_225,c_224,c_20])).

tff(c_257,plain,
    ( ~ r2_hidden('#skF_4','#skF_6')
    | ~ r2_hidden('#skF_3',k1_tarski('#skF_3')) ),
    inference(resolution,[status(thm)],[c_14,c_254])).

tff(c_261,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_231,c_257])).

%------------------------------------------------------------------------------

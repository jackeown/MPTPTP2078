%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0298+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:36:04 EST 2020

% Result     : Theorem 1.60s
% Output     : CNFRefutation 1.60s
% Verified   : 
% Statistics : Number of formulae       :   60 ( 110 expanded)
%              Number of leaves         :   16 (  42 expanded)
%              Depth                    :    6
%              Number of atoms          :   70 ( 201 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k4_tarski > k2_zfmisc_1 > #nlpp > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_8 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

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

tff(f_37,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,D))
      <=> ( r2_hidden(A,C)
          & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_zfmisc_1)).

tff(f_30,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,D))
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).

tff(c_12,plain,
    ( r2_hidden('#skF_1','#skF_3')
    | ~ r2_hidden('#skF_6','#skF_8')
    | ~ r2_hidden('#skF_5','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_19,plain,(
    ~ r2_hidden('#skF_5','#skF_7') ),
    inference(splitLeft,[status(thm)],[c_12])).

tff(c_16,plain,
    ( r2_hidden('#skF_2','#skF_4')
    | r2_hidden(k4_tarski('#skF_5','#skF_6'),k2_zfmisc_1('#skF_7','#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_21,plain,(
    r2_hidden(k4_tarski('#skF_5','#skF_6'),k2_zfmisc_1('#skF_7','#skF_8')) ),
    inference(splitLeft,[status(thm)],[c_16])).

tff(c_26,plain,(
    ! [A_9,C_10,B_11,D_12] :
      ( r2_hidden(A_9,C_10)
      | ~ r2_hidden(k4_tarski(A_9,B_11),k2_zfmisc_1(C_10,D_12)) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_29,plain,(
    r2_hidden('#skF_5','#skF_7') ),
    inference(resolution,[status(thm)],[c_21,c_26])).

tff(c_33,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_19,c_29])).

tff(c_35,plain,(
    ~ r2_hidden(k4_tarski('#skF_5','#skF_6'),k2_zfmisc_1('#skF_7','#skF_8')) ),
    inference(splitRight,[status(thm)],[c_16])).

tff(c_18,plain,
    ( r2_hidden('#skF_1','#skF_3')
    | r2_hidden(k4_tarski('#skF_5','#skF_6'),k2_zfmisc_1('#skF_7','#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_36,plain,(
    r2_hidden(k4_tarski('#skF_5','#skF_6'),k2_zfmisc_1('#skF_7','#skF_8')) ),
    inference(splitLeft,[status(thm)],[c_18])).

tff(c_37,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_35,c_36])).

tff(c_38,plain,(
    r2_hidden('#skF_1','#skF_3') ),
    inference(splitRight,[status(thm)],[c_18])).

tff(c_34,plain,(
    r2_hidden('#skF_2','#skF_4') ),
    inference(splitRight,[status(thm)],[c_16])).

tff(c_2,plain,(
    ! [A_1,B_2,C_3,D_4] :
      ( r2_hidden(k4_tarski(A_1,B_2),k2_zfmisc_1(C_3,D_4))
      | ~ r2_hidden(B_2,D_4)
      | ~ r2_hidden(A_1,C_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_39,plain,(
    ~ r2_hidden(k4_tarski('#skF_5','#skF_6'),k2_zfmisc_1('#skF_7','#skF_8')) ),
    inference(splitRight,[status(thm)],[c_18])).

tff(c_14,plain,
    ( ~ r2_hidden(k4_tarski('#skF_1','#skF_2'),k2_zfmisc_1('#skF_3','#skF_4'))
    | r2_hidden(k4_tarski('#skF_5','#skF_6'),k2_zfmisc_1('#skF_7','#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_54,plain,(
    ~ r2_hidden(k4_tarski('#skF_1','#skF_2'),k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_39,c_14])).

tff(c_57,plain,
    ( ~ r2_hidden('#skF_2','#skF_4')
    | ~ r2_hidden('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_2,c_54])).

tff(c_61,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_34,c_57])).

tff(c_63,plain,(
    r2_hidden('#skF_5','#skF_7') ),
    inference(splitRight,[status(thm)],[c_12])).

tff(c_10,plain,
    ( r2_hidden('#skF_2','#skF_4')
    | ~ r2_hidden('#skF_6','#skF_8')
    | ~ r2_hidden('#skF_5','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_64,plain,(
    ~ r2_hidden('#skF_5','#skF_7') ),
    inference(splitLeft,[status(thm)],[c_10])).

tff(c_66,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_64])).

tff(c_67,plain,
    ( ~ r2_hidden('#skF_6','#skF_8')
    | r2_hidden('#skF_2','#skF_4') ),
    inference(splitRight,[status(thm)],[c_10])).

tff(c_70,plain,(
    ~ r2_hidden('#skF_6','#skF_8') ),
    inference(splitLeft,[status(thm)],[c_67])).

tff(c_71,plain,(
    r2_hidden(k4_tarski('#skF_5','#skF_6'),k2_zfmisc_1('#skF_7','#skF_8')) ),
    inference(splitLeft,[status(thm)],[c_16])).

tff(c_79,plain,(
    ! [B_25,D_26,A_27,C_28] :
      ( r2_hidden(B_25,D_26)
      | ~ r2_hidden(k4_tarski(A_27,B_25),k2_zfmisc_1(C_28,D_26)) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_82,plain,(
    r2_hidden('#skF_6','#skF_8') ),
    inference(resolution,[status(thm)],[c_71,c_79])).

tff(c_86,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_82])).

tff(c_88,plain,(
    ~ r2_hidden(k4_tarski('#skF_5','#skF_6'),k2_zfmisc_1('#skF_7','#skF_8')) ),
    inference(splitRight,[status(thm)],[c_16])).

tff(c_90,plain,(
    r2_hidden('#skF_1','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_18])).

tff(c_87,plain,(
    r2_hidden('#skF_2','#skF_4') ),
    inference(splitRight,[status(thm)],[c_16])).

tff(c_109,plain,(
    ~ r2_hidden(k4_tarski('#skF_1','#skF_2'),k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_14])).

tff(c_112,plain,
    ( ~ r2_hidden('#skF_2','#skF_4')
    | ~ r2_hidden('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_2,c_109])).

tff(c_116,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_87,c_112])).

tff(c_118,plain,(
    r2_hidden('#skF_6','#skF_8') ),
    inference(splitRight,[status(thm)],[c_67])).

tff(c_62,plain,
    ( ~ r2_hidden('#skF_6','#skF_8')
    | r2_hidden('#skF_1','#skF_3') ),
    inference(splitRight,[status(thm)],[c_12])).

tff(c_120,plain,(
    r2_hidden('#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_118,c_62])).

tff(c_117,plain,(
    r2_hidden('#skF_2','#skF_4') ),
    inference(splitRight,[status(thm)],[c_67])).

tff(c_127,plain,(
    ! [A_49,B_50,C_51,D_52] :
      ( r2_hidden(k4_tarski(A_49,B_50),k2_zfmisc_1(C_51,D_52))
      | ~ r2_hidden(B_50,D_52)
      | ~ r2_hidden(A_49,C_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_8,plain,
    ( ~ r2_hidden(k4_tarski('#skF_1','#skF_2'),k2_zfmisc_1('#skF_3','#skF_4'))
    | ~ r2_hidden('#skF_6','#skF_8')
    | ~ r2_hidden('#skF_5','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_126,plain,(
    ~ r2_hidden(k4_tarski('#skF_1','#skF_2'),k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_118,c_8])).

tff(c_130,plain,
    ( ~ r2_hidden('#skF_2','#skF_4')
    | ~ r2_hidden('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_127,c_126])).

tff(c_140,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_120,c_117,c_130])).

%------------------------------------------------------------------------------

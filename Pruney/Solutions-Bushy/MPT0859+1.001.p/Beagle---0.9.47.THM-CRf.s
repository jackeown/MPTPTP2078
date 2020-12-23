%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0859+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:36:58 EST 2020

% Result     : Theorem 1.64s
% Output     : CNFRefutation 1.64s
% Verified   : 
% Statistics : Number of formulae       :   32 (  41 expanded)
%              Number of leaves         :   17 (  23 expanded)
%              Depth                    :    4
%              Number of atoms          :   33 (  61 expanded)
%              Number of equality atoms :   13 (  25 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k2_zfmisc_1 > k2_tarski > #nlpp > k2_mcart_1 > k1_mcart_1 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_mcart_1,type,(
    k2_mcart_1: $i > $i )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_mcart_1,type,(
    k1_mcart_1: $i > $i )).

tff(f_48,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( r2_hidden(A,k2_zfmisc_1(k2_tarski(B,C),D))
       => ( ( k1_mcart_1(A) = B
            | k1_mcart_1(A) = C )
          & r2_hidden(k2_mcart_1(A),D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_mcart_1)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k2_zfmisc_1(B,C))
     => ( r2_hidden(k1_mcart_1(A),B)
        & r2_hidden(k2_mcart_1(A),C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_mcart_1)).

tff(f_33,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

tff(c_26,plain,
    ( k1_mcart_1('#skF_3') != '#skF_5'
    | ~ r2_hidden(k2_mcart_1('#skF_3'),'#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_31,plain,(
    ~ r2_hidden(k2_mcart_1('#skF_3'),'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_26])).

tff(c_24,plain,(
    r2_hidden('#skF_3',k2_zfmisc_1(k2_tarski('#skF_4','#skF_5'),'#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_43,plain,(
    ! [A_17,C_18,B_19] :
      ( r2_hidden(k2_mcart_1(A_17),C_18)
      | ~ r2_hidden(A_17,k2_zfmisc_1(B_19,C_18)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_45,plain,(
    r2_hidden(k2_mcart_1('#skF_3'),'#skF_6') ),
    inference(resolution,[status(thm)],[c_24,c_43])).

tff(c_49,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_31,c_45])).

tff(c_51,plain,(
    r2_hidden(k2_mcart_1('#skF_3'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_26])).

tff(c_28,plain,
    ( k1_mcart_1('#skF_3') != '#skF_4'
    | ~ r2_hidden(k2_mcart_1('#skF_3'),'#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_53,plain,(
    k1_mcart_1('#skF_3') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_51,c_28])).

tff(c_50,plain,(
    k1_mcart_1('#skF_3') != '#skF_5' ),
    inference(splitRight,[status(thm)],[c_26])).

tff(c_59,plain,(
    ! [A_23,B_24,C_25] :
      ( r2_hidden(k1_mcart_1(A_23),B_24)
      | ~ r2_hidden(A_23,k2_zfmisc_1(B_24,C_25)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_62,plain,(
    r2_hidden(k1_mcart_1('#skF_3'),k2_tarski('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_24,c_59])).

tff(c_63,plain,(
    ! [D_26,B_27,A_28] :
      ( D_26 = B_27
      | D_26 = A_28
      | ~ r2_hidden(D_26,k2_tarski(A_28,B_27)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_66,plain,
    ( k1_mcart_1('#skF_3') = '#skF_5'
    | k1_mcart_1('#skF_3') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_62,c_63])).

tff(c_76,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_53,c_50,c_66])).

%------------------------------------------------------------------------------

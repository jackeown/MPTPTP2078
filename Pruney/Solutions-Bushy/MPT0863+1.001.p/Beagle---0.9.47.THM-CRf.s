%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0863+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:36:58 EST 2020

% Result     : Theorem 1.87s
% Output     : CNFRefutation 1.87s
% Verified   : 
% Statistics : Number of formulae       :   45 (  66 expanded)
%              Number of leaves         :   18 (  32 expanded)
%              Depth                    :    4
%              Number of atoms          :   53 ( 130 expanded)
%              Number of equality atoms :   33 (  89 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k2_zfmisc_1 > k2_tarski > #nlpp > k2_mcart_1 > k1_mcart_1 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_7',type,(
    '#skF_7': $i )).

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

tff(f_50,negated_conjecture,(
    ~ ! [A,B,C,D,E] :
        ( r2_hidden(A,k2_zfmisc_1(k2_tarski(B,C),k2_tarski(D,E)))
       => ( ( k1_mcart_1(A) = B
            | k1_mcart_1(A) = C )
          & ( k2_mcart_1(A) = D
            | k2_mcart_1(A) = E ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_mcart_1)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k2_zfmisc_1(B,C))
     => ( r2_hidden(k1_mcart_1(A),B)
        & r2_hidden(k2_mcart_1(A),C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_mcart_1)).

tff(f_33,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

tff(c_30,plain,
    ( k1_mcart_1('#skF_3') != '#skF_5'
    | k2_mcart_1('#skF_3') != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_35,plain,(
    k2_mcart_1('#skF_3') != '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_30])).

tff(c_28,plain,
    ( k1_mcart_1('#skF_3') != '#skF_4'
    | k2_mcart_1('#skF_3') != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_36,plain,(
    k2_mcart_1('#skF_3') != '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_28])).

tff(c_24,plain,(
    r2_hidden('#skF_3',k2_zfmisc_1(k2_tarski('#skF_4','#skF_5'),k2_tarski('#skF_6','#skF_7'))) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_20,plain,(
    ! [A_7,C_9,B_8] :
      ( r2_hidden(k2_mcart_1(A_7),C_9)
      | ~ r2_hidden(A_7,k2_zfmisc_1(B_8,C_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_40,plain,(
    r2_hidden(k2_mcart_1('#skF_3'),k2_tarski('#skF_6','#skF_7')) ),
    inference(resolution,[status(thm)],[c_24,c_20])).

tff(c_45,plain,(
    ! [D_20,B_21,A_22] :
      ( D_20 = B_21
      | D_20 = A_22
      | ~ r2_hidden(D_20,k2_tarski(A_22,B_21)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_51,plain,
    ( k2_mcart_1('#skF_3') = '#skF_7'
    | k2_mcart_1('#skF_3') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_40,c_45])).

tff(c_62,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_35,c_36,c_51])).

tff(c_63,plain,(
    k1_mcart_1('#skF_3') != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_28])).

tff(c_64,plain,(
    k2_mcart_1('#skF_3') = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_28])).

tff(c_26,plain,
    ( k1_mcart_1('#skF_3') != '#skF_5'
    | k2_mcart_1('#skF_3') != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_71,plain,(
    k1_mcart_1('#skF_3') != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_26])).

tff(c_89,plain,(
    ! [A_29,B_30,C_31] :
      ( r2_hidden(k1_mcart_1(A_29),B_30)
      | ~ r2_hidden(A_29,k2_zfmisc_1(B_30,C_31)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_92,plain,(
    r2_hidden(k1_mcart_1('#skF_3'),k2_tarski('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_24,c_89])).

tff(c_2,plain,(
    ! [D_6,B_2,A_1] :
      ( D_6 = B_2
      | D_6 = A_1
      | ~ r2_hidden(D_6,k2_tarski(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_95,plain,
    ( k1_mcart_1('#skF_3') = '#skF_5'
    | k1_mcart_1('#skF_3') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_92,c_2])).

tff(c_99,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_63,c_71,c_95])).

tff(c_101,plain,(
    k2_mcart_1('#skF_3') = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_32,plain,
    ( k1_mcart_1('#skF_3') != '#skF_4'
    | k2_mcart_1('#skF_3') != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_108,plain,(
    k1_mcart_1('#skF_3') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_101,c_32])).

tff(c_100,plain,(
    k1_mcart_1('#skF_3') != '#skF_5' ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_126,plain,(
    ! [A_38,B_39,C_40] :
      ( r2_hidden(k1_mcart_1(A_38),B_39)
      | ~ r2_hidden(A_38,k2_zfmisc_1(B_39,C_40)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_129,plain,(
    r2_hidden(k1_mcart_1('#skF_3'),k2_tarski('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_24,c_126])).

tff(c_132,plain,
    ( k1_mcart_1('#skF_3') = '#skF_5'
    | k1_mcart_1('#skF_3') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_129,c_2])).

tff(c_136,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_108,c_100,c_132])).

%------------------------------------------------------------------------------

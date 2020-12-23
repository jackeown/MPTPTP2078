%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0855+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:36:57 EST 2020

% Result     : Theorem 1.85s
% Output     : CNFRefutation 1.85s
% Verified   : 
% Statistics : Number of formulae       :   34 (  41 expanded)
%              Number of leaves         :   22 (  27 expanded)
%              Depth                    :    7
%              Number of atoms          :   28 (  50 expanded)
%              Number of equality atoms :    9 (  16 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k4_tarski > k2_zfmisc_1 > #nlpp > k2_mcart_1 > k1_mcart_1 > #skF_1 > #skF_11 > #skF_4 > #skF_7 > #skF_10 > #skF_2 > #skF_6 > #skF_9 > #skF_8 > #skF_5 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_11',type,(
    '#skF_11': $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_mcart_1,type,(
    k2_mcart_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i * $i ) > $i )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_mcart_1,type,(
    k1_mcart_1: $i > $i )).

tff(f_52,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( r2_hidden(k1_mcart_1(A),B)
          & r2_hidden(k2_mcart_1(A),C) )
       => ( ! [D,E] : A != k4_tarski(D,E)
          | r2_hidden(A,k2_zfmisc_1(B,C)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_mcart_1)).

tff(f_41,axiom,(
    ! [A] :
      ( ? [B,C] : A = k4_tarski(B,C)
     => k4_tarski(k1_mcart_1(A),k2_mcart_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_mcart_1)).

tff(f_36,axiom,(
    ! [A,B,C] :
      ( C = k2_zfmisc_1(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ? [E,F] :
              ( r2_hidden(E,A)
              & r2_hidden(F,B)
              & D = k4_tarski(E,F) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_zfmisc_1)).

tff(c_28,plain,(
    ~ r2_hidden('#skF_7',k2_zfmisc_1('#skF_8','#skF_9')) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_34,plain,(
    r2_hidden(k1_mcart_1('#skF_7'),'#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_32,plain,(
    r2_hidden(k2_mcart_1('#skF_7'),'#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_30,plain,(
    k4_tarski('#skF_10','#skF_11') = '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_39,plain,(
    ! [B_42,C_43] : k4_tarski(k1_mcart_1(k4_tarski(B_42,C_43)),k2_mcart_1(k4_tarski(B_42,C_43))) = k4_tarski(B_42,C_43) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_60,plain,(
    k4_tarski(k1_mcart_1('#skF_7'),k2_mcart_1(k4_tarski('#skF_10','#skF_11'))) = k4_tarski('#skF_10','#skF_11') ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_39])).

tff(c_70,plain,(
    k4_tarski(k1_mcart_1('#skF_7'),k2_mcart_1('#skF_7')) = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_30,c_60])).

tff(c_2,plain,(
    ! [E_33,F_34,A_1,B_2] :
      ( r2_hidden(k4_tarski(E_33,F_34),k2_zfmisc_1(A_1,B_2))
      | ~ r2_hidden(F_34,B_2)
      | ~ r2_hidden(E_33,A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_101,plain,(
    ! [A_50,B_51] :
      ( r2_hidden('#skF_7',k2_zfmisc_1(A_50,B_51))
      | ~ r2_hidden(k2_mcart_1('#skF_7'),B_51)
      | ~ r2_hidden(k1_mcart_1('#skF_7'),A_50) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_70,c_2])).

tff(c_105,plain,(
    ! [A_52] :
      ( r2_hidden('#skF_7',k2_zfmisc_1(A_52,'#skF_9'))
      | ~ r2_hidden(k1_mcart_1('#skF_7'),A_52) ) ),
    inference(resolution,[status(thm)],[c_32,c_101])).

tff(c_108,plain,(
    r2_hidden('#skF_7',k2_zfmisc_1('#skF_8','#skF_9')) ),
    inference(resolution,[status(thm)],[c_34,c_105])).

tff(c_112,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_108])).

%------------------------------------------------------------------------------

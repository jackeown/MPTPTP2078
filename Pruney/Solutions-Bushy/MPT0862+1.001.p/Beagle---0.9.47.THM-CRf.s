%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0862+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:36:58 EST 2020

% Result     : Theorem 1.81s
% Output     : CNFRefutation 1.90s
% Verified   : 
% Statistics : Number of formulae       :   38 (  47 expanded)
%              Number of leaves         :   21 (  27 expanded)
%              Depth                    :    4
%              Number of atoms          :   39 (  67 expanded)
%              Number of equality atoms :   22 (  41 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k2_zfmisc_1 > k2_tarski > #nlpp > k2_mcart_1 > k1_tarski > k1_mcart_1 > #skF_4 > #skF_7 > #skF_5 > #skF_6 > #skF_8 > #skF_3 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_mcart_1,type,(
    k2_mcart_1: $i > $i )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k1_mcart_1,type,(
    k1_mcart_1: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_55,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( r2_hidden(A,k2_zfmisc_1(k1_tarski(B),k2_tarski(C,D)))
       => ( k1_mcart_1(A) = B
          & ( k2_mcart_1(A) = C
            | k2_mcart_1(A) = D ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_mcart_1)).

tff(f_46,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k2_zfmisc_1(B,C))
     => ( r2_hidden(k1_mcart_1(A),B)
        & r2_hidden(k2_mcart_1(A),C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_mcart_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(f_40,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

tff(c_38,plain,
    ( k2_mcart_1('#skF_5') != '#skF_8'
    | k1_mcart_1('#skF_5') != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_44,plain,(
    k1_mcart_1('#skF_5') != '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_38])).

tff(c_36,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1(k1_tarski('#skF_6'),k2_tarski('#skF_7','#skF_8'))) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_77,plain,(
    ! [A_28,B_29,C_30] :
      ( r2_hidden(k1_mcart_1(A_28),B_29)
      | ~ r2_hidden(A_28,k2_zfmisc_1(B_29,C_30)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_80,plain,(
    r2_hidden(k1_mcart_1('#skF_5'),k1_tarski('#skF_6')) ),
    inference(resolution,[status(thm)],[c_36,c_77])).

tff(c_2,plain,(
    ! [C_5,A_1] :
      ( C_5 = A_1
      | ~ r2_hidden(C_5,k1_tarski(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_83,plain,(
    k1_mcart_1('#skF_5') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_80,c_2])).

tff(c_87,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_83])).

tff(c_89,plain,(
    k1_mcart_1('#skF_5') = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_40,plain,
    ( k2_mcart_1('#skF_5') != '#skF_7'
    | k1_mcart_1('#skF_5') != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_95,plain,(
    k2_mcart_1('#skF_5') != '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_89,c_40])).

tff(c_88,plain,(
    k2_mcart_1('#skF_5') != '#skF_8' ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_118,plain,(
    ! [A_39,C_40,B_41] :
      ( r2_hidden(k2_mcart_1(A_39),C_40)
      | ~ r2_hidden(A_39,k2_zfmisc_1(B_41,C_40)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_121,plain,(
    r2_hidden(k2_mcart_1('#skF_5'),k2_tarski('#skF_7','#skF_8')) ),
    inference(resolution,[status(thm)],[c_36,c_118])).

tff(c_14,plain,(
    ! [D_11,B_7,A_6] :
      ( D_11 = B_7
      | D_11 = A_6
      | ~ r2_hidden(D_11,k2_tarski(A_6,B_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_124,plain,
    ( k2_mcart_1('#skF_5') = '#skF_8'
    | k2_mcart_1('#skF_5') = '#skF_7' ),
    inference(resolution,[status(thm)],[c_121,c_14])).

tff(c_128,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_95,c_88,c_124])).

%------------------------------------------------------------------------------

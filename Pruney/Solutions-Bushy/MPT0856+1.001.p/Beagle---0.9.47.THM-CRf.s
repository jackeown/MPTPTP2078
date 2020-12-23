%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0856+1.001 : TPTP v7.4.0. Released v7.4.0.
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

% Result     : Theorem 1.70s
% Output     : CNFRefutation 1.79s
% Verified   : 
% Statistics : Number of formulae       :   28 (  34 expanded)
%              Number of leaves         :   16 (  20 expanded)
%              Depth                    :    4
%              Number of atoms          :   25 (  40 expanded)
%              Number of equality atoms :    7 (  11 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k2_zfmisc_1 > #nlpp > k2_mcart_1 > k1_tarski > k1_mcart_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k1_mcart_1,type,(
    k1_mcart_1: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_44,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r2_hidden(A,k2_zfmisc_1(k1_tarski(B),C))
       => ( k1_mcart_1(A) = B
          & r2_hidden(k2_mcart_1(A),C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_mcart_1)).

tff(f_37,axiom,(
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

tff(c_18,plain,
    ( ~ r2_hidden(k2_mcart_1('#skF_3'),'#skF_5')
    | k1_mcart_1('#skF_3') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_28,plain,(
    k1_mcart_1('#skF_3') != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_18])).

tff(c_20,plain,(
    r2_hidden('#skF_3',k2_zfmisc_1(k1_tarski('#skF_4'),'#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_29,plain,(
    ! [A_12,B_13,C_14] :
      ( r2_hidden(k1_mcart_1(A_12),B_13)
      | ~ r2_hidden(A_12,k2_zfmisc_1(B_13,C_14)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_32,plain,(
    r2_hidden(k1_mcart_1('#skF_3'),k1_tarski('#skF_4')) ),
    inference(resolution,[status(thm)],[c_20,c_29])).

tff(c_2,plain,(
    ! [C_5,A_1] :
      ( C_5 = A_1
      | ~ r2_hidden(C_5,k1_tarski(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_35,plain,(
    k1_mcart_1('#skF_3') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_32,c_2])).

tff(c_39,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_35])).

tff(c_40,plain,(
    ~ r2_hidden(k2_mcart_1('#skF_3'),'#skF_5') ),
    inference(splitRight,[status(thm)],[c_18])).

tff(c_51,plain,(
    ! [A_18,C_19,B_20] :
      ( r2_hidden(k2_mcart_1(A_18),C_19)
      | ~ r2_hidden(A_18,k2_zfmisc_1(B_20,C_19)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_53,plain,(
    r2_hidden(k2_mcart_1('#skF_3'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_20,c_51])).

tff(c_57,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_53])).

%------------------------------------------------------------------------------

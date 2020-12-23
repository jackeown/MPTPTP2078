%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0880+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:37:00 EST 2020

% Result     : Theorem 2.90s
% Output     : CNFRefutation 3.04s
% Verified   : 
% Statistics : Number of formulae       :   25 (  28 expanded)
%              Number of leaves         :   17 (  19 expanded)
%              Depth                    :    4
%              Number of atoms          :   13 (  17 expanded)
%              Number of equality atoms :   12 (  16 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k3_zfmisc_1 > k3_mcart_1 > k4_tarski > k2_zfmisc_1 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k3_mcart_1,type,(
    k3_mcart_1: ( $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k3_zfmisc_1,type,(
    k3_zfmisc_1: ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(f_26,axiom,(
    ! [A,B,C] : k3_mcart_1(A,B,C) = k4_tarski(k4_tarski(A,B),C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_mcart_1)).

tff(f_28,axiom,(
    ! [A,B,C] : k3_zfmisc_1(A,B,C) = k2_zfmisc_1(k2_zfmisc_1(A,B),C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).

tff(f_32,axiom,(
    ! [A,B,C] :
      ( k2_zfmisc_1(k1_tarski(A),k2_tarski(B,C)) = k2_tarski(k4_tarski(A,B),k4_tarski(A,C))
      & k2_zfmisc_1(k2_tarski(A,B),k1_tarski(C)) = k2_tarski(k4_tarski(A,C),k4_tarski(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_zfmisc_1)).

tff(f_35,negated_conjecture,(
    ~ ! [A,B,C,D] : k3_zfmisc_1(k2_tarski(A,B),k1_tarski(C),k1_tarski(D)) = k2_tarski(k3_mcart_1(A,C,D),k3_mcart_1(B,C,D)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_mcart_1)).

tff(c_2,plain,(
    ! [A_1,B_2,C_3] : k4_tarski(k4_tarski(A_1,B_2),C_3) = k3_mcart_1(A_1,B_2,C_3) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_4,plain,(
    ! [A_4,B_5,C_6] : k2_zfmisc_1(k2_zfmisc_1(A_4,B_5),C_6) = k3_zfmisc_1(A_4,B_5,C_6) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_106,plain,(
    ! [A_27,B_28,C_29] : k2_zfmisc_1(k2_tarski(A_27,B_28),k1_tarski(C_29)) = k2_tarski(k4_tarski(A_27,C_29),k4_tarski(B_28,C_29)) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_8,plain,(
    ! [A_7,B_8,C_9] : k2_zfmisc_1(k2_tarski(A_7,B_8),k1_tarski(C_9)) = k2_tarski(k4_tarski(A_7,C_9),k4_tarski(B_8,C_9)) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_109,plain,(
    ! [A_27,B_28,C_29,C_9] : k2_zfmisc_1(k2_zfmisc_1(k2_tarski(A_27,B_28),k1_tarski(C_29)),k1_tarski(C_9)) = k2_tarski(k4_tarski(k4_tarski(A_27,C_29),C_9),k4_tarski(k4_tarski(B_28,C_29),C_9)) ),
    inference(superposition,[status(thm),theory(equality)],[c_106,c_8])).

tff(c_151,plain,(
    ! [A_27,B_28,C_29,C_9] : k3_zfmisc_1(k2_tarski(A_27,B_28),k1_tarski(C_29),k1_tarski(C_9)) = k2_tarski(k3_mcart_1(A_27,C_29,C_9),k3_mcart_1(B_28,C_29,C_9)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_2,c_4,c_109])).

tff(c_10,plain,(
    k3_zfmisc_1(k2_tarski('#skF_1','#skF_2'),k1_tarski('#skF_3'),k1_tarski('#skF_4')) != k2_tarski(k3_mcart_1('#skF_1','#skF_3','#skF_4'),k3_mcart_1('#skF_2','#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_840,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_151,c_10])).

%------------------------------------------------------------------------------

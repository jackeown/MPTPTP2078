%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0882+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:37:00 EST 2020

% Result     : Theorem 3.08s
% Output     : CNFRefutation 3.39s
% Verified   : 
% Statistics : Number of formulae       :   28 (  30 expanded)
%              Number of leaves         :   18 (  19 expanded)
%              Depth                    :    4
%              Number of atoms          :   16 (  18 expanded)
%              Number of equality atoms :   15 (  17 expanded)
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_mcart_1)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( k2_zfmisc_1(k1_tarski(A),k2_tarski(B,C)) = k2_tarski(k4_tarski(A,B),k4_tarski(A,C))
      & k2_zfmisc_1(k2_tarski(A,B),k1_tarski(C)) = k2_tarski(k4_tarski(A,C),k4_tarski(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_zfmisc_1)).

tff(f_30,axiom,(
    ! [A,B] : k2_zfmisc_1(k1_tarski(A),k1_tarski(B)) = k1_tarski(k4_tarski(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_zfmisc_1)).

tff(f_28,axiom,(
    ! [A,B,C] : k3_zfmisc_1(A,B,C) = k2_zfmisc_1(k2_zfmisc_1(A,B),C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).

tff(f_37,negated_conjecture,(
    ~ ! [A,B,C,D] : k3_zfmisc_1(k1_tarski(A),k1_tarski(B),k2_tarski(C,D)) = k2_tarski(k3_mcart_1(A,B,C),k3_mcart_1(A,B,D)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_mcart_1)).

tff(c_2,plain,(
    ! [A_1,B_2,C_3] : k4_tarski(k4_tarski(A_1,B_2),C_3) = k3_mcart_1(A_1,B_2,C_3) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_134,plain,(
    ! [A_34,B_35,C_36] : k2_zfmisc_1(k1_tarski(A_34),k2_tarski(B_35,C_36)) = k2_tarski(k4_tarski(A_34,B_35),k4_tarski(A_34,C_36)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_178,plain,(
    ! [A_1,B_2,B_35,C_3] : k2_zfmisc_1(k1_tarski(k4_tarski(A_1,B_2)),k2_tarski(B_35,C_3)) = k2_tarski(k4_tarski(k4_tarski(A_1,B_2),B_35),k3_mcart_1(A_1,B_2,C_3)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_134])).

tff(c_185,plain,(
    ! [A_1,B_2,B_35,C_3] : k2_zfmisc_1(k1_tarski(k4_tarski(A_1,B_2)),k2_tarski(B_35,C_3)) = k2_tarski(k3_mcart_1(A_1,B_2,B_35),k3_mcart_1(A_1,B_2,C_3)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_178])).

tff(c_6,plain,(
    ! [A_7,B_8] : k2_zfmisc_1(k1_tarski(A_7),k1_tarski(B_8)) = k1_tarski(k4_tarski(A_7,B_8)) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_22,plain,(
    ! [A_14,B_15,C_16] : k2_zfmisc_1(k2_zfmisc_1(A_14,B_15),C_16) = k3_zfmisc_1(A_14,B_15,C_16) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_37,plain,(
    ! [A_7,B_8,C_16] : k3_zfmisc_1(k1_tarski(A_7),k1_tarski(B_8),C_16) = k2_zfmisc_1(k1_tarski(k4_tarski(A_7,B_8)),C_16) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_22])).

tff(c_12,plain,(
    k3_zfmisc_1(k1_tarski('#skF_1'),k1_tarski('#skF_2'),k2_tarski('#skF_3','#skF_4')) != k2_tarski(k3_mcart_1('#skF_1','#skF_2','#skF_3'),k3_mcart_1('#skF_1','#skF_2','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_133,plain,(
    k2_zfmisc_1(k1_tarski(k4_tarski('#skF_1','#skF_2')),k2_tarski('#skF_3','#skF_4')) != k2_tarski(k3_mcart_1('#skF_1','#skF_2','#skF_3'),k3_mcart_1('#skF_1','#skF_2','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_37,c_12])).

tff(c_1128,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_185,c_133])).

%------------------------------------------------------------------------------

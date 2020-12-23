%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0872+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:36:59 EST 2020

% Result     : Theorem 1.49s
% Output     : CNFRefutation 1.49s
% Verified   : 
% Statistics : Number of formulae       :   20 (  21 expanded)
%              Number of leaves         :   13 (  14 expanded)
%              Depth                    :    4
%              Number of atoms          :   10 (  11 expanded)
%              Number of equality atoms :    9 (  10 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    3 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k4_mcart_1 > k3_mcart_1 > k4_tarski > #nlpp > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k3_mcart_1,type,(
    k3_mcart_1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k4_mcart_1,type,(
    k4_mcart_1: ( $i * $i * $i * $i ) > $i )).

tff(f_28,axiom,(
    ! [A,B,C,D] : k4_mcart_1(A,B,C,D) = k4_tarski(k3_mcart_1(A,B,C),D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_mcart_1)).

tff(f_26,axiom,(
    ! [A,B,C] : k3_mcart_1(A,B,C) = k4_tarski(k4_tarski(A,B),C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_mcart_1)).

tff(f_31,negated_conjecture,(
    ~ ! [A,B,C,D] : k4_mcart_1(A,B,C,D) = k3_mcart_1(k4_tarski(A,B),C,D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_mcart_1)).

tff(c_4,plain,(
    ! [A_4,B_5,C_6,D_7] : k4_tarski(k3_mcart_1(A_4,B_5,C_6),D_7) = k4_mcart_1(A_4,B_5,C_6,D_7) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_7,plain,(
    ! [A_8,B_9,C_10] : k4_tarski(k4_tarski(A_8,B_9),C_10) = k3_mcart_1(A_8,B_9,C_10) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_2,plain,(
    ! [A_1,B_2,C_3] : k4_tarski(k4_tarski(A_1,B_2),C_3) = k3_mcart_1(A_1,B_2,C_3) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_10,plain,(
    ! [A_8,B_9,C_10,C_3] : k3_mcart_1(k4_tarski(A_8,B_9),C_10,C_3) = k4_tarski(k3_mcart_1(A_8,B_9,C_10),C_3) ),
    inference(superposition,[status(thm),theory(equality)],[c_7,c_2])).

tff(c_34,plain,(
    ! [A_8,B_9,C_10,C_3] : k3_mcart_1(k4_tarski(A_8,B_9),C_10,C_3) = k4_mcart_1(A_8,B_9,C_10,C_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_10])).

tff(c_6,plain,(
    k3_mcart_1(k4_tarski('#skF_1','#skF_2'),'#skF_3','#skF_4') != k4_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_37,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_6])).

%------------------------------------------------------------------------------

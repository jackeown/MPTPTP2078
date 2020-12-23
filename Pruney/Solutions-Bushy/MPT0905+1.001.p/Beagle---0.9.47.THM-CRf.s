%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0905+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:37:03 EST 2020

% Result     : Theorem 1.57s
% Output     : CNFRefutation 1.78s
% Verified   : 
% Statistics : Number of formulae       :   32 (  33 expanded)
%              Number of leaves         :   20 (  21 expanded)
%              Depth                    :    4
%              Number of atoms          :   18 (  19 expanded)
%              Number of equality atoms :   17 (  18 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k4_zfmisc_1 > k4_mcart_1 > k3_zfmisc_1 > k3_mcart_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(k4_zfmisc_1,type,(
    k4_zfmisc_1: ( $i * $i * $i * $i ) > $i )).

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

tff(k4_mcart_1,type,(
    k4_mcart_1: ( $i * $i * $i * $i ) > $i )).

tff(f_28,axiom,(
    ! [A,B,C,D] : k4_mcart_1(A,B,C,D) = k4_tarski(k3_mcart_1(A,B,C),D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_mcart_1)).

tff(f_26,axiom,(
    ! [A,B,C] : k3_mcart_1(A,B,C) = k4_tarski(k4_tarski(A,B),C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_mcart_1)).

tff(f_32,axiom,(
    ! [A,B,C] : k3_zfmisc_1(k1_tarski(A),k1_tarski(B),k1_tarski(C)) = k1_tarski(k3_mcart_1(A,B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_mcart_1)).

tff(f_30,axiom,(
    ! [A,B] : k2_zfmisc_1(k1_tarski(A),k1_tarski(B)) = k1_tarski(k4_tarski(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_zfmisc_1)).

tff(f_34,axiom,(
    ! [A,B,C,D] : k3_zfmisc_1(k2_zfmisc_1(A,B),C,D) = k4_zfmisc_1(A,B,C,D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t54_mcart_1)).

tff(f_37,negated_conjecture,(
    ~ ! [A,B,C,D] : k4_zfmisc_1(k1_tarski(A),k1_tarski(B),k1_tarski(C),k1_tarski(D)) = k1_tarski(k4_mcart_1(A,B,C,D)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_mcart_1)).

tff(c_4,plain,(
    ! [A_4,B_5,C_6,D_7] : k4_tarski(k3_mcart_1(A_4,B_5,C_6),D_7) = k4_mcart_1(A_4,B_5,C_6,D_7) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_2,plain,(
    ! [A_1,B_2,C_3] : k4_tarski(k4_tarski(A_1,B_2),C_3) = k3_mcart_1(A_1,B_2,C_3) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_22,plain,(
    ! [A_19,B_20,C_21] : k4_tarski(k4_tarski(A_19,B_20),C_21) = k3_mcart_1(A_19,B_20,C_21) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_31,plain,(
    ! [A_1,B_2,C_3,C_21] : k3_mcart_1(k4_tarski(A_1,B_2),C_3,C_21) = k4_tarski(k3_mcart_1(A_1,B_2,C_3),C_21) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_22])).

tff(c_70,plain,(
    ! [A_1,B_2,C_3,C_21] : k3_mcart_1(k4_tarski(A_1,B_2),C_3,C_21) = k4_mcart_1(A_1,B_2,C_3,C_21) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_31])).

tff(c_8,plain,(
    ! [A_10,B_11,C_12] : k3_zfmisc_1(k1_tarski(A_10),k1_tarski(B_11),k1_tarski(C_12)) = k1_tarski(k3_mcart_1(A_10,B_11,C_12)) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_6,plain,(
    ! [A_8,B_9] : k2_zfmisc_1(k1_tarski(A_8),k1_tarski(B_9)) = k1_tarski(k4_tarski(A_8,B_9)) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_49,plain,(
    ! [A_26,B_27,C_28,D_29] : k3_zfmisc_1(k2_zfmisc_1(A_26,B_27),C_28,D_29) = k4_zfmisc_1(A_26,B_27,C_28,D_29) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_58,plain,(
    ! [A_8,B_9,C_28,D_29] : k4_zfmisc_1(k1_tarski(A_8),k1_tarski(B_9),C_28,D_29) = k3_zfmisc_1(k1_tarski(k4_tarski(A_8,B_9)),C_28,D_29) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_49])).

tff(c_12,plain,(
    k4_zfmisc_1(k1_tarski('#skF_1'),k1_tarski('#skF_2'),k1_tarski('#skF_3'),k1_tarski('#skF_4')) != k1_tarski(k4_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_114,plain,(
    k3_zfmisc_1(k1_tarski(k4_tarski('#skF_1','#skF_2')),k1_tarski('#skF_3'),k1_tarski('#skF_4')) != k1_tarski(k4_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_12])).

tff(c_117,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_8,c_114])).

%------------------------------------------------------------------------------

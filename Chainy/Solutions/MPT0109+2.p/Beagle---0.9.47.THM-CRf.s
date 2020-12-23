%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0109+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:07:15 EST 2020

% Result     : Theorem 3.83s
% Output     : CNFRefutation 3.83s
% Verified   : 
% Statistics : Number of formulae       :   50 (  52 expanded)
%              Number of leaves         :   42 (  43 expanded)
%              Depth                    :    3
%              Number of atoms          :   13 (  15 expanded)
%              Number of equality atoms :   12 (  14 expanded)
%              Maximal formula depth    :    5 (   4 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_xboole_0 > r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > o_0_0_xboole_0 > k1_xboole_0 > #skF_13 > #skF_11 > #skF_20 > #skF_18 > #skF_6 > #skF_1 > #skF_17 > #skF_22 > #skF_19 > #skF_4 > #skF_10 > #skF_12 > #skF_23 > #skF_5 > #skF_21 > #skF_9 > #skF_7 > #skF_14 > #skF_3 > #skF_2 > #skF_8 > #skF_16 > #skF_15

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_13',type,(
    '#skF_13': ( $i * ( $i * $i ) ) > $i )).

tff('#skF_11',type,(
    '#skF_11': ( $i * $i ) > $i )).

tff(o_0_0_xboole_0,type,(
    o_0_0_xboole_0: $i )).

tff('#skF_20',type,(
    '#skF_20': $i )).

tff('#skF_18',type,(
    '#skF_18': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': ( $i * ( $i * $i ) ) > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff('#skF_17',type,(
    '#skF_17': ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_22',type,(
    '#skF_22': ( $i * ( $i * $i ) ) > $i )).

tff('#skF_19',type,(
    '#skF_19': $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * ( $i * $i ) ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff('#skF_12',type,(
    '#skF_12': ( $i * $i ) > $i )).

tff('#skF_23',type,(
    '#skF_23': ( $i * ( $i * $i ) ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * ( $i * $i ) ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_21',type,(
    '#skF_21': $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * ( $i * $i ) ) > $i )).

tff(r2_xboole_0,type,(
    r2_xboole_0: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_14',type,(
    '#skF_14': ( $i * ( $i * $i ) ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * ( $i * $i ) ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': ( $i * ( $i * $i ) ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_16',type,(
    '#skF_16': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_15',type,(
    '#skF_15': ( $i * $i ) > $i )).

tff(f_274,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k4_xboole_0(k2_xboole_0(A,B),k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t101_xboole_1)).

tff(f_461,axiom,(
    ! [A,B] : k4_xboole_0(k2_xboole_0(A,B),k3_xboole_0(A,B)) = k2_xboole_0(k4_xboole_0(A,B),k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_xboole_1)).

tff(f_455,axiom,(
    ! [A,B,C] : k4_xboole_0(A,k4_xboole_0(B,C)) = k2_xboole_0(k4_xboole_0(A,B),k3_xboole_0(A,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_xboole_1)).

tff(f_314,axiom,(
    ! [A,B,C] : k3_xboole_0(k3_xboole_0(A,B),C) = k3_xboole_0(A,k3_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_xboole_1)).

tff(f_277,negated_conjecture,(
    ~ ! [A,B,C] : k4_xboole_0(A,k5_xboole_0(B,C)) = k2_xboole_0(k4_xboole_0(A,k2_xboole_0(B,C)),k3_xboole_0(k3_xboole_0(A,B),C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t102_xboole_1)).

tff(c_216,plain,(
    ! [A_101,B_102] : k4_xboole_0(k2_xboole_0(A_101,B_102),k3_xboole_0(A_101,B_102)) = k5_xboole_0(A_101,B_102) ),
    inference(cnfTransformation,[status(thm)],[f_274])).

tff(c_336,plain,(
    ! [A_238,B_239] : k4_xboole_0(k2_xboole_0(A_238,B_239),k3_xboole_0(A_238,B_239)) = k2_xboole_0(k4_xboole_0(A_238,B_239),k4_xboole_0(B_239,A_238)) ),
    inference(cnfTransformation,[status(thm)],[f_461])).

tff(c_460,plain,(
    ! [A_238,B_239] : k2_xboole_0(k4_xboole_0(A_238,B_239),k4_xboole_0(B_239,A_238)) = k5_xboole_0(A_238,B_239) ),
    inference(demodulation,[status(thm),theory(equality)],[c_216,c_336])).

tff(c_330,plain,(
    ! [A_229,B_230,C_231] : k2_xboole_0(k4_xboole_0(A_229,B_230),k3_xboole_0(A_229,C_231)) = k4_xboole_0(A_229,k4_xboole_0(B_230,C_231)) ),
    inference(cnfTransformation,[status(thm)],[f_455])).

tff(c_236,plain,(
    ! [A_121,B_122,C_123] : k3_xboole_0(k3_xboole_0(A_121,B_122),C_123) = k3_xboole_0(A_121,k3_xboole_0(B_122,C_123)) ),
    inference(cnfTransformation,[status(thm)],[f_314])).

tff(c_218,plain,(
    k2_xboole_0(k4_xboole_0('#skF_19',k2_xboole_0('#skF_20','#skF_21')),k3_xboole_0(k3_xboole_0('#skF_19','#skF_20'),'#skF_21')) != k4_xboole_0('#skF_19',k5_xboole_0('#skF_20','#skF_21')) ),
    inference(cnfTransformation,[status(thm)],[f_277])).

tff(c_459,plain,(
    k4_xboole_0('#skF_19',k2_xboole_0(k4_xboole_0('#skF_20','#skF_21'),k4_xboole_0('#skF_21','#skF_20'))) != k4_xboole_0('#skF_19',k5_xboole_0('#skF_20','#skF_21')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_336,c_330,c_236,c_218])).

tff(c_462,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_460,c_459])).
%------------------------------------------------------------------------------

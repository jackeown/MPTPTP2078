%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0106+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:35:44 EST 2020

% Result     : Theorem 4.39s
% Output     : CNFRefutation 4.39s
% Verified   : 
% Statistics : Number of formulae       :   21 (  23 expanded)
%              Number of leaves         :   13 (  14 expanded)
%              Depth                    :    5
%              Number of atoms          :   12 (  14 expanded)
%              Number of equality atoms :   11 (  13 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_26,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k2_xboole_0(k4_xboole_0(A,B),k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_xboole_0)).

tff(f_28,axiom,(
    ! [A,B,C] : k4_xboole_0(k4_xboole_0(A,B),C) = k4_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

tff(f_30,axiom,(
    ! [A,B,C] : k4_xboole_0(k2_xboole_0(A,B),C) = k2_xboole_0(k4_xboole_0(A,C),k4_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_xboole_1)).

tff(f_33,negated_conjecture,(
    ~ ! [A,B,C] : k4_xboole_0(k5_xboole_0(A,B),C) = k2_xboole_0(k4_xboole_0(A,k2_xboole_0(B,C)),k4_xboole_0(B,k2_xboole_0(A,C))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t99_xboole_1)).

tff(c_2,plain,(
    ! [A_1,B_2] : k2_xboole_0(k4_xboole_0(A_1,B_2),k4_xboole_0(B_2,A_1)) = k5_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_4,plain,(
    ! [A_3,B_4,C_5] : k4_xboole_0(k4_xboole_0(A_3,B_4),C_5) = k4_xboole_0(A_3,k2_xboole_0(B_4,C_5)) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_41,plain,(
    ! [A_14,C_15,B_16] : k2_xboole_0(k4_xboole_0(A_14,C_15),k4_xboole_0(B_16,C_15)) = k4_xboole_0(k2_xboole_0(A_14,B_16),C_15) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_518,plain,(
    ! [A_34,B_35,C_36,B_37] : k2_xboole_0(k4_xboole_0(A_34,k2_xboole_0(B_35,C_36)),k4_xboole_0(B_37,C_36)) = k4_xboole_0(k2_xboole_0(k4_xboole_0(A_34,B_35),B_37),C_36) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_41])).

tff(c_610,plain,(
    ! [A_3,A_34,B_35,C_5,B_4] : k2_xboole_0(k4_xboole_0(A_34,k2_xboole_0(B_35,C_5)),k4_xboole_0(A_3,k2_xboole_0(B_4,C_5))) = k4_xboole_0(k2_xboole_0(k4_xboole_0(A_34,B_35),k4_xboole_0(A_3,B_4)),C_5) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_518])).

tff(c_8,plain,(
    k2_xboole_0(k4_xboole_0('#skF_1',k2_xboole_0('#skF_2','#skF_3')),k4_xboole_0('#skF_2',k2_xboole_0('#skF_1','#skF_3'))) != k4_xboole_0(k5_xboole_0('#skF_1','#skF_2'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_2653,plain,(
    k4_xboole_0(k2_xboole_0(k4_xboole_0('#skF_1','#skF_2'),k4_xboole_0('#skF_2','#skF_1')),'#skF_3') != k4_xboole_0(k5_xboole_0('#skF_1','#skF_2'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_610,c_8])).

tff(c_2656,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_2653])).

%------------------------------------------------------------------------------

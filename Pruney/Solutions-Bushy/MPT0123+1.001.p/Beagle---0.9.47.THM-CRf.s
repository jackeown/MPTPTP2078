%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0123+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:35:46 EST 2020

% Result     : Theorem 1.82s
% Output     : CNFRefutation 1.96s
% Verified   : 
% Statistics : Number of formulae       :   22 (  27 expanded)
%              Number of leaves         :   11 (  14 expanded)
%              Depth                    :    5
%              Number of atoms          :   15 (  20 expanded)
%              Number of equality atoms :   14 (  19 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k3_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(f_28,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_30,axiom,(
    ! [A,B,C] : k3_xboole_0(k3_xboole_0(A,B),C) = k3_xboole_0(A,k3_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_xboole_1)).

tff(f_26,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_33,negated_conjecture,(
    ~ ! [A,B,C] : k3_xboole_0(A,k3_xboole_0(B,C)) = k3_xboole_0(k3_xboole_0(A,B),k3_xboole_0(A,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t116_xboole_1)).

tff(c_4,plain,(
    ! [A_3] : k3_xboole_0(A_3,A_3) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_53,plain,(
    ! [A_11,B_12,C_13] : k3_xboole_0(k3_xboole_0(A_11,B_12),C_13) = k3_xboole_0(A_11,k3_xboole_0(B_12,C_13)) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_92,plain,(
    ! [A_3,C_13] : k3_xboole_0(A_3,k3_xboole_0(A_3,C_13)) = k3_xboole_0(A_3,C_13) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_53])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_62,plain,(
    ! [C_13,A_11,B_12] : k3_xboole_0(C_13,k3_xboole_0(A_11,B_12)) = k3_xboole_0(A_11,k3_xboole_0(B_12,C_13)) ),
    inference(superposition,[status(thm),theory(equality)],[c_53,c_2])).

tff(c_6,plain,(
    ! [A_5,B_6,C_7] : k3_xboole_0(k3_xboole_0(A_5,B_6),C_7) = k3_xboole_0(A_5,k3_xboole_0(B_6,C_7)) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_8,plain,(
    k3_xboole_0(k3_xboole_0('#skF_1','#skF_2'),k3_xboole_0('#skF_1','#skF_3')) != k3_xboole_0('#skF_1',k3_xboole_0('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_9,plain,(
    k3_xboole_0('#skF_1',k3_xboole_0('#skF_2',k3_xboole_0('#skF_1','#skF_3'))) != k3_xboole_0('#skF_1',k3_xboole_0('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_8])).

tff(c_10,plain,(
    k3_xboole_0('#skF_1',k3_xboole_0('#skF_2',k3_xboole_0('#skF_1','#skF_3'))) != k3_xboole_0('#skF_1',k3_xboole_0('#skF_3','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_9])).

tff(c_211,plain,(
    k3_xboole_0('#skF_1',k3_xboole_0('#skF_1',k3_xboole_0('#skF_3','#skF_2'))) != k3_xboole_0('#skF_1',k3_xboole_0('#skF_3','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_10])).

tff(c_214,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_211])).

%------------------------------------------------------------------------------

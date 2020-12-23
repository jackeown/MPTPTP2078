%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0139+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:35:47 EST 2020

% Result     : Theorem 1.34s
% Output     : CNFRefutation 1.34s
% Verified   : 
% Statistics : Number of formulae       :   29 (  29 expanded)
%              Number of leaves         :   20 (  20 expanded)
%              Depth                    :    5
%              Number of atoms          :   14 (  14 expanded)
%              Number of equality atoms :   13 (  13 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k4_enumset1 > k3_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_28,axiom,(
    ! [A,B,C,D,E,F] : k4_enumset1(A,B,C,D,E,F) = k2_xboole_0(k1_enumset1(A,B,C),k1_enumset1(D,E,F)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l62_enumset1)).

tff(f_30,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k2_xboole_0(k2_tarski(A,B),k1_tarski(C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_enumset1)).

tff(f_26,axiom,(
    ! [A,B,C,D,E] : k3_enumset1(A,B,C,D,E) = k2_xboole_0(k1_enumset1(A,B,C),k2_tarski(D,E)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l57_enumset1)).

tff(f_32,axiom,(
    ! [A,B,C] : k2_xboole_0(k2_xboole_0(A,B),C) = k2_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).

tff(f_35,negated_conjecture,(
    ~ ! [A,B,C,D,E,F] : k4_enumset1(A,B,C,D,E,F) = k2_xboole_0(k3_enumset1(A,B,C,D,E),k1_tarski(F)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_enumset1)).

tff(c_4,plain,(
    ! [B_7,D_9,C_8,F_11,E_10,A_6] : k2_xboole_0(k1_enumset1(A_6,B_7,C_8),k1_enumset1(D_9,E_10,F_11)) = k4_enumset1(A_6,B_7,C_8,D_9,E_10,F_11) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_6,plain,(
    ! [A_12,B_13,C_14] : k2_xboole_0(k2_tarski(A_12,B_13),k1_tarski(C_14)) = k1_enumset1(A_12,B_13,C_14) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_40,plain,(
    ! [E_24,A_28,C_27,D_25,B_26] : k2_xboole_0(k1_enumset1(A_28,B_26,C_27),k2_tarski(D_25,E_24)) = k3_enumset1(A_28,B_26,C_27,D_25,E_24) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_8,plain,(
    ! [A_15,B_16,C_17] : k2_xboole_0(k2_xboole_0(A_15,B_16),C_17) = k2_xboole_0(A_15,k2_xboole_0(B_16,C_17)) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_77,plain,(
    ! [C_39,D_44,E_43,B_42,A_40,C_41] : k2_xboole_0(k1_enumset1(A_40,B_42,C_41),k2_xboole_0(k2_tarski(D_44,E_43),C_39)) = k2_xboole_0(k3_enumset1(A_40,B_42,C_41,D_44,E_43),C_39) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_8])).

tff(c_92,plain,(
    ! [C_14,B_42,A_12,B_13,A_40,C_41] : k2_xboole_0(k3_enumset1(A_40,B_42,C_41,A_12,B_13),k1_tarski(C_14)) = k2_xboole_0(k1_enumset1(A_40,B_42,C_41),k1_enumset1(A_12,B_13,C_14)) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_77])).

tff(c_96,plain,(
    ! [C_14,B_42,A_12,B_13,A_40,C_41] : k2_xboole_0(k3_enumset1(A_40,B_42,C_41,A_12,B_13),k1_tarski(C_14)) = k4_enumset1(A_40,B_42,C_41,A_12,B_13,C_14) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_92])).

tff(c_10,plain,(
    k2_xboole_0(k3_enumset1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5'),k1_tarski('#skF_6')) != k4_enumset1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_99,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_10])).

%------------------------------------------------------------------------------

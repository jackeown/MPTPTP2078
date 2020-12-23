%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0131+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:35:46 EST 2020

% Result     : Theorem 1.65s
% Output     : CNFRefutation 1.65s
% Verified   : 
% Statistics : Number of formulae       :   28 (  28 expanded)
%              Number of leaves         :   19 (  19 expanded)
%              Depth                    :    5
%              Number of atoms          :   14 (  14 expanded)
%              Number of equality atoms :   13 (  13 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_28,axiom,(
    ! [A,B,C,D,E] : k3_enumset1(A,B,C,D,E) = k2_xboole_0(k1_enumset1(A,B,C),k2_tarski(D,E)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l57_enumset1)).

tff(f_26,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k2_tarski(A,B),k2_tarski(C,D)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l53_enumset1)).

tff(f_30,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k2_xboole_0(k1_tarski(A),k2_tarski(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_enumset1)).

tff(f_32,axiom,(
    ! [A,B,C] : k2_xboole_0(k2_xboole_0(A,B),C) = k2_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).

tff(f_35,negated_conjecture,(
    ~ ! [A,B,C,D,E] : k3_enumset1(A,B,C,D,E) = k2_xboole_0(k1_tarski(A),k2_enumset1(B,C,D,E)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_enumset1)).

tff(c_4,plain,(
    ! [B_6,C_7,E_9,D_8,A_5] : k2_xboole_0(k1_enumset1(A_5,B_6,C_7),k2_tarski(D_8,E_9)) = k3_enumset1(A_5,B_6,C_7,D_8,E_9) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_2,plain,(
    ! [A_1,B_2,C_3,D_4] : k2_xboole_0(k2_tarski(A_1,B_2),k2_tarski(C_3,D_4)) = k2_enumset1(A_1,B_2,C_3,D_4) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_28,plain,(
    ! [A_19,B_20,C_21] : k2_xboole_0(k1_tarski(A_19),k2_tarski(B_20,C_21)) = k1_enumset1(A_19,B_20,C_21) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_8,plain,(
    ! [A_13,B_14,C_15] : k2_xboole_0(k2_xboole_0(A_13,B_14),C_15) = k2_xboole_0(A_13,k2_xboole_0(B_14,C_15)) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_64,plain,(
    ! [A_31,B_32,C_33,C_34] : k2_xboole_0(k1_tarski(A_31),k2_xboole_0(k2_tarski(B_32,C_33),C_34)) = k2_xboole_0(k1_enumset1(A_31,B_32,C_33),C_34) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_8])).

tff(c_76,plain,(
    ! [A_31,B_2,C_3,A_1,D_4] : k2_xboole_0(k1_enumset1(A_31,A_1,B_2),k2_tarski(C_3,D_4)) = k2_xboole_0(k1_tarski(A_31),k2_enumset1(A_1,B_2,C_3,D_4)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_64])).

tff(c_80,plain,(
    ! [A_31,B_2,C_3,A_1,D_4] : k2_xboole_0(k1_tarski(A_31),k2_enumset1(A_1,B_2,C_3,D_4)) = k3_enumset1(A_31,A_1,B_2,C_3,D_4) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_76])).

tff(c_10,plain,(
    k2_xboole_0(k1_tarski('#skF_1'),k2_enumset1('#skF_2','#skF_3','#skF_4','#skF_5')) != k3_enumset1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_83,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_10])).

%------------------------------------------------------------------------------

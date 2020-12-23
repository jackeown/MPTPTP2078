%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0135+1.001 : TPTP v7.4.0. Released v7.4.0.
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

% Result     : Theorem 1.55s
% Output     : CNFRefutation 1.58s
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

tff(f_26,axiom,(
    ! [A,B,C,D,E,F] : k4_enumset1(A,B,C,D,E,F) = k2_xboole_0(k1_enumset1(A,B,C),k1_enumset1(D,E,F)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l62_enumset1)).

tff(f_30,axiom,(
    ! [A,B,C,D,E] : k3_enumset1(A,B,C,D,E) = k2_xboole_0(k2_tarski(A,B),k1_enumset1(C,D,E)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_enumset1)).

tff(f_28,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k2_xboole_0(k1_tarski(A),k2_tarski(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_enumset1)).

tff(f_32,axiom,(
    ! [A,B,C] : k2_xboole_0(k2_xboole_0(A,B),C) = k2_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).

tff(f_35,negated_conjecture,(
    ~ ! [A,B,C,D,E,F] : k4_enumset1(A,B,C,D,E,F) = k2_xboole_0(k1_tarski(A),k3_enumset1(B,C,D,E,F)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_enumset1)).

tff(c_2,plain,(
    ! [B_2,C_3,A_1,E_5,D_4,F_6] : k2_xboole_0(k1_enumset1(A_1,B_2,C_3),k1_enumset1(D_4,E_5,F_6)) = k4_enumset1(A_1,B_2,C_3,D_4,E_5,F_6) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_6,plain,(
    ! [B_11,A_10,C_12,E_14,D_13] : k2_xboole_0(k2_tarski(A_10,B_11),k1_enumset1(C_12,D_13,E_14)) = k3_enumset1(A_10,B_11,C_12,D_13,E_14) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_28,plain,(
    ! [A_21,B_22,C_23] : k2_xboole_0(k1_tarski(A_21),k2_tarski(B_22,C_23)) = k1_enumset1(A_21,B_22,C_23) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_8,plain,(
    ! [A_15,B_16,C_17] : k2_xboole_0(k2_xboole_0(A_15,B_16),C_17) = k2_xboole_0(A_15,k2_xboole_0(B_16,C_17)) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_52,plain,(
    ! [A_29,B_30,C_31,C_32] : k2_xboole_0(k1_tarski(A_29),k2_xboole_0(k2_tarski(B_30,C_31),C_32)) = k2_xboole_0(k1_enumset1(A_29,B_30,C_31),C_32) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_8])).

tff(c_64,plain,(
    ! [B_11,A_10,C_12,A_29,E_14,D_13] : k2_xboole_0(k1_enumset1(A_29,A_10,B_11),k1_enumset1(C_12,D_13,E_14)) = k2_xboole_0(k1_tarski(A_29),k3_enumset1(A_10,B_11,C_12,D_13,E_14)) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_52])).

tff(c_99,plain,(
    ! [B_11,A_10,C_12,A_29,E_14,D_13] : k2_xboole_0(k1_tarski(A_29),k3_enumset1(A_10,B_11,C_12,D_13,E_14)) = k4_enumset1(A_29,A_10,B_11,C_12,D_13,E_14) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_64])).

tff(c_10,plain,(
    k2_xboole_0(k1_tarski('#skF_1'),k3_enumset1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')) != k4_enumset1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_102,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_99,c_10])).

%------------------------------------------------------------------------------

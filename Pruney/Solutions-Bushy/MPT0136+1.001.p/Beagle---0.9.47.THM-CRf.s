%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0136+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:35:47 EST 2020

% Result     : Theorem 1.64s
% Output     : CNFRefutation 1.82s
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
%$ k4_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l62_enumset1)).

tff(f_30,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k1_tarski(A),k1_enumset1(B,C,D)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_enumset1)).

tff(f_28,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k2_xboole_0(k2_tarski(A,B),k1_tarski(C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_enumset1)).

tff(f_32,axiom,(
    ! [A,B,C] : k2_xboole_0(k2_xboole_0(A,B),C) = k2_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).

tff(f_35,negated_conjecture,(
    ~ ! [A,B,C,D,E,F] : k4_enumset1(A,B,C,D,E,F) = k2_xboole_0(k2_tarski(A,B),k2_enumset1(C,D,E,F)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_enumset1)).

tff(c_2,plain,(
    ! [B_2,C_3,A_1,E_5,D_4,F_6] : k2_xboole_0(k1_enumset1(A_1,B_2,C_3),k1_enumset1(D_4,E_5,F_6)) = k4_enumset1(A_1,B_2,C_3,D_4,E_5,F_6) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_6,plain,(
    ! [A_10,B_11,C_12,D_13] : k2_xboole_0(k1_tarski(A_10),k1_enumset1(B_11,C_12,D_13)) = k2_enumset1(A_10,B_11,C_12,D_13) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_28,plain,(
    ! [A_20,B_21,C_22] : k2_xboole_0(k2_tarski(A_20,B_21),k1_tarski(C_22)) = k1_enumset1(A_20,B_21,C_22) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_8,plain,(
    ! [A_14,B_15,C_16] : k2_xboole_0(k2_xboole_0(A_14,B_15),C_16) = k2_xboole_0(A_14,k2_xboole_0(B_15,C_16)) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_52,plain,(
    ! [A_27,B_28,C_29,C_30] : k2_xboole_0(k2_tarski(A_27,B_28),k2_xboole_0(k1_tarski(C_29),C_30)) = k2_xboole_0(k1_enumset1(A_27,B_28,C_29),C_30) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_8])).

tff(c_64,plain,(
    ! [B_11,A_10,C_12,B_28,D_13,A_27] : k2_xboole_0(k1_enumset1(A_27,B_28,A_10),k1_enumset1(B_11,C_12,D_13)) = k2_xboole_0(k2_tarski(A_27,B_28),k2_enumset1(A_10,B_11,C_12,D_13)) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_52])).

tff(c_99,plain,(
    ! [B_11,A_10,C_12,B_28,D_13,A_27] : k2_xboole_0(k2_tarski(A_27,B_28),k2_enumset1(A_10,B_11,C_12,D_13)) = k4_enumset1(A_27,B_28,A_10,B_11,C_12,D_13) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_64])).

tff(c_10,plain,(
    k2_xboole_0(k2_tarski('#skF_1','#skF_2'),k2_enumset1('#skF_3','#skF_4','#skF_5','#skF_6')) != k4_enumset1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_102,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_99,c_10])).

%------------------------------------------------------------------------------

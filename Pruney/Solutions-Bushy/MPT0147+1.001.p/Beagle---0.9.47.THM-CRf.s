%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0147+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:35:48 EST 2020

% Result     : Theorem 1.96s
% Output     : CNFRefutation 1.96s
% Verified   : 
% Statistics : Number of formulae       :   30 (  30 expanded)
%              Number of leaves         :   21 (  21 expanded)
%              Depth                    :    5
%              Number of atoms          :   14 (  14 expanded)
%              Number of equality atoms :   13 (  13 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k6_enumset1 > k4_enumset1 > k2_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_8 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_28,axiom,(
    ! [A,B,C,D,E,F,G,H] : k6_enumset1(A,B,C,D,E,F,G,H) = k2_xboole_0(k2_enumset1(A,B,C,D),k2_enumset1(E,F,G,H)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l75_enumset1)).

tff(f_32,axiom,(
    ! [A,B,C,D,E,F] : k4_enumset1(A,B,C,D,E,F) = k2_xboole_0(k2_tarski(A,B),k2_enumset1(C,D,E,F)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_enumset1)).

tff(f_26,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k2_tarski(A,B),k2_tarski(C,D)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l53_enumset1)).

tff(f_30,axiom,(
    ! [A,B,C] : k2_xboole_0(k2_xboole_0(A,B),C) = k2_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).

tff(f_35,negated_conjecture,(
    ~ ! [A,B,C,D,E,F,G,H] : k6_enumset1(A,B,C,D,E,F,G,H) = k2_xboole_0(k2_tarski(A,B),k4_enumset1(C,D,E,F,G,H)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_enumset1)).

tff(c_4,plain,(
    ! [B_6,H_12,C_7,E_9,D_8,A_5,G_11,F_10] : k2_xboole_0(k2_enumset1(A_5,B_6,C_7,D_8),k2_enumset1(E_9,F_10,G_11,H_12)) = k6_enumset1(A_5,B_6,C_7,D_8,E_9,F_10,G_11,H_12) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_8,plain,(
    ! [C_18,B_17,A_16,D_19,E_20,F_21] : k2_xboole_0(k2_tarski(A_16,B_17),k2_enumset1(C_18,D_19,E_20,F_21)) = k4_enumset1(A_16,B_17,C_18,D_19,E_20,F_21) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_28,plain,(
    ! [A_25,B_26,C_27,D_28] : k2_xboole_0(k2_tarski(A_25,B_26),k2_tarski(C_27,D_28)) = k2_enumset1(A_25,B_26,C_27,D_28) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_6,plain,(
    ! [A_13,B_14,C_15] : k2_xboole_0(k2_xboole_0(A_13,B_14),C_15) = k2_xboole_0(A_13,k2_xboole_0(B_14,C_15)) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_52,plain,(
    ! [C_39,B_38,A_36,C_37,D_35] : k2_xboole_0(k2_tarski(A_36,B_38),k2_xboole_0(k2_tarski(C_37,D_35),C_39)) = k2_xboole_0(k2_enumset1(A_36,B_38,C_37,D_35),C_39) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_6])).

tff(c_70,plain,(
    ! [B_38,A_36,C_18,B_17,A_16,D_19,E_20,F_21] : k2_xboole_0(k2_enumset1(A_36,B_38,A_16,B_17),k2_enumset1(C_18,D_19,E_20,F_21)) = k2_xboole_0(k2_tarski(A_36,B_38),k4_enumset1(A_16,B_17,C_18,D_19,E_20,F_21)) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_52])).

tff(c_153,plain,(
    ! [B_38,A_36,C_18,B_17,A_16,D_19,E_20,F_21] : k2_xboole_0(k2_tarski(A_36,B_38),k4_enumset1(A_16,B_17,C_18,D_19,E_20,F_21)) = k6_enumset1(A_36,B_38,A_16,B_17,C_18,D_19,E_20,F_21) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_70])).

tff(c_10,plain,(
    k2_xboole_0(k2_tarski('#skF_1','#skF_2'),k4_enumset1('#skF_3','#skF_4','#skF_5','#skF_6','#skF_7','#skF_8')) != k6_enumset1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_156,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_153,c_10])).

%------------------------------------------------------------------------------

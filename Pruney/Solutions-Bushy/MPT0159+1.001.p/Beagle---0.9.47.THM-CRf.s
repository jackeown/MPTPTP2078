%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0159+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:35:49 EST 2020

% Result     : Theorem 1.28s
% Output     : CNFRefutation 1.28s
% Verified   : 
% Statistics : Number of formulae       :   27 (  27 expanded)
%              Number of leaves         :   20 (  20 expanded)
%              Depth                    :    4
%              Number of atoms          :   11 (  11 expanded)
%              Number of equality atoms :   10 (  10 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k6_enumset1 > k5_enumset1 > k4_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

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

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_26,axiom,(
    ! [A,B,C,D,E,F,G] : k5_enumset1(A,B,C,D,E,F,G) = k2_xboole_0(k1_tarski(A),k4_enumset1(B,C,D,E,F,G)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_enumset1)).

tff(f_30,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_28,axiom,(
    ! [A,B,C,D,E,F,G,H] : k6_enumset1(A,B,C,D,E,F,G,H) = k2_xboole_0(k2_tarski(A,B),k4_enumset1(C,D,E,F,G,H)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_enumset1)).

tff(f_33,negated_conjecture,(
    ~ ! [A,B,C,D,E,F,G] : k6_enumset1(A,A,B,C,D,E,F,G) = k5_enumset1(A,B,C,D,E,F,G) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).

tff(c_2,plain,(
    ! [B_2,C_3,A_1,E_5,D_4,G_7,F_6] : k2_xboole_0(k1_tarski(A_1),k4_enumset1(B_2,C_3,D_4,E_5,F_6,G_7)) = k5_enumset1(A_1,B_2,C_3,D_4,E_5,F_6,G_7) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_6,plain,(
    ! [A_16] : k2_tarski(A_16,A_16) = k1_tarski(A_16) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_27,plain,(
    ! [C_29,H_31,B_28,A_26,F_25,D_32,E_27,G_30] : k2_xboole_0(k2_tarski(A_26,B_28),k4_enumset1(C_29,D_32,E_27,F_25,G_30,H_31)) = k6_enumset1(A_26,B_28,C_29,D_32,E_27,F_25,G_30,H_31) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_36,plain,(
    ! [C_29,H_31,A_16,F_25,D_32,E_27,G_30] : k6_enumset1(A_16,A_16,C_29,D_32,E_27,F_25,G_30,H_31) = k2_xboole_0(k1_tarski(A_16),k4_enumset1(C_29,D_32,E_27,F_25,G_30,H_31)) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_27])).

tff(c_39,plain,(
    ! [C_29,H_31,A_16,F_25,D_32,E_27,G_30] : k6_enumset1(A_16,A_16,C_29,D_32,E_27,F_25,G_30,H_31) = k5_enumset1(A_16,C_29,D_32,E_27,F_25,G_30,H_31) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_36])).

tff(c_8,plain,(
    k6_enumset1('#skF_1','#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7') != k5_enumset1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_42,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_39,c_8])).

%------------------------------------------------------------------------------

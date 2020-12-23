%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0187+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:35:52 EST 2020

% Result     : Theorem 1.64s
% Output     : CNFRefutation 1.64s
% Verified   : 
% Statistics : Number of formulae       :   21 (  30 expanded)
%              Number of leaves         :   14 (  18 expanded)
%              Depth                    :    4
%              Number of atoms          :   10 (  19 expanded)
%              Number of equality atoms :    9 (  18 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k2_enumset1 > k1_enumset1 > k2_xboole_0 > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

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

tff(f_26,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k1_enumset1(B,C,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_enumset1)).

tff(f_28,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k1_tarski(A),k1_enumset1(B,C,D)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_enumset1)).

tff(f_31,negated_conjecture,(
    ~ ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(A,C,D,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t105_enumset1)).

tff(c_2,plain,(
    ! [B_2,C_3,A_1] : k1_enumset1(B_2,C_3,A_1) = k1_enumset1(A_1,B_2,C_3) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_36,plain,(
    ! [A_11,B_12,C_13,D_14] : k2_xboole_0(k1_tarski(A_11),k1_enumset1(B_12,C_13,D_14)) = k2_enumset1(A_11,B_12,C_13,D_14) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_51,plain,(
    ! [A_15,B_16,C_17,A_18] : k2_xboole_0(k1_tarski(A_15),k1_enumset1(B_16,C_17,A_18)) = k2_enumset1(A_15,A_18,B_16,C_17) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_36])).

tff(c_4,plain,(
    ! [A_4,B_5,C_6,D_7] : k2_xboole_0(k1_tarski(A_4),k1_enumset1(B_5,C_6,D_7)) = k2_enumset1(A_4,B_5,C_6,D_7) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_57,plain,(
    ! [A_15,B_16,C_17,A_18] : k2_enumset1(A_15,B_16,C_17,A_18) = k2_enumset1(A_15,A_18,B_16,C_17) ),
    inference(superposition,[status(thm),theory(equality)],[c_51,c_4])).

tff(c_6,plain,(
    k2_enumset1('#skF_1','#skF_2','#skF_3','#skF_4') != k2_enumset1('#skF_1','#skF_3','#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_75,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_57,c_57,c_6])).

%------------------------------------------------------------------------------

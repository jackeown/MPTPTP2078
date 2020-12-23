%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0127+1.001 : TPTP v7.4.0. Released v7.4.0.
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

% Result     : Theorem 3.26s
% Output     : CNFRefutation 3.26s
% Verified   : 
% Statistics : Number of formulae       :   34 (  75 expanded)
%              Number of leaves         :   15 (  33 expanded)
%              Depth                    :    6
%              Number of atoms          :   24 (  65 expanded)
%              Number of equality atoms :   23 (  64 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_26,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_30,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k2_xboole_0(k1_tarski(A),k2_tarski(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_enumset1)).

tff(f_28,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_xboole_0(k1_tarski(A),k1_tarski(B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).

tff(f_32,axiom,(
    ! [A,B,C] : k2_xboole_0(k2_xboole_0(A,B),C) = k2_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).

tff(f_35,negated_conjecture,(
    ~ ! [A,B,C] : k1_enumset1(A,B,C) = k2_xboole_0(k2_tarski(A,B),k1_tarski(C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_enumset1)).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_131,plain,(
    ! [A_19,B_20,C_21] : k2_xboole_0(k1_tarski(A_19),k2_tarski(B_20,C_21)) = k1_enumset1(A_19,B_20,C_21) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_155,plain,(
    ! [B_20,C_21,A_19] : k2_xboole_0(k2_tarski(B_20,C_21),k1_tarski(A_19)) = k1_enumset1(A_19,B_20,C_21) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_131])).

tff(c_6,plain,(
    ! [A_5,B_6,C_7] : k2_xboole_0(k1_tarski(A_5),k2_tarski(B_6,C_7)) = k1_enumset1(A_5,B_6,C_7) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_46,plain,(
    ! [A_13,B_14] : k2_xboole_0(k1_tarski(A_13),k1_tarski(B_14)) = k2_tarski(A_13,B_14) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_52,plain,(
    ! [B_14,A_13] : k2_xboole_0(k1_tarski(B_14),k1_tarski(A_13)) = k2_tarski(A_13,B_14) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_2])).

tff(c_4,plain,(
    ! [A_3,B_4] : k2_xboole_0(k1_tarski(A_3),k1_tarski(B_4)) = k2_tarski(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_160,plain,(
    ! [A_22,B_23,C_24] : k2_xboole_0(k2_xboole_0(A_22,B_23),C_24) = k2_xboole_0(A_22,k2_xboole_0(B_23,C_24)) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_886,plain,(
    ! [A_40,B_41,C_42] : k2_xboole_0(k1_tarski(A_40),k2_xboole_0(k1_tarski(B_41),C_42)) = k2_xboole_0(k2_tarski(A_40,B_41),C_42) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_160])).

tff(c_975,plain,(
    ! [A_40,B_14,A_13] : k2_xboole_0(k2_tarski(A_40,B_14),k1_tarski(A_13)) = k2_xboole_0(k1_tarski(A_40),k2_tarski(A_13,B_14)) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_886])).

tff(c_1005,plain,(
    ! [A_40,A_13,B_14] : k1_enumset1(A_40,A_13,B_14) = k1_enumset1(A_13,A_40,B_14) ),
    inference(demodulation,[status(thm),theory(equality)],[c_155,c_6,c_975])).

tff(c_978,plain,(
    ! [A_40,A_3,B_4] : k2_xboole_0(k2_tarski(A_40,A_3),k1_tarski(B_4)) = k2_xboole_0(k1_tarski(A_40),k2_tarski(A_3,B_4)) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_886])).

tff(c_1041,plain,(
    ! [B_46,A_47,A_48] : k1_enumset1(B_46,A_47,A_48) = k1_enumset1(A_47,A_48,B_46) ),
    inference(demodulation,[status(thm),theory(equality)],[c_155,c_6,c_978])).

tff(c_1086,plain,(
    ! [A_13,B_14,A_40] : k1_enumset1(A_13,B_14,A_40) = k1_enumset1(A_13,A_40,B_14) ),
    inference(superposition,[status(thm),theory(equality)],[c_1005,c_1041])).

tff(c_10,plain,(
    k2_xboole_0(k2_tarski('#skF_1','#skF_2'),k1_tarski('#skF_3')) != k1_enumset1('#skF_1','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_11,plain,(
    k2_xboole_0(k1_tarski('#skF_3'),k2_tarski('#skF_1','#skF_2')) != k1_enumset1('#skF_1','#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_10])).

tff(c_12,plain,(
    k1_enumset1('#skF_3','#skF_1','#skF_2') != k1_enumset1('#skF_1','#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_11])).

tff(c_1007,plain,(
    k1_enumset1('#skF_1','#skF_2','#skF_3') != k1_enumset1('#skF_1','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1005,c_12])).

tff(c_1178,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1086,c_1007])).

%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0119+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:35:45 EST 2020

% Result     : Theorem 3.78s
% Output     : CNFRefutation 4.18s
% Verified   : 
% Statistics : Number of formulae       :   29 (  36 expanded)
%              Number of leaves         :   15 (  19 expanded)
%              Depth                    :    6
%              Number of atoms          :   19 (  26 expanded)
%              Number of equality atoms :   18 (  25 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_28,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k2_xboole_0(k4_xboole_0(A,B),k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_xboole_0)).

tff(f_26,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_32,axiom,(
    ! [A,B,C] : k3_xboole_0(A,k2_xboole_0(B,C)) = k2_xboole_0(k3_xboole_0(A,B),k3_xboole_0(A,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_xboole_1)).

tff(f_30,axiom,(
    ! [A,B,C] : k4_xboole_0(k3_xboole_0(A,B),k3_xboole_0(C,B)) = k3_xboole_0(k4_xboole_0(A,C),B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t111_xboole_1)).

tff(f_35,negated_conjecture,(
    ~ ! [A,B,C] : k5_xboole_0(k3_xboole_0(A,B),k3_xboole_0(C,B)) = k3_xboole_0(k5_xboole_0(A,C),B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t112_xboole_1)).

tff(c_4,plain,(
    ! [A_3,B_4] : k2_xboole_0(k4_xboole_0(A_3,B_4),k4_xboole_0(B_4,A_3)) = k5_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_83,plain,(
    ! [A_18,B_19,C_20] : k2_xboole_0(k3_xboole_0(A_18,B_19),k3_xboole_0(A_18,C_20)) = k3_xboole_0(A_18,k2_xboole_0(B_19,C_20)) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_104,plain,(
    ! [B_21,B_22,A_23] : k2_xboole_0(k3_xboole_0(B_21,B_22),k3_xboole_0(A_23,B_21)) = k3_xboole_0(B_21,k2_xboole_0(B_22,A_23)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_83])).

tff(c_127,plain,(
    ! [A_1,B_2,A_23] : k2_xboole_0(k3_xboole_0(A_1,B_2),k3_xboole_0(A_23,B_2)) = k3_xboole_0(B_2,k2_xboole_0(A_1,A_23)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_104])).

tff(c_6,plain,(
    ! [A_5,B_6,C_7] : k4_xboole_0(k3_xboole_0(A_5,B_6),k3_xboole_0(C_7,B_6)) = k3_xboole_0(k4_xboole_0(A_5,C_7),B_6) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_54,plain,(
    ! [A_15,B_16,C_17] : k4_xboole_0(k3_xboole_0(A_15,B_16),k3_xboole_0(C_17,B_16)) = k3_xboole_0(k4_xboole_0(A_15,C_17),B_16) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_60,plain,(
    ! [A_15,C_17,B_16] : k2_xboole_0(k3_xboole_0(k4_xboole_0(A_15,C_17),B_16),k4_xboole_0(k3_xboole_0(C_17,B_16),k3_xboole_0(A_15,B_16))) = k5_xboole_0(k3_xboole_0(A_15,B_16),k3_xboole_0(C_17,B_16)) ),
    inference(superposition,[status(thm),theory(equality)],[c_54,c_4])).

tff(c_1912,plain,(
    ! [A_51,C_52,B_53] : k2_xboole_0(k3_xboole_0(k4_xboole_0(A_51,C_52),B_53),k3_xboole_0(k4_xboole_0(C_52,A_51),B_53)) = k5_xboole_0(k3_xboole_0(A_51,B_53),k3_xboole_0(C_52,B_53)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_60])).

tff(c_1961,plain,(
    ! [A_51,B_2,C_52] : k5_xboole_0(k3_xboole_0(A_51,B_2),k3_xboole_0(C_52,B_2)) = k3_xboole_0(B_2,k2_xboole_0(k4_xboole_0(A_51,C_52),k4_xboole_0(C_52,A_51))) ),
    inference(superposition,[status(thm),theory(equality)],[c_127,c_1912])).

tff(c_2085,plain,(
    ! [A_51,B_2,C_52] : k5_xboole_0(k3_xboole_0(A_51,B_2),k3_xboole_0(C_52,B_2)) = k3_xboole_0(B_2,k5_xboole_0(A_51,C_52)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_1961])).

tff(c_10,plain,(
    k5_xboole_0(k3_xboole_0('#skF_1','#skF_2'),k3_xboole_0('#skF_3','#skF_2')) != k3_xboole_0(k5_xboole_0('#skF_1','#skF_3'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_11,plain,(
    k5_xboole_0(k3_xboole_0('#skF_1','#skF_2'),k3_xboole_0('#skF_3','#skF_2')) != k3_xboole_0('#skF_2',k5_xboole_0('#skF_1','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_10])).

tff(c_2103,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2085,c_11])).

%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0152+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:35:49 EST 2020

% Result     : Theorem 1.79s
% Output     : CNFRefutation 1.93s
% Verified   : 
% Statistics : Number of formulae       :   31 (  31 expanded)
%              Number of leaves         :   22 (  22 expanded)
%              Depth                    :    5
%              Number of atoms          :   14 (  14 expanded)
%              Number of equality atoms :   13 (  13 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k6_enumset1 > k5_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > #nlpp > k1_tarski > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_8 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

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

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_28,axiom,(
    ! [A,B,C,D,E,F,G,H] : k6_enumset1(A,B,C,D,E,F,G,H) = k2_xboole_0(k2_enumset1(A,B,C,D),k2_enumset1(E,F,G,H)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l75_enumset1)).

tff(f_30,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k1_enumset1(A,B,C),k1_tarski(D)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_enumset1)).

tff(f_26,axiom,(
    ! [A,B,C,D,E,F,G] : k5_enumset1(A,B,C,D,E,F,G) = k2_xboole_0(k2_enumset1(A,B,C,D),k1_enumset1(E,F,G)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l68_enumset1)).

tff(f_32,axiom,(
    ! [A,B,C] : k2_xboole_0(k2_xboole_0(A,B),C) = k2_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).

tff(f_35,negated_conjecture,(
    ~ ! [A,B,C,D,E,F,G,H] : k6_enumset1(A,B,C,D,E,F,G,H) = k2_xboole_0(k5_enumset1(A,B,C,D,E,F,G),k1_tarski(H)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t68_enumset1)).

tff(c_4,plain,(
    ! [E_12,D_11,A_8,C_10,B_9,H_15,F_13,G_14] : k2_xboole_0(k2_enumset1(A_8,B_9,C_10,D_11),k2_enumset1(E_12,F_13,G_14,H_15)) = k6_enumset1(A_8,B_9,C_10,D_11,E_12,F_13,G_14,H_15) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_6,plain,(
    ! [A_16,B_17,C_18,D_19] : k2_xboole_0(k1_enumset1(A_16,B_17,C_18),k1_tarski(D_19)) = k2_enumset1(A_16,B_17,C_18,D_19) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_53,plain,(
    ! [B_39,E_37,D_38,A_41,G_36,F_35,C_40] : k2_xboole_0(k2_enumset1(A_41,B_39,C_40,D_38),k1_enumset1(E_37,F_35,G_36)) = k5_enumset1(A_41,B_39,C_40,D_38,E_37,F_35,G_36) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_8,plain,(
    ! [A_20,B_21,C_22] : k2_xboole_0(k2_xboole_0(A_20,B_21),C_22) = k2_xboole_0(A_20,k2_xboole_0(B_21,C_22)) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_77,plain,(
    ! [G_57,D_56,B_53,E_52,F_54,C_50,A_51,C_55] : k2_xboole_0(k2_enumset1(A_51,B_53,C_55,D_56),k2_xboole_0(k1_enumset1(E_52,F_54,G_57),C_50)) = k2_xboole_0(k5_enumset1(A_51,B_53,C_55,D_56,E_52,F_54,G_57),C_50) ),
    inference(superposition,[status(thm),theory(equality)],[c_53,c_8])).

tff(c_92,plain,(
    ! [C_18,B_17,A_16,D_56,B_53,D_19,A_51,C_55] : k2_xboole_0(k5_enumset1(A_51,B_53,C_55,D_56,A_16,B_17,C_18),k1_tarski(D_19)) = k2_xboole_0(k2_enumset1(A_51,B_53,C_55,D_56),k2_enumset1(A_16,B_17,C_18,D_19)) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_77])).

tff(c_96,plain,(
    ! [C_18,B_17,A_16,D_56,B_53,D_19,A_51,C_55] : k2_xboole_0(k5_enumset1(A_51,B_53,C_55,D_56,A_16,B_17,C_18),k1_tarski(D_19)) = k6_enumset1(A_51,B_53,C_55,D_56,A_16,B_17,C_18,D_19) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_92])).

tff(c_10,plain,(
    k2_xboole_0(k5_enumset1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'),k1_tarski('#skF_8')) != k6_enumset1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_99,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_10])).

%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0201+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:35:54 EST 2020

% Result     : Theorem 1.83s
% Output     : CNFRefutation 1.83s
% Verified   : 
% Statistics : Number of formulae       :   33 (  33 expanded)
%              Number of leaves         :   24 (  24 expanded)
%              Depth                    :    5
%              Number of atoms          :   14 (  14 expanded)
%              Number of equality atoms :   13 (  13 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k7_enumset1 > k6_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > #nlpp > k1_tarski > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_9 > #skF_8 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k7_enumset1,type,(
    k7_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

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

tff('#skF_9',type,(
    '#skF_9': $i )).

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

tff(f_26,axiom,(
    ! [A,B,C,D,E,F,G,H,I] : k7_enumset1(A,B,C,D,E,F,G,H,I) = k2_xboole_0(k2_enumset1(A,B,C,D),k3_enumset1(E,F,G,H,I)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l142_enumset1)).

tff(f_32,axiom,(
    ! [A,B,C,D,E,F,G,H] : k6_enumset1(A,B,C,D,E,F,G,H) = k2_xboole_0(k1_enumset1(A,B,C),k3_enumset1(D,E,F,G,H)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_enumset1)).

tff(f_28,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k1_tarski(A),k1_enumset1(B,C,D)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_enumset1)).

tff(f_30,axiom,(
    ! [A,B,C] : k2_xboole_0(k2_xboole_0(A,B),C) = k2_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).

tff(f_35,negated_conjecture,(
    ~ ! [A,B,C,D,E,F,G,H,I] : k7_enumset1(A,B,C,D,E,F,G,H,I) = k2_xboole_0(k1_tarski(A),k6_enumset1(B,C,D,E,F,G,H,I)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t127_enumset1)).

tff(c_2,plain,(
    ! [B_2,C_3,A_1,H_8,E_5,D_4,I_9,G_7,F_6] : k2_xboole_0(k2_enumset1(A_1,B_2,C_3,D_4),k3_enumset1(E_5,F_6,G_7,H_8,I_9)) = k7_enumset1(A_1,B_2,C_3,D_4,E_5,F_6,G_7,H_8,I_9) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_53,plain,(
    ! [D_41,F_40,B_39,C_37,G_43,A_38,H_44,E_42] : k2_xboole_0(k1_enumset1(A_38,B_39,C_37),k3_enumset1(D_41,E_42,F_40,G_43,H_44)) = k6_enumset1(A_38,B_39,C_37,D_41,E_42,F_40,G_43,H_44) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_28,plain,(
    ! [A_28,B_29,C_30,D_31] : k2_xboole_0(k1_tarski(A_28),k1_enumset1(B_29,C_30,D_31)) = k2_enumset1(A_28,B_29,C_30,D_31) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_6,plain,(
    ! [A_14,B_15,C_16] : k2_xboole_0(k2_xboole_0(A_14,B_15),C_16) = k2_xboole_0(A_14,k2_xboole_0(B_15,C_16)) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_34,plain,(
    ! [C_30,D_31,B_29,C_16,A_28] : k2_xboole_0(k1_tarski(A_28),k2_xboole_0(k1_enumset1(B_29,C_30,D_31),C_16)) = k2_xboole_0(k2_enumset1(A_28,B_29,C_30,D_31),C_16) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_6])).

tff(c_59,plain,(
    ! [D_41,F_40,B_39,C_37,G_43,A_38,H_44,E_42,A_28] : k2_xboole_0(k2_enumset1(A_28,A_38,B_39,C_37),k3_enumset1(D_41,E_42,F_40,G_43,H_44)) = k2_xboole_0(k1_tarski(A_28),k6_enumset1(A_38,B_39,C_37,D_41,E_42,F_40,G_43,H_44)) ),
    inference(superposition,[status(thm),theory(equality)],[c_53,c_34])).

tff(c_96,plain,(
    ! [D_41,F_40,B_39,C_37,G_43,A_38,H_44,E_42,A_28] : k2_xboole_0(k1_tarski(A_28),k6_enumset1(A_38,B_39,C_37,D_41,E_42,F_40,G_43,H_44)) = k7_enumset1(A_28,A_38,B_39,C_37,D_41,E_42,F_40,G_43,H_44) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_59])).

tff(c_10,plain,(
    k2_xboole_0(k1_tarski('#skF_1'),k6_enumset1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7','#skF_8','#skF_9')) != k7_enumset1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7','#skF_8','#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_99,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_10])).

%------------------------------------------------------------------------------

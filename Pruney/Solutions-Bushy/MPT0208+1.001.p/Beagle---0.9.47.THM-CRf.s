%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0208+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:35:55 EST 2020

% Result     : Theorem 1.67s
% Output     : CNFRefutation 1.67s
% Verified   : 
% Statistics : Number of formulae       :   32 (  32 expanded)
%              Number of leaves         :   23 (  23 expanded)
%              Depth                    :    5
%              Number of atoms          :   14 (  14 expanded)
%              Number of equality atoms :   13 (  13 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k7_enumset1 > k6_enumset1 > k3_enumset1 > k2_enumset1 > k2_xboole_0 > #nlpp > k1_tarski > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_9 > #skF_8 > #skF_4

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
    ! [A,B,C,D,E] : k3_enumset1(A,B,C,D,E) = k2_xboole_0(k2_enumset1(A,B,C,D),k1_tarski(E)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_enumset1)).

tff(f_28,axiom,(
    ! [A,B,C,D,E,F,G,H] : k6_enumset1(A,B,C,D,E,F,G,H) = k2_xboole_0(k2_enumset1(A,B,C,D),k2_enumset1(E,F,G,H)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l75_enumset1)).

tff(f_30,axiom,(
    ! [A,B,C] : k2_xboole_0(k2_xboole_0(A,B),C) = k2_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).

tff(f_35,negated_conjecture,(
    ~ ! [A,B,C,D,E,F,G,H,I] : k7_enumset1(A,B,C,D,E,F,G,H,I) = k2_xboole_0(k6_enumset1(A,B,C,D,E,F,G,H),k1_tarski(I)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t134_enumset1)).

tff(c_2,plain,(
    ! [B_2,C_3,A_1,H_8,E_5,D_4,I_9,G_7,F_6] : k2_xboole_0(k2_enumset1(A_1,B_2,C_3,D_4),k3_enumset1(E_5,F_6,G_7,H_8,I_9)) = k7_enumset1(A_1,B_2,C_3,D_4,E_5,F_6,G_7,H_8,I_9) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_8,plain,(
    ! [A_21,B_22,D_24,C_23,E_25] : k2_xboole_0(k2_enumset1(A_21,B_22,C_23,D_24),k1_tarski(E_25)) = k3_enumset1(A_21,B_22,C_23,D_24,E_25) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_53,plain,(
    ! [F_46,E_43,H_42,C_47,D_45,A_44,G_40,B_41] : k2_xboole_0(k2_enumset1(A_44,B_41,C_47,D_45),k2_enumset1(E_43,F_46,G_40,H_42)) = k6_enumset1(A_44,B_41,C_47,D_45,E_43,F_46,G_40,H_42) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_6,plain,(
    ! [A_18,B_19,C_20] : k2_xboole_0(k2_xboole_0(A_18,B_19),C_20) = k2_xboole_0(A_18,k2_xboole_0(B_19,C_20)) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_77,plain,(
    ! [A_61,H_58,D_57,C_60,C_59,B_65,F_62,E_64,G_63] : k2_xboole_0(k2_enumset1(A_61,B_65,C_60,D_57),k2_xboole_0(k2_enumset1(E_64,F_62,G_63,H_58),C_59)) = k2_xboole_0(k6_enumset1(A_61,B_65,C_60,D_57,E_64,F_62,G_63,H_58),C_59) ),
    inference(superposition,[status(thm),theory(equality)],[c_53,c_6])).

tff(c_104,plain,(
    ! [A_21,B_22,A_61,D_24,C_23,E_25,D_57,C_60,B_65] : k2_xboole_0(k6_enumset1(A_61,B_65,C_60,D_57,A_21,B_22,C_23,D_24),k1_tarski(E_25)) = k2_xboole_0(k2_enumset1(A_61,B_65,C_60,D_57),k3_enumset1(A_21,B_22,C_23,D_24,E_25)) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_77])).

tff(c_108,plain,(
    ! [A_21,B_22,A_61,D_24,C_23,E_25,D_57,C_60,B_65] : k2_xboole_0(k6_enumset1(A_61,B_65,C_60,D_57,A_21,B_22,C_23,D_24),k1_tarski(E_25)) = k7_enumset1(A_61,B_65,C_60,D_57,A_21,B_22,C_23,D_24,E_25) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_104])).

tff(c_10,plain,(
    k2_xboole_0(k6_enumset1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'),k1_tarski('#skF_9')) != k7_enumset1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7','#skF_8','#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_111,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_108,c_10])).

%------------------------------------------------------------------------------

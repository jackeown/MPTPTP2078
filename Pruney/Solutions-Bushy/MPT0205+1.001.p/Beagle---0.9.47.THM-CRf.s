%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0205+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:35:54 EST 2020

% Result     : Theorem 1.88s
% Output     : CNFRefutation 1.88s
% Verified   : 
% Statistics : Number of formulae       :   31 (  31 expanded)
%              Number of leaves         :   22 (  22 expanded)
%              Depth                    :    5
%              Number of atoms          :   14 (  14 expanded)
%              Number of equality atoms :   13 (  13 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k7_enumset1 > k3_enumset1 > k2_enumset1 > k2_xboole_0 > #nlpp > k1_tarski > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_9 > #skF_8 > #skF_4

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

tff(f_28,axiom,(
    ! [A,B,C,D,E] : k3_enumset1(A,B,C,D,E) = k2_xboole_0(k1_tarski(A),k2_enumset1(B,C,D,E)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_enumset1)).

tff(f_32,axiom,(
    ! [A,B,C,D,E] : k3_enumset1(A,B,C,D,E) = k2_xboole_0(k2_enumset1(A,B,C,D),k1_tarski(E)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_enumset1)).

tff(f_30,axiom,(
    ! [A,B,C] : k2_xboole_0(k2_xboole_0(A,B),C) = k2_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).

tff(f_35,negated_conjecture,(
    ~ ! [A,B,C,D,E,F,G,H,I] : k7_enumset1(A,B,C,D,E,F,G,H,I) = k2_xboole_0(k3_enumset1(A,B,C,D,E),k2_enumset1(F,G,H,I)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t131_enumset1)).

tff(c_2,plain,(
    ! [B_2,C_3,A_1,H_8,E_5,D_4,I_9,G_7,F_6] : k2_xboole_0(k2_enumset1(A_1,B_2,C_3,D_4),k3_enumset1(E_5,F_6,G_7,H_8,I_9)) = k7_enumset1(A_1,B_2,C_3,D_4,E_5,F_6,G_7,H_8,I_9) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_4,plain,(
    ! [B_11,A_10,C_12,E_14,D_13] : k2_xboole_0(k1_tarski(A_10),k2_enumset1(B_11,C_12,D_13,E_14)) = k3_enumset1(A_10,B_11,C_12,D_13,E_14) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_40,plain,(
    ! [E_33,A_31,C_32,D_34,B_35] : k2_xboole_0(k2_enumset1(A_31,B_35,C_32,D_34),k1_tarski(E_33)) = k3_enumset1(A_31,B_35,C_32,D_34,E_33) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_6,plain,(
    ! [A_15,B_16,C_17] : k2_xboole_0(k2_xboole_0(A_15,B_16),C_17) = k2_xboole_0(A_15,k2_xboole_0(B_16,C_17)) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_68,plain,(
    ! [C_43,A_45,E_47,D_42,B_46,C_44] : k2_xboole_0(k2_enumset1(A_45,B_46,C_44,D_42),k2_xboole_0(k1_tarski(E_47),C_43)) = k2_xboole_0(k3_enumset1(A_45,B_46,C_44,D_42,E_47),C_43) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_6])).

tff(c_86,plain,(
    ! [B_11,A_10,C_12,A_45,E_14,D_42,B_46,D_13,C_44] : k2_xboole_0(k3_enumset1(A_45,B_46,C_44,D_42,A_10),k2_enumset1(B_11,C_12,D_13,E_14)) = k2_xboole_0(k2_enumset1(A_45,B_46,C_44,D_42),k3_enumset1(A_10,B_11,C_12,D_13,E_14)) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_68])).

tff(c_137,plain,(
    ! [B_11,A_10,C_12,A_45,E_14,D_42,B_46,D_13,C_44] : k2_xboole_0(k3_enumset1(A_45,B_46,C_44,D_42,A_10),k2_enumset1(B_11,C_12,D_13,E_14)) = k7_enumset1(A_45,B_46,C_44,D_42,A_10,B_11,C_12,D_13,E_14) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_86])).

tff(c_10,plain,(
    k2_xboole_0(k3_enumset1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5'),k2_enumset1('#skF_6','#skF_7','#skF_8','#skF_9')) != k7_enumset1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7','#skF_8','#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_140,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_137,c_10])).

%------------------------------------------------------------------------------

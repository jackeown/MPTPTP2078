%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0128+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:35:46 EST 2020

% Result     : Theorem 17.75s
% Output     : CNFRefutation 17.92s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 339 expanded)
%              Number of leaves         :   18 ( 124 expanded)
%              Depth                    :   12
%              Number of atoms          :   54 ( 327 expanded)
%              Number of equality atoms :   53 ( 326 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(f_28,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k2_tarski(A,B),k2_tarski(C,D)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l53_enumset1)).

tff(f_32,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k2_xboole_0(k1_tarski(A),k2_tarski(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_enumset1)).

tff(f_30,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_xboole_0(k1_tarski(A),k1_tarski(B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).

tff(f_34,axiom,(
    ! [A,B,C] : k2_xboole_0(k2_xboole_0(A,B),C) = k2_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).

tff(f_26,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_37,negated_conjecture,(
    ~ ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k1_tarski(A),k1_enumset1(B,C,D)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_enumset1)).

tff(c_4,plain,(
    ! [A_3,B_4,C_5,D_6] : k2_xboole_0(k2_tarski(A_3,B_4),k2_tarski(C_5,D_6)) = k2_enumset1(A_3,B_4,C_5,D_6) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_8,plain,(
    ! [A_9,B_10,C_11] : k2_xboole_0(k1_tarski(A_9),k2_tarski(B_10,C_11)) = k1_enumset1(A_9,B_10,C_11) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_6,plain,(
    ! [A_7,B_8] : k2_xboole_0(k1_tarski(A_7),k1_tarski(B_8)) = k2_tarski(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_131,plain,(
    ! [A_23,B_24,C_25] : k2_xboole_0(k2_xboole_0(A_23,B_24),C_25) = k2_xboole_0(A_23,k2_xboole_0(B_24,C_25)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_1470,plain,(
    ! [A_65,B_66,C_67] : k2_xboole_0(k1_tarski(A_65),k2_xboole_0(k1_tarski(B_66),C_67)) = k2_xboole_0(k2_tarski(A_65,B_66),C_67) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_131])).

tff(c_1587,plain,(
    ! [A_65,A_9,B_10,C_11] : k2_xboole_0(k2_tarski(A_65,A_9),k2_tarski(B_10,C_11)) = k2_xboole_0(k1_tarski(A_65),k1_enumset1(A_9,B_10,C_11)) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_1470])).

tff(c_1621,plain,(
    ! [A_65,A_9,B_10,C_11] : k2_xboole_0(k1_tarski(A_65),k1_enumset1(A_9,B_10,C_11)) = k2_enumset1(A_65,A_9,B_10,C_11) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_1587])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_177,plain,(
    ! [A_26,B_27,C_28] : k2_xboole_0(k1_tarski(A_26),k2_tarski(B_27,C_28)) = k1_enumset1(A_26,B_27,C_28) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_204,plain,(
    ! [B_27,C_28,A_26] : k2_xboole_0(k2_tarski(B_27,C_28),k1_tarski(A_26)) = k1_enumset1(A_26,B_27,C_28) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_177])).

tff(c_46,plain,(
    ! [A_17,B_18] : k2_xboole_0(k1_tarski(A_17),k1_tarski(B_18)) = k2_tarski(A_17,B_18) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_52,plain,(
    ! [B_18,A_17] : k2_xboole_0(k1_tarski(B_18),k1_tarski(A_17)) = k2_tarski(A_17,B_18) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_2])).

tff(c_1590,plain,(
    ! [A_65,B_18,A_17] : k2_xboole_0(k2_tarski(A_65,B_18),k1_tarski(A_17)) = k2_xboole_0(k1_tarski(A_65),k2_tarski(A_17,B_18)) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_1470])).

tff(c_1622,plain,(
    ! [A_65,A_17,B_18] : k1_enumset1(A_65,A_17,B_18) = k1_enumset1(A_17,A_65,B_18) ),
    inference(demodulation,[status(thm),theory(equality)],[c_204,c_8,c_1590])).

tff(c_7137,plain,(
    ! [A_139,A_140,B_141,C_142] : k2_xboole_0(k1_tarski(A_139),k1_enumset1(A_140,B_141,C_142)) = k2_enumset1(A_139,A_140,B_141,C_142) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_1587])).

tff(c_21090,plain,(
    ! [A_252,A_253,A_254,B_255] : k2_xboole_0(k1_tarski(A_252),k1_enumset1(A_253,A_254,B_255)) = k2_enumset1(A_252,A_254,A_253,B_255) ),
    inference(superposition,[status(thm),theory(equality)],[c_1622,c_7137])).

tff(c_21234,plain,(
    ! [A_65,B_10,A_9,C_11] : k2_enumset1(A_65,B_10,A_9,C_11) = k2_enumset1(A_65,A_9,B_10,C_11) ),
    inference(superposition,[status(thm),theory(equality)],[c_1621,c_21090])).

tff(c_6503,plain,(
    ! [B_133,A_134,C_135] : k2_xboole_0(k1_tarski(B_133),k2_xboole_0(k1_tarski(A_134),C_135)) = k2_xboole_0(k2_tarski(A_134,B_133),C_135) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_131])).

tff(c_6755,plain,(
    ! [A_9,B_133,B_10,C_11] : k2_xboole_0(k2_tarski(A_9,B_133),k2_tarski(B_10,C_11)) = k2_xboole_0(k1_tarski(B_133),k1_enumset1(A_9,B_10,C_11)) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_6503])).

tff(c_7241,plain,(
    ! [B_143,A_144,B_145,C_146] : k2_xboole_0(k1_tarski(B_143),k1_enumset1(A_144,B_145,C_146)) = k2_enumset1(A_144,B_143,B_145,C_146) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_6755])).

tff(c_7603,plain,(
    ! [B_150,A_151,B_152,C_153] : k2_enumset1(B_150,A_151,B_152,C_153) = k2_enumset1(A_151,B_150,B_152,C_153) ),
    inference(superposition,[status(thm),theory(equality)],[c_7241,c_1621])).

tff(c_440,plain,(
    ! [B_39,A_40,C_41] : k2_xboole_0(k2_xboole_0(B_39,A_40),C_41) = k2_xboole_0(A_40,k2_xboole_0(B_39,C_41)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_131])).

tff(c_520,plain,(
    ! [B_2,B_39,A_40] : k2_xboole_0(B_2,k2_xboole_0(B_39,A_40)) = k2_xboole_0(A_40,k2_xboole_0(B_39,B_2)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_440])).

tff(c_1552,plain,(
    ! [A_40,B_66,A_65] : k2_xboole_0(A_40,k2_xboole_0(k1_tarski(B_66),k1_tarski(A_65))) = k2_xboole_0(k2_tarski(A_65,B_66),A_40) ),
    inference(superposition,[status(thm),theory(equality)],[c_520,c_1470])).

tff(c_1619,plain,(
    ! [A_65,B_66,A_40] : k2_xboole_0(k2_tarski(A_65,B_66),A_40) = k2_xboole_0(A_40,k2_tarski(B_66,A_65)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_1552])).

tff(c_2549,plain,(
    ! [A_83,B_84,A_85] : k2_xboole_0(k2_tarski(A_83,B_84),A_85) = k2_xboole_0(A_85,k2_tarski(B_84,A_83)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_1552])).

tff(c_2741,plain,(
    ! [B_84,A_83,B_66,A_65] : k2_xboole_0(k2_tarski(B_84,A_83),k2_tarski(B_66,A_65)) = k2_xboole_0(k2_tarski(A_83,B_84),k2_tarski(A_65,B_66)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1619,c_2549])).

tff(c_2849,plain,(
    ! [B_84,A_83,B_66,A_65] : k2_enumset1(B_84,A_83,B_66,A_65) = k2_enumset1(A_83,B_84,A_65,B_66) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_4,c_2741])).

tff(c_7618,plain,(
    ! [B_150,A_151,C_153,B_152] : k2_enumset1(B_150,A_151,C_153,B_152) = k2_enumset1(B_150,A_151,B_152,C_153) ),
    inference(superposition,[status(thm),theory(equality)],[c_7603,c_2849])).

tff(c_207,plain,(
    ! [B_29,A_30,B_31] : k2_xboole_0(B_29,k2_xboole_0(A_30,B_31)) = k2_xboole_0(A_30,k2_xboole_0(B_31,B_29)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_131])).

tff(c_3263,plain,(
    ! [B_95,A_96,B_97] : k2_xboole_0(k1_tarski(B_95),k2_xboole_0(k1_tarski(A_96),B_97)) = k2_xboole_0(B_97,k2_tarski(A_96,B_95)) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_207])).

tff(c_162,plain,(
    ! [B_2,A_23,B_24] : k2_xboole_0(B_2,k2_xboole_0(A_23,B_24)) = k2_xboole_0(A_23,k2_xboole_0(B_24,B_2)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_131])).

tff(c_3332,plain,(
    ! [B_97,B_95,A_96] : k2_xboole_0(B_97,k2_xboole_0(k1_tarski(B_95),k1_tarski(A_96))) = k2_xboole_0(B_97,k2_tarski(A_96,B_95)) ),
    inference(superposition,[status(thm),theory(equality)],[c_3263,c_162])).

tff(c_4223,plain,(
    ! [B_104,B_105,A_106] : k2_xboole_0(B_104,k2_tarski(B_105,A_106)) = k2_xboole_0(B_104,k2_tarski(A_106,B_105)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_3332])).

tff(c_4483,plain,(
    ! [A_65,B_66,B_105,A_106] : k2_xboole_0(k2_tarski(A_65,B_66),k2_tarski(B_105,A_106)) = k2_xboole_0(k2_tarski(A_106,B_105),k2_tarski(B_66,A_65)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1619,c_4223])).

tff(c_4591,plain,(
    ! [A_65,B_66,B_105,A_106] : k2_enumset1(A_65,B_66,B_105,A_106) = k2_enumset1(A_106,B_105,B_66,A_65) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_4,c_4483])).

tff(c_67,plain,(
    ! [B_19,A_20] : k2_xboole_0(k1_tarski(B_19),k1_tarski(A_20)) = k2_tarski(A_20,B_19) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_2])).

tff(c_73,plain,(
    ! [B_19,A_20] : k2_tarski(B_19,A_20) = k2_tarski(A_20,B_19) ),
    inference(superposition,[status(thm),theory(equality)],[c_67,c_6])).

tff(c_1373,plain,(
    ! [A_59,A_60,B_61] : k2_xboole_0(k1_tarski(A_59),k2_tarski(A_60,B_61)) = k1_enumset1(A_59,B_61,A_60) ),
    inference(superposition,[status(thm),theory(equality)],[c_73,c_177])).

tff(c_1403,plain,(
    ! [A_59,B_61,A_60] : k1_enumset1(A_59,B_61,A_60) = k1_enumset1(A_59,A_60,B_61) ),
    inference(superposition,[status(thm),theory(equality)],[c_1373,c_8])).

tff(c_12,plain,(
    k2_xboole_0(k1_tarski('#skF_1'),k1_enumset1('#skF_2','#skF_3','#skF_4')) != k2_enumset1('#skF_1','#skF_2','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_1435,plain,(
    k2_xboole_0(k1_tarski('#skF_1'),k1_enumset1('#skF_2','#skF_4','#skF_3')) != k2_enumset1('#skF_1','#skF_2','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1403,c_12])).

tff(c_1863,plain,(
    k2_xboole_0(k1_tarski('#skF_1'),k1_enumset1('#skF_4','#skF_3','#skF_2')) != k2_enumset1('#skF_1','#skF_2','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1403,c_1622,c_1435])).

tff(c_4835,plain,(
    k2_xboole_0(k1_tarski('#skF_1'),k1_enumset1('#skF_4','#skF_3','#skF_2')) != k2_enumset1('#skF_4','#skF_3','#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4591,c_1863])).

tff(c_7135,plain,(
    k2_enumset1('#skF_1','#skF_4','#skF_3','#skF_2') != k2_enumset1('#skF_4','#skF_3','#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1621,c_4835])).

tff(c_7136,plain,(
    k2_enumset1('#skF_4','#skF_3','#skF_2','#skF_1') != k2_enumset1('#skF_4','#skF_1','#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2849,c_7135])).

tff(c_7833,plain,(
    k2_enumset1('#skF_4','#skF_3','#skF_1','#skF_2') != k2_enumset1('#skF_4','#skF_1','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7618,c_7618,c_7136])).

tff(c_22070,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_21234,c_7833])).

%------------------------------------------------------------------------------

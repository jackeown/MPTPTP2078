%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0130+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:35:46 EST 2020

% Result     : Theorem 10.08s
% Output     : CNFRefutation 10.08s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 281 expanded)
%              Number of leaves         :   18 ( 105 expanded)
%              Depth                    :   11
%              Number of atoms          :   52 ( 269 expanded)
%              Number of equality atoms :   51 ( 268 expanded)
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l53_enumset1)).

tff(f_26,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_30,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_xboole_0(k1_tarski(A),k1_tarski(B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).

tff(f_32,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k2_xboole_0(k2_tarski(A,B),k1_tarski(C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_enumset1)).

tff(f_34,axiom,(
    ! [A,B,C] : k2_xboole_0(k2_xboole_0(A,B),C) = k2_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).

tff(f_37,negated_conjecture,(
    ~ ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k1_enumset1(A,B,C),k1_tarski(D)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_enumset1)).

tff(c_4,plain,(
    ! [A_3,B_4,C_5,D_6] : k2_xboole_0(k2_tarski(A_3,B_4),k2_tarski(C_5,D_6)) = k2_enumset1(A_3,B_4,C_5,D_6) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_399,plain,(
    ! [A_35,B_36,C_37,D_38] : k2_xboole_0(k2_tarski(A_35,B_36),k2_tarski(C_37,D_38)) = k2_enumset1(A_35,B_36,C_37,D_38) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_1267,plain,(
    ! [C_51,D_52,A_53,B_54] : k2_xboole_0(k2_tarski(C_51,D_52),k2_tarski(A_53,B_54)) = k2_enumset1(A_53,B_54,C_51,D_52) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_399])).

tff(c_1312,plain,(
    ! [C_5,D_6,A_3,B_4] : k2_enumset1(C_5,D_6,A_3,B_4) = k2_enumset1(A_3,B_4,C_5,D_6) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_1267])).

tff(c_47,plain,(
    ! [A_17,B_18] : k2_xboole_0(k1_tarski(A_17),k1_tarski(B_18)) = k2_tarski(A_17,B_18) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_53,plain,(
    ! [B_18,A_17] : k2_xboole_0(k1_tarski(B_18),k1_tarski(A_17)) = k2_tarski(A_17,B_18) ),
    inference(superposition,[status(thm),theory(equality)],[c_47,c_2])).

tff(c_178,plain,(
    ! [A_26,B_27,C_28] : k2_xboole_0(k2_tarski(A_26,B_27),k1_tarski(C_28)) = k1_enumset1(A_26,B_27,C_28) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_10,plain,(
    ! [A_12,B_13,C_14] : k2_xboole_0(k2_xboole_0(A_12,B_13),C_14) = k2_xboole_0(A_12,k2_xboole_0(B_13,C_14)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_2850,plain,(
    ! [A_86,B_87,C_88,C_89] : k2_xboole_0(k2_tarski(A_86,B_87),k2_xboole_0(k1_tarski(C_88),C_89)) = k2_xboole_0(k1_enumset1(A_86,B_87,C_88),C_89) ),
    inference(superposition,[status(thm),theory(equality)],[c_178,c_10])).

tff(c_3012,plain,(
    ! [A_86,B_87,B_18,A_17] : k2_xboole_0(k1_enumset1(A_86,B_87,B_18),k1_tarski(A_17)) = k2_xboole_0(k2_tarski(A_86,B_87),k2_tarski(A_17,B_18)) ),
    inference(superposition,[status(thm),theory(equality)],[c_53,c_2850])).

tff(c_3046,plain,(
    ! [A_86,B_87,B_18,A_17] : k2_xboole_0(k1_enumset1(A_86,B_87,B_18),k1_tarski(A_17)) = k2_enumset1(A_86,B_87,A_17,B_18) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_3012])).

tff(c_8,plain,(
    ! [A_9,B_10,C_11] : k2_xboole_0(k2_tarski(A_9,B_10),k1_tarski(C_11)) = k1_enumset1(A_9,B_10,C_11) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_6,plain,(
    ! [A_7,B_8] : k2_xboole_0(k1_tarski(A_7),k1_tarski(B_8)) = k2_tarski(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_132,plain,(
    ! [A_23,B_24,C_25] : k2_xboole_0(k2_xboole_0(A_23,B_24),C_25) = k2_xboole_0(A_23,k2_xboole_0(B_24,C_25)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_441,plain,(
    ! [B_39,A_40,C_41] : k2_xboole_0(k2_xboole_0(B_39,A_40),C_41) = k2_xboole_0(A_40,k2_xboole_0(B_39,C_41)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_132])).

tff(c_521,plain,(
    ! [B_2,B_39,A_40] : k2_xboole_0(B_2,k2_xboole_0(B_39,A_40)) = k2_xboole_0(A_40,k2_xboole_0(B_39,B_2)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_441])).

tff(c_1470,plain,(
    ! [A_65,B_66,C_67] : k2_xboole_0(k1_tarski(A_65),k2_xboole_0(k1_tarski(B_66),C_67)) = k2_xboole_0(k2_tarski(A_65,B_66),C_67) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_132])).

tff(c_1549,plain,(
    ! [A_40,B_66,A_65] : k2_xboole_0(A_40,k2_xboole_0(k1_tarski(B_66),k1_tarski(A_65))) = k2_xboole_0(k2_tarski(A_65,B_66),A_40) ),
    inference(superposition,[status(thm),theory(equality)],[c_521,c_1470])).

tff(c_1615,plain,(
    ! [A_65,B_66,A_40] : k2_xboole_0(k2_tarski(A_65,B_66),A_40) = k2_xboole_0(A_40,k2_tarski(B_66,A_65)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_1549])).

tff(c_5209,plain,(
    ! [B_118,C_119,A_120] : k2_xboole_0(k2_xboole_0(k1_tarski(B_118),C_119),k1_tarski(A_120)) = k2_xboole_0(k2_tarski(A_120,B_118),C_119) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_1470])).

tff(c_5315,plain,(
    ! [A_65,B_66,B_118,A_120] : k2_xboole_0(k2_xboole_0(k2_tarski(A_65,B_66),k1_tarski(B_118)),k1_tarski(A_120)) = k2_xboole_0(k2_tarski(A_120,B_118),k2_tarski(B_66,A_65)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1615,c_5209])).

tff(c_5417,plain,(
    ! [A_123,B_124,B_122,A_121] : k2_enumset1(A_123,B_124,B_122,A_121) = k2_enumset1(A_121,B_122,A_123,B_124) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3046,c_4,c_8,c_5315])).

tff(c_5489,plain,(
    ! [A_3,B_4,D_6,C_5] : k2_enumset1(A_3,B_4,D_6,C_5) = k2_enumset1(A_3,B_4,C_5,D_6) ),
    inference(superposition,[status(thm),theory(equality)],[c_1312,c_5417])).

tff(c_205,plain,(
    ! [C_28,A_26,B_27] : k2_xboole_0(k1_tarski(C_28),k2_tarski(A_26,B_27)) = k1_enumset1(A_26,B_27,C_28) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_178])).

tff(c_1587,plain,(
    ! [A_65,B_18,A_17] : k2_xboole_0(k2_tarski(A_65,B_18),k1_tarski(A_17)) = k2_xboole_0(k1_tarski(A_65),k2_tarski(A_17,B_18)) ),
    inference(superposition,[status(thm),theory(equality)],[c_53,c_1470])).

tff(c_1618,plain,(
    ! [A_65,B_18,A_17] : k1_enumset1(A_65,B_18,A_17) = k1_enumset1(A_17,B_18,A_65) ),
    inference(demodulation,[status(thm),theory(equality)],[c_205,c_8,c_1587])).

tff(c_3268,plain,(
    ! [A_95,B_96,B_97,A_98] : k2_xboole_0(k1_enumset1(A_95,B_96,B_97),k1_tarski(A_98)) = k2_enumset1(A_95,B_96,A_98,B_97) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_3012])).

tff(c_8198,plain,(
    ! [A_170,B_171,A_172,A_173] : k2_xboole_0(k1_enumset1(A_170,B_171,A_172),k1_tarski(A_173)) = k2_enumset1(A_172,B_171,A_173,A_170) ),
    inference(superposition,[status(thm),theory(equality)],[c_1618,c_3268])).

tff(c_3015,plain,(
    ! [A_86,B_87,A_7,B_8] : k2_xboole_0(k1_enumset1(A_86,B_87,A_7),k1_tarski(B_8)) = k2_xboole_0(k2_tarski(A_86,B_87),k2_tarski(A_7,B_8)) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_2850])).

tff(c_3047,plain,(
    ! [A_86,B_87,A_7,B_8] : k2_xboole_0(k1_enumset1(A_86,B_87,A_7),k1_tarski(B_8)) = k2_enumset1(A_86,B_87,A_7,B_8) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_3015])).

tff(c_8315,plain,(
    ! [A_177,B_175,A_174,A_176] : k2_enumset1(A_177,B_175,A_174,A_176) = k2_enumset1(A_174,B_175,A_176,A_177) ),
    inference(superposition,[status(thm),theory(equality)],[c_8198,c_3047])).

tff(c_8399,plain,(
    ! [A_174,B_175,A_176,A_177] : k2_enumset1(A_174,B_175,A_176,A_177) = k2_enumset1(A_174,A_176,A_177,B_175) ),
    inference(superposition,[status(thm),theory(equality)],[c_8315,c_1312])).

tff(c_1568,plain,(
    ! [A_65,C_28,A_26,B_27] : k2_xboole_0(k2_tarski(A_65,C_28),k2_tarski(A_26,B_27)) = k2_xboole_0(k1_tarski(A_65),k1_enumset1(A_26,B_27,C_28)) ),
    inference(superposition,[status(thm),theory(equality)],[c_205,c_1470])).

tff(c_1616,plain,(
    ! [A_65,A_26,B_27,C_28] : k2_xboole_0(k1_tarski(A_65),k1_enumset1(A_26,B_27,C_28)) = k2_enumset1(A_65,C_28,A_26,B_27) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_1568])).

tff(c_5405,plain,(
    ! [A_65,B_66,A_120,B_118] : k2_enumset1(A_65,B_66,A_120,B_118) = k2_enumset1(A_120,B_118,B_66,A_65) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3046,c_4,c_8,c_5315])).

tff(c_1590,plain,(
    ! [A_65,A_7,B_8] : k2_xboole_0(k2_tarski(A_65,A_7),k1_tarski(B_8)) = k2_xboole_0(k1_tarski(A_65),k2_tarski(A_7,B_8)) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_1470])).

tff(c_1677,plain,(
    ! [A_73,A_71,B_72] : k1_enumset1(A_73,A_71,B_72) = k1_enumset1(A_71,B_72,A_73) ),
    inference(demodulation,[status(thm),theory(equality)],[c_205,c_8,c_1590])).

tff(c_1692,plain,(
    ! [A_73,B_72,A_71] : k1_enumset1(A_73,B_72,A_71) = k1_enumset1(A_73,A_71,B_72) ),
    inference(superposition,[status(thm),theory(equality)],[c_1677,c_1618])).

tff(c_12,plain,(
    k2_xboole_0(k1_enumset1('#skF_1','#skF_2','#skF_3'),k1_tarski('#skF_4')) != k2_enumset1('#skF_1','#skF_2','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_13,plain,(
    k2_xboole_0(k1_tarski('#skF_4'),k1_enumset1('#skF_1','#skF_2','#skF_3')) != k2_enumset1('#skF_1','#skF_2','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_12])).

tff(c_1754,plain,(
    k2_xboole_0(k1_tarski('#skF_4'),k1_enumset1('#skF_1','#skF_3','#skF_2')) != k2_enumset1('#skF_1','#skF_2','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1692,c_13])).

tff(c_5416,plain,(
    k2_xboole_0(k1_tarski('#skF_4'),k1_enumset1('#skF_1','#skF_3','#skF_2')) != k2_enumset1('#skF_4','#skF_3','#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5405,c_1754])).

tff(c_6401,plain,(
    k2_enumset1('#skF_4','#skF_2','#skF_1','#skF_3') != k2_enumset1('#skF_4','#skF_3','#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1616,c_5416])).

tff(c_11421,plain,(
    k2_enumset1('#skF_4','#skF_1','#skF_2','#skF_3') != k2_enumset1('#skF_4','#skF_1','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8399,c_8399,c_6401])).

tff(c_11424,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5489,c_11421])).

%------------------------------------------------------------------------------

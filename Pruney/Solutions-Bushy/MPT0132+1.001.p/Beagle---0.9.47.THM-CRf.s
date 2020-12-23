%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0132+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:35:46 EST 2020

% Result     : Theorem 5.06s
% Output     : CNFRefutation 5.06s
% Verified   : 
% Statistics : Number of formulae       :   44 (  81 expanded)
%              Number of leaves         :   19 (  36 expanded)
%              Depth                    :    8
%              Number of atoms          :   31 (  68 expanded)
%              Number of equality atoms :   30 (  67 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k3_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

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
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_28,axiom,(
    ! [A,B,C,D,E] : k3_enumset1(A,B,C,D,E) = k2_xboole_0(k1_enumset1(A,B,C),k2_tarski(D,E)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l57_enumset1)).

tff(f_30,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k2_xboole_0(k1_tarski(A),k2_tarski(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_enumset1)).

tff(f_32,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k2_xboole_0(k2_tarski(A,B),k1_tarski(C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_enumset1)).

tff(f_34,axiom,(
    ! [A,B,C] : k2_xboole_0(k2_xboole_0(A,B),C) = k2_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).

tff(f_37,negated_conjecture,(
    ~ ! [A,B,C,D,E] : k3_enumset1(A,B,C,D,E) = k2_xboole_0(k2_tarski(A,B),k1_enumset1(C,D,E)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_enumset1)).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_tarski(B_2,A_1) = k2_tarski(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_184,plain,(
    ! [E_37,D_38,A_39,C_40,B_41] : k2_xboole_0(k1_enumset1(A_39,B_41,C_40),k2_tarski(D_38,E_37)) = k3_enumset1(A_39,B_41,C_40,D_38,E_37) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_468,plain,(
    ! [B_53,C_52,A_51,B_55,A_54] : k2_xboole_0(k1_enumset1(A_51,B_55,C_52),k2_tarski(B_53,A_54)) = k3_enumset1(A_51,B_55,C_52,A_54,B_53) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_184])).

tff(c_4,plain,(
    ! [A_3,D_6,C_5,E_7,B_4] : k2_xboole_0(k1_enumset1(A_3,B_4,C_5),k2_tarski(D_6,E_7)) = k3_enumset1(A_3,B_4,C_5,D_6,E_7) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_474,plain,(
    ! [B_53,C_52,A_51,B_55,A_54] : k3_enumset1(A_51,B_55,C_52,B_53,A_54) = k3_enumset1(A_51,B_55,C_52,A_54,B_53) ),
    inference(superposition,[status(thm),theory(equality)],[c_468,c_4])).

tff(c_6,plain,(
    ! [A_8,B_9,C_10] : k2_xboole_0(k1_tarski(A_8),k2_tarski(B_9,C_10)) = k1_enumset1(A_8,B_9,C_10) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_8,plain,(
    ! [A_11,B_12,C_13] : k2_xboole_0(k2_tarski(A_11,B_12),k1_tarski(C_13)) = k1_enumset1(A_11,B_12,C_13) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_76,plain,(
    ! [A_25,B_26,C_27] : k2_xboole_0(k2_xboole_0(A_25,B_26),C_27) = k2_xboole_0(A_25,k2_xboole_0(B_26,C_27)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_552,plain,(
    ! [A_61,B_62,C_63,C_64] : k2_xboole_0(k2_tarski(A_61,B_62),k2_xboole_0(k1_tarski(C_63),C_64)) = k2_xboole_0(k1_enumset1(A_61,B_62,C_63),C_64) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_76])).

tff(c_567,plain,(
    ! [A_61,B_62,A_8,C_10,B_9] : k2_xboole_0(k1_enumset1(A_61,B_62,A_8),k2_tarski(B_9,C_10)) = k2_xboole_0(k2_tarski(A_61,B_62),k1_enumset1(A_8,B_9,C_10)) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_552])).

tff(c_578,plain,(
    ! [A_61,B_62,A_8,C_10,B_9] : k2_xboole_0(k2_tarski(A_61,B_62),k1_enumset1(A_8,B_9,C_10)) = k3_enumset1(A_61,B_62,A_8,B_9,C_10) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_567])).

tff(c_46,plain,(
    ! [A_19,B_20,C_21] : k2_xboole_0(k2_tarski(A_19,B_20),k1_tarski(C_21)) = k1_enumset1(A_19,B_20,C_21) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_158,plain,(
    ! [B_34,A_35,C_36] : k2_xboole_0(k2_tarski(B_34,A_35),k1_tarski(C_36)) = k1_enumset1(A_35,B_34,C_36) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_46])).

tff(c_167,plain,(
    ! [B_34,A_35,C_36] : k1_enumset1(B_34,A_35,C_36) = k1_enumset1(A_35,B_34,C_36) ),
    inference(superposition,[status(thm),theory(equality)],[c_158,c_8])).

tff(c_61,plain,(
    ! [A_22,B_23,C_24] : k2_xboole_0(k1_tarski(A_22),k2_tarski(B_23,C_24)) = k1_enumset1(A_22,B_23,C_24) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_73,plain,(
    ! [A_22,A_1,B_2] : k2_xboole_0(k1_tarski(A_22),k2_tarski(A_1,B_2)) = k1_enumset1(A_22,B_2,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_61])).

tff(c_564,plain,(
    ! [A_61,B_62,B_2,A_1,A_22] : k2_xboole_0(k1_enumset1(A_61,B_62,A_22),k2_tarski(A_1,B_2)) = k2_xboole_0(k2_tarski(A_61,B_62),k1_enumset1(A_22,B_2,A_1)) ),
    inference(superposition,[status(thm),theory(equality)],[c_73,c_552])).

tff(c_1988,plain,(
    ! [B_133,A_132,A_136,B_134,A_135] : k2_xboole_0(k2_tarski(A_135,B_133),k1_enumset1(A_132,B_134,A_136)) = k3_enumset1(A_135,B_133,A_132,A_136,B_134) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_564])).

tff(c_2362,plain,(
    ! [A_152,B_155,A_154,C_156,B_153] : k2_xboole_0(k2_tarski(A_154,B_153),k1_enumset1(A_152,B_155,C_156)) = k3_enumset1(A_154,B_153,B_155,C_156,A_152) ),
    inference(superposition,[status(thm),theory(equality)],[c_167,c_1988])).

tff(c_2404,plain,(
    ! [A_61,B_62,A_8,C_10,B_9] : k3_enumset1(A_61,B_62,B_9,C_10,A_8) = k3_enumset1(A_61,B_62,A_8,B_9,C_10) ),
    inference(superposition,[status(thm),theory(equality)],[c_578,c_2362])).

tff(c_12,plain,(
    k2_xboole_0(k2_tarski('#skF_1','#skF_2'),k1_enumset1('#skF_3','#skF_4','#skF_5')) != k3_enumset1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_208,plain,(
    k2_xboole_0(k2_tarski('#skF_1','#skF_2'),k1_enumset1('#skF_4','#skF_3','#skF_5')) != k3_enumset1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_167,c_12])).

tff(c_1518,plain,(
    k3_enumset1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5') != k3_enumset1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_578,c_208])).

tff(c_2808,plain,(
    k3_enumset1('#skF_1','#skF_2','#skF_4','#skF_5','#skF_3') != k3_enumset1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2404,c_1518])).

tff(c_2811,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_474,c_2808])).

%------------------------------------------------------------------------------

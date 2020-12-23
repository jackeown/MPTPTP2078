%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0128+1.001 : TPTP v7.4.0. Released v7.4.0.
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

% Result     : Theorem 3.32s
% Output     : CNFRefutation 3.32s
% Verified   : 
% Statistics : Number of formulae       :   55 ( 216 expanded)
%              Number of leaves         :   18 (  81 expanded)
%              Depth                    :   12
%              Number of atoms          :   43 ( 204 expanded)
%              Number of equality atoms :   42 ( 203 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    4 (   2 average)

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

tff(f_26,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

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

tff(f_37,negated_conjecture,(
    ~ ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k1_tarski(A),k1_enumset1(B,C,D)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_enumset1)).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_tarski(B_2,A_1) = k2_tarski(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_119,plain,(
    ! [A_28,B_29,C_30,D_31] : k2_xboole_0(k2_tarski(A_28,B_29),k2_tarski(C_30,D_31)) = k2_enumset1(A_28,B_29,C_30,D_31) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_243,plain,(
    ! [A_43,B_44,B_45,A_46] : k2_xboole_0(k2_tarski(A_43,B_44),k2_tarski(B_45,A_46)) = k2_enumset1(A_43,B_44,A_46,B_45) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_119])).

tff(c_4,plain,(
    ! [A_3,B_4,C_5,D_6] : k2_xboole_0(k2_tarski(A_3,B_4),k2_tarski(C_5,D_6)) = k2_enumset1(A_3,B_4,C_5,D_6) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_252,plain,(
    ! [A_43,B_44,B_45,A_46] : k2_enumset1(A_43,B_44,B_45,A_46) = k2_enumset1(A_43,B_44,A_46,B_45) ),
    inference(superposition,[status(thm),theory(equality)],[c_243,c_4])).

tff(c_178,plain,(
    ! [A_35,B_36,C_37,D_38] : k2_xboole_0(k2_tarski(A_35,B_36),k2_tarski(C_37,D_38)) = k2_enumset1(B_36,A_35,C_37,D_38) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_119])).

tff(c_184,plain,(
    ! [B_36,A_35,C_37,D_38] : k2_enumset1(B_36,A_35,C_37,D_38) = k2_enumset1(A_35,B_36,C_37,D_38) ),
    inference(superposition,[status(thm),theory(equality)],[c_178,c_4])).

tff(c_8,plain,(
    ! [A_9,B_10,C_11] : k2_xboole_0(k1_tarski(A_9),k2_tarski(B_10,C_11)) = k1_enumset1(A_9,B_10,C_11) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_6,plain,(
    ! [A_7,B_8] : k2_xboole_0(k1_tarski(A_7),k1_tarski(B_8)) = k2_tarski(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_55,plain,(
    ! [A_19,B_20,C_21] : k2_xboole_0(k2_xboole_0(A_19,B_20),C_21) = k2_xboole_0(A_19,k2_xboole_0(B_20,C_21)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_422,plain,(
    ! [A_55,B_56,C_57] : k2_xboole_0(k1_tarski(A_55),k2_xboole_0(k1_tarski(B_56),C_57)) = k2_xboole_0(k2_tarski(A_55,B_56),C_57) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_55])).

tff(c_446,plain,(
    ! [A_55,A_7,B_8] : k2_xboole_0(k2_tarski(A_55,A_7),k1_tarski(B_8)) = k2_xboole_0(k1_tarski(A_55),k2_tarski(A_7,B_8)) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_422])).

tff(c_453,plain,(
    ! [A_58,A_59,B_60] : k2_xboole_0(k2_tarski(A_58,A_59),k1_tarski(B_60)) = k1_enumset1(A_58,A_59,B_60) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_446])).

tff(c_471,plain,(
    ! [B_61,A_62,B_63] : k2_xboole_0(k2_tarski(B_61,A_62),k1_tarski(B_63)) = k1_enumset1(A_62,B_61,B_63) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_453])).

tff(c_452,plain,(
    ! [A_55,A_7,B_8] : k2_xboole_0(k2_tarski(A_55,A_7),k1_tarski(B_8)) = k1_enumset1(A_55,A_7,B_8) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_446])).

tff(c_477,plain,(
    ! [B_61,A_62,B_63] : k1_enumset1(B_61,A_62,B_63) = k1_enumset1(A_62,B_61,B_63) ),
    inference(superposition,[status(thm),theory(equality)],[c_471,c_452])).

tff(c_75,plain,(
    ! [A_22,B_23,C_24] : k2_xboole_0(k1_tarski(A_22),k2_tarski(B_23,C_24)) = k1_enumset1(A_22,B_23,C_24) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_87,plain,(
    ! [A_22,B_2,A_1] : k2_xboole_0(k1_tarski(A_22),k2_tarski(B_2,A_1)) = k1_enumset1(A_22,A_1,B_2) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_75])).

tff(c_440,plain,(
    ! [A_55,A_22,B_2,A_1] : k2_xboole_0(k2_tarski(A_55,A_22),k2_tarski(B_2,A_1)) = k2_xboole_0(k1_tarski(A_55),k1_enumset1(A_22,A_1,B_2)) ),
    inference(superposition,[status(thm),theory(equality)],[c_87,c_422])).

tff(c_866,plain,(
    ! [A_86,A_87,A_88,B_89] : k2_xboole_0(k1_tarski(A_86),k1_enumset1(A_87,A_88,B_89)) = k2_enumset1(A_86,A_87,B_89,A_88) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_440])).

tff(c_970,plain,(
    ! [A_94,A_95,B_96,B_97] : k2_xboole_0(k1_tarski(A_94),k1_enumset1(A_95,B_96,B_97)) = k2_enumset1(A_94,B_96,B_97,A_95) ),
    inference(superposition,[status(thm),theory(equality)],[c_477,c_866])).

tff(c_443,plain,(
    ! [A_55,A_9,B_10,C_11] : k2_xboole_0(k2_tarski(A_55,A_9),k2_tarski(B_10,C_11)) = k2_xboole_0(k1_tarski(A_55),k1_enumset1(A_9,B_10,C_11)) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_422])).

tff(c_451,plain,(
    ! [A_55,A_9,B_10,C_11] : k2_xboole_0(k1_tarski(A_55),k1_enumset1(A_9,B_10,C_11)) = k2_enumset1(A_55,A_9,B_10,C_11) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_443])).

tff(c_979,plain,(
    ! [A_94,B_96,B_97,A_95] : k2_enumset1(A_94,B_96,B_97,A_95) = k2_enumset1(A_94,A_95,B_96,B_97) ),
    inference(superposition,[status(thm),theory(equality)],[c_970,c_451])).

tff(c_450,plain,(
    ! [A_55,A_22,A_1,B_2] : k2_xboole_0(k1_tarski(A_55),k1_enumset1(A_22,A_1,B_2)) = k2_enumset1(A_55,A_22,B_2,A_1) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_440])).

tff(c_976,plain,(
    ! [A_94,B_96,B_97,A_95] : k2_enumset1(A_94,B_96,B_97,A_95) = k2_enumset1(A_94,A_95,B_97,B_96) ),
    inference(superposition,[status(thm),theory(equality)],[c_970,c_450])).

tff(c_93,plain,(
    ! [A_25,B_26,A_27] : k2_xboole_0(k1_tarski(A_25),k2_tarski(B_26,A_27)) = k1_enumset1(A_25,A_27,B_26) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_75])).

tff(c_99,plain,(
    ! [A_25,B_26,A_27] : k1_enumset1(A_25,B_26,A_27) = k1_enumset1(A_25,A_27,B_26) ),
    inference(superposition,[status(thm),theory(equality)],[c_93,c_8])).

tff(c_12,plain,(
    k2_xboole_0(k1_tarski('#skF_1'),k1_enumset1('#skF_2','#skF_3','#skF_4')) != k2_enumset1('#skF_1','#skF_2','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_177,plain,(
    k2_xboole_0(k1_tarski('#skF_1'),k1_enumset1('#skF_2','#skF_4','#skF_3')) != k2_enumset1('#skF_1','#skF_2','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_99,c_12])).

tff(c_339,plain,(
    k2_xboole_0(k1_tarski('#skF_1'),k1_enumset1('#skF_2','#skF_4','#skF_3')) != k2_enumset1('#skF_1','#skF_2','#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_252,c_177])).

tff(c_497,plain,(
    k2_xboole_0(k1_tarski('#skF_1'),k1_enumset1('#skF_4','#skF_2','#skF_3')) != k2_enumset1('#skF_1','#skF_2','#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_477,c_339])).

tff(c_498,plain,(
    k2_xboole_0(k1_tarski('#skF_1'),k1_enumset1('#skF_4','#skF_3','#skF_2')) != k2_enumset1('#skF_1','#skF_2','#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_99,c_497])).

tff(c_825,plain,(
    k2_enumset1('#skF_1','#skF_2','#skF_4','#skF_3') != k2_enumset1('#skF_1','#skF_4','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_451,c_498])).

tff(c_826,plain,(
    k2_enumset1('#skF_1','#skF_2','#skF_4','#skF_3') != k2_enumset1('#skF_4','#skF_1','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_184,c_825])).

tff(c_1024,plain,(
    k2_enumset1('#skF_1','#skF_3','#skF_4','#skF_2') != k2_enumset1('#skF_4','#skF_1','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_976,c_826])).

tff(c_1310,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_252,c_184,c_979,c_1024])).

%------------------------------------------------------------------------------

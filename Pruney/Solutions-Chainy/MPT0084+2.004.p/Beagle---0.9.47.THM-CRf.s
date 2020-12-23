%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:44:05 EST 2020

% Result     : Theorem 5.08s
% Output     : CNFRefutation 5.08s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 308 expanded)
%              Number of leaves         :   23 ( 112 expanded)
%              Depth                    :   20
%              Number of atoms          :   77 ( 316 expanded)
%              Number of equality atoms :   62 ( 277 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

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

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_60,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( ~ r1_xboole_0(A,B)
          & r1_tarski(A,C)
          & r1_xboole_0(A,k3_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_xboole_1)).

tff(f_43,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_45,axiom,(
    ! [A,B,C] : k4_xboole_0(k4_xboole_0(A,B),C) = k4_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

tff(f_39,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_47,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_49,axiom,(
    ! [A,B,C] : k3_xboole_0(A,k4_xboole_0(B,C)) = k4_xboole_0(k3_xboole_0(A,B),C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).

tff(f_37,axiom,(
    ! [A,B,C] : k3_xboole_0(k3_xboole_0(A,B),C) = k3_xboole_0(A,k3_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_51,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(c_168,plain,(
    ! [A_42,B_43] :
      ( r1_xboole_0(A_42,B_43)
      | k3_xboole_0(A_42,B_43) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_32,plain,(
    ~ r1_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_176,plain,(
    k3_xboole_0('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_168,c_32])).

tff(c_18,plain,(
    ! [A_13] : k4_xboole_0(A_13,k1_xboole_0) = A_13 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_780,plain,(
    ! [A_62,B_63,C_64] : k4_xboole_0(k4_xboole_0(A_62,B_63),C_64) = k4_xboole_0(A_62,k2_xboole_0(B_63,C_64)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_864,plain,(
    ! [A_13,C_64] : k4_xboole_0(A_13,k2_xboole_0(k1_xboole_0,C_64)) = k4_xboole_0(A_13,C_64) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_780])).

tff(c_14,plain,(
    ! [A_10] : k3_xboole_0(A_10,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_247,plain,(
    ! [A_46,B_47] : k4_xboole_0(A_46,k4_xboole_0(A_46,B_47)) = k3_xboole_0(A_46,B_47) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_277,plain,(
    ! [A_13] : k4_xboole_0(A_13,A_13) = k3_xboole_0(A_13,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_247])).

tff(c_285,plain,(
    ! [A_13] : k4_xboole_0(A_13,A_13) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_277])).

tff(c_24,plain,(
    ! [A_19,B_20,C_21] : k4_xboole_0(k3_xboole_0(A_19,B_20),C_21) = k3_xboole_0(A_19,k4_xboole_0(B_20,C_21)) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_22,plain,(
    ! [A_17,B_18] : k4_xboole_0(A_17,k4_xboole_0(A_17,B_18)) = k3_xboole_0(A_17,B_18) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_837,plain,(
    ! [A_17,B_18,C_64] : k4_xboole_0(A_17,k2_xboole_0(k4_xboole_0(A_17,B_18),C_64)) = k4_xboole_0(k3_xboole_0(A_17,B_18),C_64) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_780])).

tff(c_3763,plain,(
    ! [A_112,B_113,C_114] : k4_xboole_0(A_112,k2_xboole_0(k4_xboole_0(A_112,B_113),C_114)) = k3_xboole_0(A_112,k4_xboole_0(B_113,C_114)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_837])).

tff(c_3918,plain,(
    ! [A_13,C_114] : k4_xboole_0(A_13,k2_xboole_0(k1_xboole_0,C_114)) = k3_xboole_0(A_13,k4_xboole_0(A_13,C_114)) ),
    inference(superposition,[status(thm),theory(equality)],[c_285,c_3763])).

tff(c_3987,plain,(
    ! [A_13,C_114] : k3_xboole_0(A_13,k4_xboole_0(A_13,C_114)) = k4_xboole_0(A_13,C_114) ),
    inference(demodulation,[status(thm),theory(equality)],[c_864,c_3918])).

tff(c_259,plain,(
    ! [A_17,B_18] : k4_xboole_0(A_17,k3_xboole_0(A_17,B_18)) = k3_xboole_0(A_17,k4_xboole_0(A_17,B_18)) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_247])).

tff(c_4229,plain,(
    ! [A_17,B_18] : k4_xboole_0(A_17,k3_xboole_0(A_17,B_18)) = k4_xboole_0(A_17,B_18) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3987,c_259])).

tff(c_12,plain,(
    ! [A_7,B_8,C_9] : k3_xboole_0(k3_xboole_0(A_7,B_8),C_9) = k3_xboole_0(A_7,k3_xboole_0(B_8,C_9)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_4230,plain,(
    ! [A_118,C_119] : k3_xboole_0(A_118,k4_xboole_0(A_118,C_119)) = k4_xboole_0(A_118,C_119) ),
    inference(demodulation,[status(thm),theory(equality)],[c_864,c_3918])).

tff(c_28,plain,(
    r1_xboole_0('#skF_1',k3_xboole_0('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_99,plain,(
    ! [A_32,B_33] :
      ( k3_xboole_0(A_32,B_33) = k1_xboole_0
      | ~ r1_xboole_0(A_32,B_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_103,plain,(
    k3_xboole_0('#skF_1',k3_xboole_0('#skF_2','#skF_3')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_28,c_99])).

tff(c_2391,plain,(
    ! [A_95,B_96] : k4_xboole_0(A_95,k3_xboole_0(A_95,B_96)) = k3_xboole_0(A_95,k4_xboole_0(A_95,B_96)) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_247])).

tff(c_2473,plain,(
    k3_xboole_0('#skF_1',k4_xboole_0('#skF_1',k3_xboole_0('#skF_2','#skF_3'))) = k4_xboole_0('#skF_1',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_103,c_2391])).

tff(c_2499,plain,(
    k3_xboole_0('#skF_1',k4_xboole_0('#skF_1',k3_xboole_0('#skF_2','#skF_3'))) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_2473])).

tff(c_4258,plain,(
    k4_xboole_0('#skF_1',k3_xboole_0('#skF_2','#skF_3')) = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_4230,c_2499])).

tff(c_50,plain,(
    ! [B_28,A_29] : k2_xboole_0(B_28,A_29) = k2_xboole_0(A_29,B_28) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_26,plain,(
    ! [A_22,B_23] : r1_tarski(A_22,k2_xboole_0(A_22,B_23)) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_65,plain,(
    ! [A_29,B_28] : r1_tarski(A_29,k2_xboole_0(B_28,A_29)) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_26])).

tff(c_108,plain,(
    ! [A_34,B_35] :
      ( k4_xboole_0(A_34,B_35) = k1_xboole_0
      | ~ r1_tarski(A_34,B_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_118,plain,(
    ! [A_29,B_28] : k4_xboole_0(A_29,k2_xboole_0(B_28,A_29)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_65,c_108])).

tff(c_3823,plain,(
    ! [C_114,B_113] : k3_xboole_0(C_114,k4_xboole_0(B_113,C_114)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_3763,c_118])).

tff(c_4420,plain,(
    k3_xboole_0(k3_xboole_0('#skF_2','#skF_3'),'#skF_1') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_4258,c_3823])).

tff(c_515,plain,(
    ! [A_55,B_56,C_57] : k4_xboole_0(k3_xboole_0(A_55,B_56),C_57) = k3_xboole_0(A_55,k4_xboole_0(B_56,C_57)) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_563,plain,(
    ! [A_55,B_56] : k3_xboole_0(A_55,k4_xboole_0(B_56,k3_xboole_0(A_55,B_56))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_285,c_515])).

tff(c_4672,plain,(
    k3_xboole_0(k3_xboole_0('#skF_2','#skF_3'),k4_xboole_0('#skF_1',k1_xboole_0)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_4420,c_563])).

tff(c_4688,plain,(
    k3_xboole_0('#skF_2',k3_xboole_0('#skF_3','#skF_1')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_18,c_4672])).

tff(c_4717,plain,(
    ! [A_123,B_124] : k4_xboole_0(A_123,k3_xboole_0(A_123,B_124)) = k4_xboole_0(A_123,B_124) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3987,c_259])).

tff(c_4777,plain,(
    k4_xboole_0('#skF_2',k3_xboole_0('#skF_3','#skF_1')) = k4_xboole_0('#skF_2',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_4688,c_4717])).

tff(c_4871,plain,(
    k4_xboole_0('#skF_2',k3_xboole_0('#skF_3','#skF_1')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_4777])).

tff(c_5639,plain,(
    k3_xboole_0(k3_xboole_0('#skF_3','#skF_1'),'#skF_2') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_4871,c_3823])).

tff(c_5766,plain,(
    k3_xboole_0(k3_xboole_0('#skF_3','#skF_1'),k4_xboole_0('#skF_2',k1_xboole_0)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_5639,c_563])).

tff(c_5783,plain,(
    k3_xboole_0('#skF_3',k3_xboole_0('#skF_1','#skF_2')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_18,c_5766])).

tff(c_30,plain,(
    r1_tarski('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_120,plain,(
    k4_xboole_0('#skF_1','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_30,c_108])).

tff(c_274,plain,(
    k4_xboole_0('#skF_1',k1_xboole_0) = k3_xboole_0('#skF_1','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_120,c_247])).

tff(c_284,plain,(
    k3_xboole_0('#skF_1','#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_274])).

tff(c_1150,plain,(
    ! [A_70,B_71,C_72] : k3_xboole_0(k3_xboole_0(A_70,B_71),C_72) = k3_xboole_0(A_70,k3_xboole_0(B_71,C_72)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_1211,plain,(
    ! [C_72] : k3_xboole_0('#skF_1',k3_xboole_0('#skF_3',C_72)) = k3_xboole_0('#skF_1',C_72) ),
    inference(superposition,[status(thm),theory(equality)],[c_284,c_1150])).

tff(c_5799,plain,(
    k3_xboole_0('#skF_1',k3_xboole_0('#skF_1','#skF_2')) = k3_xboole_0('#skF_1',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_5783,c_1211])).

tff(c_5812,plain,(
    k3_xboole_0('#skF_1',k3_xboole_0('#skF_1','#skF_2')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_5799])).

tff(c_6148,plain,(
    k4_xboole_0('#skF_1',k3_xboole_0('#skF_1','#skF_2')) = k4_xboole_0('#skF_1',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_5812,c_4229])).

tff(c_6163,plain,(
    k4_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4229,c_18,c_6148])).

tff(c_4789,plain,(
    ! [C_114,B_113] : k4_xboole_0(C_114,k4_xboole_0(B_113,C_114)) = k4_xboole_0(C_114,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_3823,c_4717])).

tff(c_4897,plain,(
    ! [C_125,B_126] : k4_xboole_0(C_125,k4_xboole_0(B_126,C_125)) = C_125 ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_4789])).

tff(c_4909,plain,(
    ! [B_126,C_125] : k3_xboole_0(k4_xboole_0(B_126,C_125),C_125) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_4897,c_3823])).

tff(c_6178,plain,(
    k3_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_6163,c_4909])).

tff(c_6214,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_176,c_6178])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n009.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 16:56:41 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.08/2.15  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.08/2.15  
% 5.08/2.15  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.08/2.15  %$ r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 5.08/2.15  
% 5.08/2.15  %Foreground sorts:
% 5.08/2.15  
% 5.08/2.15  
% 5.08/2.15  %Background operators:
% 5.08/2.15  
% 5.08/2.15  
% 5.08/2.15  %Foreground operators:
% 5.08/2.15  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.08/2.15  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 5.08/2.15  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.08/2.15  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.08/2.15  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 5.08/2.15  tff('#skF_2', type, '#skF_2': $i).
% 5.08/2.15  tff('#skF_3', type, '#skF_3': $i).
% 5.08/2.15  tff('#skF_1', type, '#skF_1': $i).
% 5.08/2.15  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.08/2.15  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.08/2.15  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.08/2.15  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 5.08/2.15  
% 5.08/2.17  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 5.08/2.17  tff(f_60, negated_conjecture, ~(![A, B, C]: ~((~r1_xboole_0(A, B) & r1_tarski(A, C)) & r1_xboole_0(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t77_xboole_1)).
% 5.08/2.17  tff(f_43, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 5.08/2.17  tff(f_45, axiom, (![A, B, C]: (k4_xboole_0(k4_xboole_0(A, B), C) = k4_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_xboole_1)).
% 5.08/2.17  tff(f_39, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 5.08/2.17  tff(f_47, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 5.08/2.17  tff(f_49, axiom, (![A, B, C]: (k3_xboole_0(A, k4_xboole_0(B, C)) = k4_xboole_0(k3_xboole_0(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_xboole_1)).
% 5.08/2.17  tff(f_37, axiom, (![A, B, C]: (k3_xboole_0(k3_xboole_0(A, B), C) = k3_xboole_0(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_xboole_1)).
% 5.08/2.17  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 5.08/2.17  tff(f_51, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 5.08/2.17  tff(f_35, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 5.08/2.17  tff(c_168, plain, (![A_42, B_43]: (r1_xboole_0(A_42, B_43) | k3_xboole_0(A_42, B_43)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.08/2.17  tff(c_32, plain, (~r1_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_60])).
% 5.08/2.17  tff(c_176, plain, (k3_xboole_0('#skF_1', '#skF_2')!=k1_xboole_0), inference(resolution, [status(thm)], [c_168, c_32])).
% 5.08/2.17  tff(c_18, plain, (![A_13]: (k4_xboole_0(A_13, k1_xboole_0)=A_13)), inference(cnfTransformation, [status(thm)], [f_43])).
% 5.08/2.17  tff(c_780, plain, (![A_62, B_63, C_64]: (k4_xboole_0(k4_xboole_0(A_62, B_63), C_64)=k4_xboole_0(A_62, k2_xboole_0(B_63, C_64)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 5.08/2.17  tff(c_864, plain, (![A_13, C_64]: (k4_xboole_0(A_13, k2_xboole_0(k1_xboole_0, C_64))=k4_xboole_0(A_13, C_64))), inference(superposition, [status(thm), theory('equality')], [c_18, c_780])).
% 5.08/2.17  tff(c_14, plain, (![A_10]: (k3_xboole_0(A_10, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 5.08/2.17  tff(c_247, plain, (![A_46, B_47]: (k4_xboole_0(A_46, k4_xboole_0(A_46, B_47))=k3_xboole_0(A_46, B_47))), inference(cnfTransformation, [status(thm)], [f_47])).
% 5.08/2.17  tff(c_277, plain, (![A_13]: (k4_xboole_0(A_13, A_13)=k3_xboole_0(A_13, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_18, c_247])).
% 5.08/2.17  tff(c_285, plain, (![A_13]: (k4_xboole_0(A_13, A_13)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_277])).
% 5.08/2.17  tff(c_24, plain, (![A_19, B_20, C_21]: (k4_xboole_0(k3_xboole_0(A_19, B_20), C_21)=k3_xboole_0(A_19, k4_xboole_0(B_20, C_21)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 5.08/2.17  tff(c_22, plain, (![A_17, B_18]: (k4_xboole_0(A_17, k4_xboole_0(A_17, B_18))=k3_xboole_0(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_47])).
% 5.08/2.17  tff(c_837, plain, (![A_17, B_18, C_64]: (k4_xboole_0(A_17, k2_xboole_0(k4_xboole_0(A_17, B_18), C_64))=k4_xboole_0(k3_xboole_0(A_17, B_18), C_64))), inference(superposition, [status(thm), theory('equality')], [c_22, c_780])).
% 5.08/2.17  tff(c_3763, plain, (![A_112, B_113, C_114]: (k4_xboole_0(A_112, k2_xboole_0(k4_xboole_0(A_112, B_113), C_114))=k3_xboole_0(A_112, k4_xboole_0(B_113, C_114)))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_837])).
% 5.08/2.17  tff(c_3918, plain, (![A_13, C_114]: (k4_xboole_0(A_13, k2_xboole_0(k1_xboole_0, C_114))=k3_xboole_0(A_13, k4_xboole_0(A_13, C_114)))), inference(superposition, [status(thm), theory('equality')], [c_285, c_3763])).
% 5.08/2.17  tff(c_3987, plain, (![A_13, C_114]: (k3_xboole_0(A_13, k4_xboole_0(A_13, C_114))=k4_xboole_0(A_13, C_114))), inference(demodulation, [status(thm), theory('equality')], [c_864, c_3918])).
% 5.08/2.17  tff(c_259, plain, (![A_17, B_18]: (k4_xboole_0(A_17, k3_xboole_0(A_17, B_18))=k3_xboole_0(A_17, k4_xboole_0(A_17, B_18)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_247])).
% 5.08/2.17  tff(c_4229, plain, (![A_17, B_18]: (k4_xboole_0(A_17, k3_xboole_0(A_17, B_18))=k4_xboole_0(A_17, B_18))), inference(demodulation, [status(thm), theory('equality')], [c_3987, c_259])).
% 5.08/2.17  tff(c_12, plain, (![A_7, B_8, C_9]: (k3_xboole_0(k3_xboole_0(A_7, B_8), C_9)=k3_xboole_0(A_7, k3_xboole_0(B_8, C_9)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.08/2.17  tff(c_4230, plain, (![A_118, C_119]: (k3_xboole_0(A_118, k4_xboole_0(A_118, C_119))=k4_xboole_0(A_118, C_119))), inference(demodulation, [status(thm), theory('equality')], [c_864, c_3918])).
% 5.08/2.17  tff(c_28, plain, (r1_xboole_0('#skF_1', k3_xboole_0('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_60])).
% 5.08/2.17  tff(c_99, plain, (![A_32, B_33]: (k3_xboole_0(A_32, B_33)=k1_xboole_0 | ~r1_xboole_0(A_32, B_33))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.08/2.17  tff(c_103, plain, (k3_xboole_0('#skF_1', k3_xboole_0('#skF_2', '#skF_3'))=k1_xboole_0), inference(resolution, [status(thm)], [c_28, c_99])).
% 5.08/2.17  tff(c_2391, plain, (![A_95, B_96]: (k4_xboole_0(A_95, k3_xboole_0(A_95, B_96))=k3_xboole_0(A_95, k4_xboole_0(A_95, B_96)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_247])).
% 5.08/2.17  tff(c_2473, plain, (k3_xboole_0('#skF_1', k4_xboole_0('#skF_1', k3_xboole_0('#skF_2', '#skF_3')))=k4_xboole_0('#skF_1', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_103, c_2391])).
% 5.08/2.17  tff(c_2499, plain, (k3_xboole_0('#skF_1', k4_xboole_0('#skF_1', k3_xboole_0('#skF_2', '#skF_3')))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_18, c_2473])).
% 5.08/2.17  tff(c_4258, plain, (k4_xboole_0('#skF_1', k3_xboole_0('#skF_2', '#skF_3'))='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_4230, c_2499])).
% 5.08/2.17  tff(c_50, plain, (![B_28, A_29]: (k2_xboole_0(B_28, A_29)=k2_xboole_0(A_29, B_28))), inference(cnfTransformation, [status(thm)], [f_27])).
% 5.08/2.17  tff(c_26, plain, (![A_22, B_23]: (r1_tarski(A_22, k2_xboole_0(A_22, B_23)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 5.08/2.17  tff(c_65, plain, (![A_29, B_28]: (r1_tarski(A_29, k2_xboole_0(B_28, A_29)))), inference(superposition, [status(thm), theory('equality')], [c_50, c_26])).
% 5.08/2.17  tff(c_108, plain, (![A_34, B_35]: (k4_xboole_0(A_34, B_35)=k1_xboole_0 | ~r1_tarski(A_34, B_35))), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.08/2.17  tff(c_118, plain, (![A_29, B_28]: (k4_xboole_0(A_29, k2_xboole_0(B_28, A_29))=k1_xboole_0)), inference(resolution, [status(thm)], [c_65, c_108])).
% 5.08/2.17  tff(c_3823, plain, (![C_114, B_113]: (k3_xboole_0(C_114, k4_xboole_0(B_113, C_114))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_3763, c_118])).
% 5.08/2.17  tff(c_4420, plain, (k3_xboole_0(k3_xboole_0('#skF_2', '#skF_3'), '#skF_1')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_4258, c_3823])).
% 5.08/2.17  tff(c_515, plain, (![A_55, B_56, C_57]: (k4_xboole_0(k3_xboole_0(A_55, B_56), C_57)=k3_xboole_0(A_55, k4_xboole_0(B_56, C_57)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 5.08/2.17  tff(c_563, plain, (![A_55, B_56]: (k3_xboole_0(A_55, k4_xboole_0(B_56, k3_xboole_0(A_55, B_56)))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_285, c_515])).
% 5.08/2.17  tff(c_4672, plain, (k3_xboole_0(k3_xboole_0('#skF_2', '#skF_3'), k4_xboole_0('#skF_1', k1_xboole_0))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_4420, c_563])).
% 5.08/2.17  tff(c_4688, plain, (k3_xboole_0('#skF_2', k3_xboole_0('#skF_3', '#skF_1'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_12, c_18, c_4672])).
% 5.08/2.17  tff(c_4717, plain, (![A_123, B_124]: (k4_xboole_0(A_123, k3_xboole_0(A_123, B_124))=k4_xboole_0(A_123, B_124))), inference(demodulation, [status(thm), theory('equality')], [c_3987, c_259])).
% 5.08/2.17  tff(c_4777, plain, (k4_xboole_0('#skF_2', k3_xboole_0('#skF_3', '#skF_1'))=k4_xboole_0('#skF_2', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_4688, c_4717])).
% 5.08/2.17  tff(c_4871, plain, (k4_xboole_0('#skF_2', k3_xboole_0('#skF_3', '#skF_1'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_18, c_4777])).
% 5.08/2.17  tff(c_5639, plain, (k3_xboole_0(k3_xboole_0('#skF_3', '#skF_1'), '#skF_2')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_4871, c_3823])).
% 5.08/2.17  tff(c_5766, plain, (k3_xboole_0(k3_xboole_0('#skF_3', '#skF_1'), k4_xboole_0('#skF_2', k1_xboole_0))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_5639, c_563])).
% 5.08/2.17  tff(c_5783, plain, (k3_xboole_0('#skF_3', k3_xboole_0('#skF_1', '#skF_2'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_12, c_18, c_5766])).
% 5.08/2.17  tff(c_30, plain, (r1_tarski('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_60])).
% 5.08/2.17  tff(c_120, plain, (k4_xboole_0('#skF_1', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_30, c_108])).
% 5.08/2.17  tff(c_274, plain, (k4_xboole_0('#skF_1', k1_xboole_0)=k3_xboole_0('#skF_1', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_120, c_247])).
% 5.08/2.17  tff(c_284, plain, (k3_xboole_0('#skF_1', '#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_18, c_274])).
% 5.08/2.17  tff(c_1150, plain, (![A_70, B_71, C_72]: (k3_xboole_0(k3_xboole_0(A_70, B_71), C_72)=k3_xboole_0(A_70, k3_xboole_0(B_71, C_72)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.08/2.17  tff(c_1211, plain, (![C_72]: (k3_xboole_0('#skF_1', k3_xboole_0('#skF_3', C_72))=k3_xboole_0('#skF_1', C_72))), inference(superposition, [status(thm), theory('equality')], [c_284, c_1150])).
% 5.08/2.17  tff(c_5799, plain, (k3_xboole_0('#skF_1', k3_xboole_0('#skF_1', '#skF_2'))=k3_xboole_0('#skF_1', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_5783, c_1211])).
% 5.08/2.17  tff(c_5812, plain, (k3_xboole_0('#skF_1', k3_xboole_0('#skF_1', '#skF_2'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_14, c_5799])).
% 5.08/2.17  tff(c_6148, plain, (k4_xboole_0('#skF_1', k3_xboole_0('#skF_1', '#skF_2'))=k4_xboole_0('#skF_1', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_5812, c_4229])).
% 5.08/2.17  tff(c_6163, plain, (k4_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_4229, c_18, c_6148])).
% 5.08/2.17  tff(c_4789, plain, (![C_114, B_113]: (k4_xboole_0(C_114, k4_xboole_0(B_113, C_114))=k4_xboole_0(C_114, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_3823, c_4717])).
% 5.08/2.17  tff(c_4897, plain, (![C_125, B_126]: (k4_xboole_0(C_125, k4_xboole_0(B_126, C_125))=C_125)), inference(demodulation, [status(thm), theory('equality')], [c_18, c_4789])).
% 5.08/2.17  tff(c_4909, plain, (![B_126, C_125]: (k3_xboole_0(k4_xboole_0(B_126, C_125), C_125)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_4897, c_3823])).
% 5.08/2.17  tff(c_6178, plain, (k3_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_6163, c_4909])).
% 5.08/2.17  tff(c_6214, plain, $false, inference(negUnitSimplification, [status(thm)], [c_176, c_6178])).
% 5.08/2.17  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.08/2.17  
% 5.08/2.17  Inference rules
% 5.08/2.17  ----------------------
% 5.08/2.17  #Ref     : 0
% 5.08/2.17  #Sup     : 1532
% 5.08/2.17  #Fact    : 0
% 5.08/2.17  #Define  : 0
% 5.08/2.17  #Split   : 0
% 5.08/2.17  #Chain   : 0
% 5.08/2.17  #Close   : 0
% 5.08/2.17  
% 5.08/2.17  Ordering : KBO
% 5.08/2.17  
% 5.08/2.17  Simplification rules
% 5.08/2.17  ----------------------
% 5.08/2.17  #Subsume      : 19
% 5.08/2.17  #Demod        : 1506
% 5.08/2.17  #Tautology    : 930
% 5.08/2.17  #SimpNegUnit  : 1
% 5.08/2.17  #BackRed      : 5
% 5.08/2.17  
% 5.08/2.17  #Partial instantiations: 0
% 5.08/2.17  #Strategies tried      : 1
% 5.08/2.17  
% 5.08/2.17  Timing (in seconds)
% 5.08/2.17  ----------------------
% 5.08/2.17  Preprocessing        : 0.33
% 5.08/2.17  Parsing              : 0.17
% 5.08/2.17  CNF conversion       : 0.02
% 5.08/2.17  Main loop            : 1.00
% 5.08/2.17  Inferencing          : 0.29
% 5.08/2.17  Reduction            : 0.48
% 5.08/2.17  Demodulation         : 0.41
% 5.08/2.17  BG Simplification    : 0.04
% 5.08/2.17  Subsumption          : 0.14
% 5.08/2.17  Abstraction          : 0.05
% 5.08/2.17  MUC search           : 0.00
% 5.08/2.17  Cooper               : 0.00
% 5.08/2.17  Total                : 1.37
% 5.08/2.17  Index Insertion      : 0.00
% 5.08/2.17  Index Deletion       : 0.00
% 5.08/2.17  Index Matching       : 0.00
% 5.08/2.17  BG Taut test         : 0.00
%------------------------------------------------------------------------------

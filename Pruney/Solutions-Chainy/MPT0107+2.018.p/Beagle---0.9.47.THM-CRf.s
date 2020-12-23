%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:44:55 EST 2020

% Result     : Theorem 12.34s
% Output     : CNFRefutation 12.34s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 122 expanded)
%              Number of leaves         :   24 (  49 expanded)
%              Depth                    :   11
%              Number of atoms          :   63 ( 119 expanded)
%              Number of equality atoms :   56 ( 101 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

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

tff(f_37,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_35,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_41,axiom,(
    ! [A,B,C] : k4_xboole_0(k4_xboole_0(A,B),C) = k4_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_39,axiom,(
    ! [A,B] : k4_xboole_0(k2_xboole_0(A,B),B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).

tff(f_47,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_53,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_51,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_49,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_56,negated_conjecture,(
    ~ ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(c_12,plain,(
    ! [A_9] : k4_xboole_0(A_9,k1_xboole_0) = A_9 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_10,plain,(
    ! [A_7,B_8] : r1_tarski(k4_xboole_0(A_7,B_8),A_7) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_201,plain,(
    ! [A_37,B_38] :
      ( k4_xboole_0(A_37,B_38) = k1_xboole_0
      | ~ r1_tarski(A_37,B_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_209,plain,(
    ! [A_7,B_8] : k4_xboole_0(k4_xboole_0(A_7,B_8),A_7) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_10,c_201])).

tff(c_637,plain,(
    ! [A_60,B_61,C_62] : k4_xboole_0(k4_xboole_0(A_60,B_61),C_62) = k4_xboole_0(A_60,k2_xboole_0(B_61,C_62)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_1097,plain,(
    ! [A_78,B_79] : k4_xboole_0(A_78,k2_xboole_0(B_79,A_78)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_209,c_637])).

tff(c_20,plain,(
    ! [A_17,B_18] : k4_xboole_0(A_17,k4_xboole_0(A_17,B_18)) = k3_xboole_0(A_17,B_18) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_1118,plain,(
    ! [A_78,B_79] : k3_xboole_0(A_78,k2_xboole_0(B_79,A_78)) = k4_xboole_0(A_78,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_1097,c_20])).

tff(c_1154,plain,(
    ! [A_78,B_79] : k3_xboole_0(A_78,k2_xboole_0(B_79,A_78)) = A_78 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_1118])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_489,plain,(
    ! [A_53,B_54] : k4_xboole_0(k2_xboole_0(A_53,B_54),B_54) = k4_xboole_0(A_53,B_54) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_505,plain,(
    ! [A_53] : k4_xboole_0(A_53,k1_xboole_0) = k2_xboole_0(A_53,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_489,c_12])).

tff(c_515,plain,(
    ! [A_53] : k2_xboole_0(A_53,k1_xboole_0) = A_53 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_505])).

tff(c_22,plain,(
    ! [A_19] : k5_xboole_0(A_19,k1_xboole_0) = A_19 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_533,plain,(
    ! [A_56,B_57] : k5_xboole_0(A_56,k4_xboole_0(B_57,A_56)) = k2_xboole_0(A_56,B_57) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_555,plain,(
    ! [A_7,B_8] : k2_xboole_0(A_7,k4_xboole_0(A_7,B_8)) = k5_xboole_0(A_7,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_209,c_533])).

tff(c_573,plain,(
    ! [A_7,B_8] : k2_xboole_0(A_7,k4_xboole_0(A_7,B_8)) = A_7 ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_555])).

tff(c_704,plain,(
    ! [A_7,B_8] : k4_xboole_0(A_7,k2_xboole_0(B_8,A_7)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_209,c_637])).

tff(c_28,plain,(
    ! [A_24,B_25] : k5_xboole_0(A_24,k4_xboole_0(B_25,A_24)) = k2_xboole_0(A_24,B_25) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_14,plain,(
    ! [A_10,B_11] : k4_xboole_0(k2_xboole_0(A_10,B_11),B_11) = k4_xboole_0(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_546,plain,(
    ! [B_11,A_10] : k5_xboole_0(B_11,k4_xboole_0(A_10,B_11)) = k2_xboole_0(B_11,k2_xboole_0(A_10,B_11)) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_533])).

tff(c_1464,plain,(
    ! [B_88,A_89] : k2_xboole_0(B_88,k2_xboole_0(A_89,B_88)) = k2_xboole_0(B_88,A_89) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_546])).

tff(c_1483,plain,(
    ! [B_88,A_89] : k4_xboole_0(k2_xboole_0(B_88,A_89),k2_xboole_0(A_89,B_88)) = k4_xboole_0(B_88,k2_xboole_0(A_89,B_88)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1464,c_14])).

tff(c_2843,plain,(
    ! [B_125,A_126] : k4_xboole_0(k2_xboole_0(B_125,A_126),k2_xboole_0(A_126,B_125)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_704,c_1483])).

tff(c_2907,plain,(
    ! [A_7,B_8] : k4_xboole_0(k2_xboole_0(k4_xboole_0(A_7,B_8),A_7),A_7) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_573,c_2843])).

tff(c_66,plain,(
    ! [A_29,B_30] : r1_tarski(k4_xboole_0(A_29,B_30),A_29) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_69,plain,(
    ! [A_9] : r1_tarski(A_9,A_9) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_66])).

tff(c_208,plain,(
    ! [A_9] : k4_xboole_0(A_9,A_9) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_69,c_201])).

tff(c_3912,plain,(
    ! [A_140,B_141] : k4_xboole_0(A_140,k2_xboole_0(B_141,k4_xboole_0(A_140,B_141))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_208,c_637])).

tff(c_3960,plain,(
    ! [A_140,B_141] : k3_xboole_0(A_140,k2_xboole_0(B_141,k4_xboole_0(A_140,B_141))) = k4_xboole_0(A_140,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_3912,c_20])).

tff(c_7269,plain,(
    ! [A_183,B_184] : k3_xboole_0(A_183,k2_xboole_0(B_184,k4_xboole_0(A_183,B_184))) = A_183 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_3960])).

tff(c_7370,plain,(
    ! [A_7,B_8] : k3_xboole_0(k2_xboole_0(k4_xboole_0(A_7,B_8),A_7),k2_xboole_0(A_7,k1_xboole_0)) = k2_xboole_0(k4_xboole_0(A_7,B_8),A_7) ),
    inference(superposition,[status(thm),theory(equality)],[c_2907,c_7269])).

tff(c_7460,plain,(
    ! [A_7,B_8] : k2_xboole_0(k4_xboole_0(A_7,B_8),A_7) = A_7 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1154,c_2,c_515,c_7370])).

tff(c_552,plain,(
    ! [A_17,B_18] : k5_xboole_0(k4_xboole_0(A_17,B_18),k3_xboole_0(A_17,B_18)) = k2_xboole_0(k4_xboole_0(A_17,B_18),A_17) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_533])).

tff(c_11178,plain,(
    ! [A_257,B_258] : k5_xboole_0(k4_xboole_0(A_257,B_258),k3_xboole_0(A_257,B_258)) = A_257 ),
    inference(demodulation,[status(thm),theory(equality)],[c_7460,c_552])).

tff(c_71,plain,(
    ! [B_32,A_33] : k5_xboole_0(B_32,A_33) = k5_xboole_0(A_33,B_32) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_87,plain,(
    ! [A_33] : k5_xboole_0(k1_xboole_0,A_33) = A_33 ),
    inference(superposition,[status(thm),theory(equality)],[c_71,c_22])).

tff(c_26,plain,(
    ! [A_23] : k5_xboole_0(A_23,A_23) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_763,plain,(
    ! [A_65,B_66,C_67] : k5_xboole_0(k5_xboole_0(A_65,B_66),C_67) = k5_xboole_0(A_65,k5_xboole_0(B_66,C_67)) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_827,plain,(
    ! [A_23,C_67] : k5_xboole_0(A_23,k5_xboole_0(A_23,C_67)) = k5_xboole_0(k1_xboole_0,C_67) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_763])).

tff(c_840,plain,(
    ! [A_23,C_67] : k5_xboole_0(A_23,k5_xboole_0(A_23,C_67)) = C_67 ),
    inference(demodulation,[status(thm),theory(equality)],[c_87,c_827])).

tff(c_4,plain,(
    ! [B_4,A_3] : k5_xboole_0(B_4,A_3) = k5_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_867,plain,(
    ! [A_70,C_71] : k5_xboole_0(A_70,k5_xboole_0(A_70,C_71)) = C_71 ),
    inference(demodulation,[status(thm),theory(equality)],[c_87,c_827])).

tff(c_1164,plain,(
    ! [B_80,A_81] : k5_xboole_0(B_80,k5_xboole_0(A_81,B_80)) = A_81 ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_867])).

tff(c_1197,plain,(
    ! [A_23,C_67] : k5_xboole_0(k5_xboole_0(A_23,C_67),C_67) = A_23 ),
    inference(superposition,[status(thm),theory(equality)],[c_840,c_1164])).

tff(c_11208,plain,(
    ! [A_257,B_258] : k5_xboole_0(A_257,k3_xboole_0(A_257,B_258)) = k4_xboole_0(A_257,B_258) ),
    inference(superposition,[status(thm),theory(equality)],[c_11178,c_1197])).

tff(c_30,plain,(
    k5_xboole_0('#skF_1',k3_xboole_0('#skF_1','#skF_2')) != k4_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_49190,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_11208,c_30])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n011.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 19:39:12 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 12.34/6.55  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 12.34/6.56  
% 12.34/6.56  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 12.34/6.56  %$ r1_tarski > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1
% 12.34/6.56  
% 12.34/6.56  %Foreground sorts:
% 12.34/6.56  
% 12.34/6.56  
% 12.34/6.56  %Background operators:
% 12.34/6.56  
% 12.34/6.56  
% 12.34/6.56  %Foreground operators:
% 12.34/6.56  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 12.34/6.56  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 12.34/6.56  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 12.34/6.56  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 12.34/6.56  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 12.34/6.56  tff('#skF_2', type, '#skF_2': $i).
% 12.34/6.56  tff('#skF_1', type, '#skF_1': $i).
% 12.34/6.56  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 12.34/6.56  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 12.34/6.56  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 12.34/6.56  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 12.34/6.56  
% 12.34/6.57  tff(f_37, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 12.34/6.57  tff(f_35, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 12.34/6.57  tff(f_33, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 12.34/6.57  tff(f_41, axiom, (![A, B, C]: (k4_xboole_0(k4_xboole_0(A, B), C) = k4_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_xboole_1)).
% 12.34/6.57  tff(f_45, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 12.34/6.57  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 12.34/6.57  tff(f_39, axiom, (![A, B]: (k4_xboole_0(k2_xboole_0(A, B), B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t40_xboole_1)).
% 12.34/6.57  tff(f_47, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 12.34/6.57  tff(f_53, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 12.34/6.57  tff(f_29, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 12.34/6.57  tff(f_51, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 12.34/6.57  tff(f_49, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_xboole_1)).
% 12.34/6.57  tff(f_56, negated_conjecture, ~(![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 12.34/6.57  tff(c_12, plain, (![A_9]: (k4_xboole_0(A_9, k1_xboole_0)=A_9)), inference(cnfTransformation, [status(thm)], [f_37])).
% 12.34/6.57  tff(c_10, plain, (![A_7, B_8]: (r1_tarski(k4_xboole_0(A_7, B_8), A_7))), inference(cnfTransformation, [status(thm)], [f_35])).
% 12.34/6.57  tff(c_201, plain, (![A_37, B_38]: (k4_xboole_0(A_37, B_38)=k1_xboole_0 | ~r1_tarski(A_37, B_38))), inference(cnfTransformation, [status(thm)], [f_33])).
% 12.34/6.57  tff(c_209, plain, (![A_7, B_8]: (k4_xboole_0(k4_xboole_0(A_7, B_8), A_7)=k1_xboole_0)), inference(resolution, [status(thm)], [c_10, c_201])).
% 12.34/6.57  tff(c_637, plain, (![A_60, B_61, C_62]: (k4_xboole_0(k4_xboole_0(A_60, B_61), C_62)=k4_xboole_0(A_60, k2_xboole_0(B_61, C_62)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 12.34/6.57  tff(c_1097, plain, (![A_78, B_79]: (k4_xboole_0(A_78, k2_xboole_0(B_79, A_78))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_209, c_637])).
% 12.34/6.57  tff(c_20, plain, (![A_17, B_18]: (k4_xboole_0(A_17, k4_xboole_0(A_17, B_18))=k3_xboole_0(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_45])).
% 12.34/6.57  tff(c_1118, plain, (![A_78, B_79]: (k3_xboole_0(A_78, k2_xboole_0(B_79, A_78))=k4_xboole_0(A_78, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_1097, c_20])).
% 12.34/6.57  tff(c_1154, plain, (![A_78, B_79]: (k3_xboole_0(A_78, k2_xboole_0(B_79, A_78))=A_78)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_1118])).
% 12.34/6.57  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 12.34/6.57  tff(c_489, plain, (![A_53, B_54]: (k4_xboole_0(k2_xboole_0(A_53, B_54), B_54)=k4_xboole_0(A_53, B_54))), inference(cnfTransformation, [status(thm)], [f_39])).
% 12.34/6.57  tff(c_505, plain, (![A_53]: (k4_xboole_0(A_53, k1_xboole_0)=k2_xboole_0(A_53, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_489, c_12])).
% 12.34/6.57  tff(c_515, plain, (![A_53]: (k2_xboole_0(A_53, k1_xboole_0)=A_53)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_505])).
% 12.34/6.57  tff(c_22, plain, (![A_19]: (k5_xboole_0(A_19, k1_xboole_0)=A_19)), inference(cnfTransformation, [status(thm)], [f_47])).
% 12.34/6.57  tff(c_533, plain, (![A_56, B_57]: (k5_xboole_0(A_56, k4_xboole_0(B_57, A_56))=k2_xboole_0(A_56, B_57))), inference(cnfTransformation, [status(thm)], [f_53])).
% 12.34/6.57  tff(c_555, plain, (![A_7, B_8]: (k2_xboole_0(A_7, k4_xboole_0(A_7, B_8))=k5_xboole_0(A_7, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_209, c_533])).
% 12.34/6.57  tff(c_573, plain, (![A_7, B_8]: (k2_xboole_0(A_7, k4_xboole_0(A_7, B_8))=A_7)), inference(demodulation, [status(thm), theory('equality')], [c_22, c_555])).
% 12.34/6.57  tff(c_704, plain, (![A_7, B_8]: (k4_xboole_0(A_7, k2_xboole_0(B_8, A_7))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_209, c_637])).
% 12.34/6.57  tff(c_28, plain, (![A_24, B_25]: (k5_xboole_0(A_24, k4_xboole_0(B_25, A_24))=k2_xboole_0(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_53])).
% 12.34/6.57  tff(c_14, plain, (![A_10, B_11]: (k4_xboole_0(k2_xboole_0(A_10, B_11), B_11)=k4_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_39])).
% 12.34/6.57  tff(c_546, plain, (![B_11, A_10]: (k5_xboole_0(B_11, k4_xboole_0(A_10, B_11))=k2_xboole_0(B_11, k2_xboole_0(A_10, B_11)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_533])).
% 12.34/6.57  tff(c_1464, plain, (![B_88, A_89]: (k2_xboole_0(B_88, k2_xboole_0(A_89, B_88))=k2_xboole_0(B_88, A_89))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_546])).
% 12.34/6.57  tff(c_1483, plain, (![B_88, A_89]: (k4_xboole_0(k2_xboole_0(B_88, A_89), k2_xboole_0(A_89, B_88))=k4_xboole_0(B_88, k2_xboole_0(A_89, B_88)))), inference(superposition, [status(thm), theory('equality')], [c_1464, c_14])).
% 12.34/6.57  tff(c_2843, plain, (![B_125, A_126]: (k4_xboole_0(k2_xboole_0(B_125, A_126), k2_xboole_0(A_126, B_125))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_704, c_1483])).
% 12.34/6.57  tff(c_2907, plain, (![A_7, B_8]: (k4_xboole_0(k2_xboole_0(k4_xboole_0(A_7, B_8), A_7), A_7)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_573, c_2843])).
% 12.34/6.57  tff(c_66, plain, (![A_29, B_30]: (r1_tarski(k4_xboole_0(A_29, B_30), A_29))), inference(cnfTransformation, [status(thm)], [f_35])).
% 12.34/6.57  tff(c_69, plain, (![A_9]: (r1_tarski(A_9, A_9))), inference(superposition, [status(thm), theory('equality')], [c_12, c_66])).
% 12.34/6.57  tff(c_208, plain, (![A_9]: (k4_xboole_0(A_9, A_9)=k1_xboole_0)), inference(resolution, [status(thm)], [c_69, c_201])).
% 12.34/6.57  tff(c_3912, plain, (![A_140, B_141]: (k4_xboole_0(A_140, k2_xboole_0(B_141, k4_xboole_0(A_140, B_141)))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_208, c_637])).
% 12.34/6.57  tff(c_3960, plain, (![A_140, B_141]: (k3_xboole_0(A_140, k2_xboole_0(B_141, k4_xboole_0(A_140, B_141)))=k4_xboole_0(A_140, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_3912, c_20])).
% 12.34/6.57  tff(c_7269, plain, (![A_183, B_184]: (k3_xboole_0(A_183, k2_xboole_0(B_184, k4_xboole_0(A_183, B_184)))=A_183)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_3960])).
% 12.34/6.57  tff(c_7370, plain, (![A_7, B_8]: (k3_xboole_0(k2_xboole_0(k4_xboole_0(A_7, B_8), A_7), k2_xboole_0(A_7, k1_xboole_0))=k2_xboole_0(k4_xboole_0(A_7, B_8), A_7))), inference(superposition, [status(thm), theory('equality')], [c_2907, c_7269])).
% 12.34/6.57  tff(c_7460, plain, (![A_7, B_8]: (k2_xboole_0(k4_xboole_0(A_7, B_8), A_7)=A_7)), inference(demodulation, [status(thm), theory('equality')], [c_1154, c_2, c_515, c_7370])).
% 12.34/6.57  tff(c_552, plain, (![A_17, B_18]: (k5_xboole_0(k4_xboole_0(A_17, B_18), k3_xboole_0(A_17, B_18))=k2_xboole_0(k4_xboole_0(A_17, B_18), A_17))), inference(superposition, [status(thm), theory('equality')], [c_20, c_533])).
% 12.34/6.57  tff(c_11178, plain, (![A_257, B_258]: (k5_xboole_0(k4_xboole_0(A_257, B_258), k3_xboole_0(A_257, B_258))=A_257)), inference(demodulation, [status(thm), theory('equality')], [c_7460, c_552])).
% 12.34/6.57  tff(c_71, plain, (![B_32, A_33]: (k5_xboole_0(B_32, A_33)=k5_xboole_0(A_33, B_32))), inference(cnfTransformation, [status(thm)], [f_29])).
% 12.34/6.57  tff(c_87, plain, (![A_33]: (k5_xboole_0(k1_xboole_0, A_33)=A_33)), inference(superposition, [status(thm), theory('equality')], [c_71, c_22])).
% 12.34/6.57  tff(c_26, plain, (![A_23]: (k5_xboole_0(A_23, A_23)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_51])).
% 12.34/6.57  tff(c_763, plain, (![A_65, B_66, C_67]: (k5_xboole_0(k5_xboole_0(A_65, B_66), C_67)=k5_xboole_0(A_65, k5_xboole_0(B_66, C_67)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 12.34/6.57  tff(c_827, plain, (![A_23, C_67]: (k5_xboole_0(A_23, k5_xboole_0(A_23, C_67))=k5_xboole_0(k1_xboole_0, C_67))), inference(superposition, [status(thm), theory('equality')], [c_26, c_763])).
% 12.34/6.57  tff(c_840, plain, (![A_23, C_67]: (k5_xboole_0(A_23, k5_xboole_0(A_23, C_67))=C_67)), inference(demodulation, [status(thm), theory('equality')], [c_87, c_827])).
% 12.34/6.57  tff(c_4, plain, (![B_4, A_3]: (k5_xboole_0(B_4, A_3)=k5_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 12.34/6.57  tff(c_867, plain, (![A_70, C_71]: (k5_xboole_0(A_70, k5_xboole_0(A_70, C_71))=C_71)), inference(demodulation, [status(thm), theory('equality')], [c_87, c_827])).
% 12.34/6.57  tff(c_1164, plain, (![B_80, A_81]: (k5_xboole_0(B_80, k5_xboole_0(A_81, B_80))=A_81)), inference(superposition, [status(thm), theory('equality')], [c_4, c_867])).
% 12.34/6.57  tff(c_1197, plain, (![A_23, C_67]: (k5_xboole_0(k5_xboole_0(A_23, C_67), C_67)=A_23)), inference(superposition, [status(thm), theory('equality')], [c_840, c_1164])).
% 12.34/6.57  tff(c_11208, plain, (![A_257, B_258]: (k5_xboole_0(A_257, k3_xboole_0(A_257, B_258))=k4_xboole_0(A_257, B_258))), inference(superposition, [status(thm), theory('equality')], [c_11178, c_1197])).
% 12.34/6.57  tff(c_30, plain, (k5_xboole_0('#skF_1', k3_xboole_0('#skF_1', '#skF_2'))!=k4_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_56])).
% 12.34/6.57  tff(c_49190, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_11208, c_30])).
% 12.34/6.57  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 12.34/6.57  
% 12.34/6.57  Inference rules
% 12.34/6.57  ----------------------
% 12.34/6.57  #Ref     : 0
% 12.34/6.57  #Sup     : 12380
% 12.34/6.57  #Fact    : 0
% 12.34/6.57  #Define  : 0
% 12.34/6.57  #Split   : 0
% 12.34/6.57  #Chain   : 0
% 12.34/6.57  #Close   : 0
% 12.34/6.57  
% 12.34/6.57  Ordering : KBO
% 12.34/6.57  
% 12.34/6.57  Simplification rules
% 12.34/6.57  ----------------------
% 12.34/6.57  #Subsume      : 211
% 12.34/6.57  #Demod        : 13856
% 12.34/6.57  #Tautology    : 8503
% 12.34/6.57  #SimpNegUnit  : 0
% 12.34/6.57  #BackRed      : 13
% 12.34/6.57  
% 12.34/6.57  #Partial instantiations: 0
% 12.34/6.57  #Strategies tried      : 1
% 12.34/6.57  
% 12.34/6.57  Timing (in seconds)
% 12.34/6.57  ----------------------
% 12.34/6.58  Preprocessing        : 0.29
% 12.34/6.58  Parsing              : 0.16
% 12.34/6.58  CNF conversion       : 0.02
% 12.34/6.58  Main loop            : 5.51
% 12.34/6.58  Inferencing          : 0.95
% 12.34/6.58  Reduction            : 3.37
% 12.34/6.58  Demodulation         : 3.07
% 12.34/6.58  BG Simplification    : 0.12
% 12.34/6.58  Subsumption          : 0.83
% 12.34/6.58  Abstraction          : 0.21
% 12.34/6.58  MUC search           : 0.00
% 12.34/6.58  Cooper               : 0.00
% 12.34/6.58  Total                : 5.83
% 12.34/6.58  Index Insertion      : 0.00
% 12.34/6.58  Index Deletion       : 0.00
% 12.34/6.58  Index Matching       : 0.00
% 12.34/6.58  BG Taut test         : 0.00
%------------------------------------------------------------------------------

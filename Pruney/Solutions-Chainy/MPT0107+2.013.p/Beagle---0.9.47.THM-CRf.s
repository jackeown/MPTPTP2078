%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:44:54 EST 2020

% Result     : Theorem 5.78s
% Output     : CNFRefutation 5.78s
% Verified   : 
% Statistics : Number of formulae       :   52 (  97 expanded)
%              Number of leaves         :   20 (  40 expanded)
%              Depth                    :   13
%              Number of atoms          :   42 (  87 expanded)
%              Number of equality atoms :   41 (  86 expanded)
%              Maximal formula depth    :    4 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1

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

tff(f_35,axiom,(
    ! [A,B] : k4_xboole_0(A,k3_xboole_0(A,B)) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_31,axiom,(
    ! [A,B] : k4_xboole_0(k2_xboole_0(A,B),B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).

tff(f_41,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_39,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

tff(f_43,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_33,axiom,(
    ! [A,B,C] : k4_xboole_0(k4_xboole_0(A,B),C) = k4_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k2_xboole_0(k4_xboole_0(A,B),k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_xboole_0)).

tff(f_46,negated_conjecture,(
    ~ ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(c_10,plain,(
    ! [A_10,B_11] : k4_xboole_0(A_10,k3_xboole_0(A_10,B_11)) = k4_xboole_0(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_12,plain,(
    ! [A_12,B_13] : k4_xboole_0(A_12,k4_xboole_0(A_12,B_13)) = k3_xboole_0(A_12,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_106,plain,(
    ! [A_25,B_26] : k4_xboole_0(k2_xboole_0(A_25,B_26),B_26) = k4_xboole_0(A_25,B_26) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_121,plain,(
    ! [B_2,A_1] : k4_xboole_0(k2_xboole_0(B_2,A_1),B_2) = k4_xboole_0(A_1,B_2) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_106])).

tff(c_16,plain,(
    ! [A_15] : k5_xboole_0(A_15,k1_xboole_0) = A_15 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_14,plain,(
    ! [A_14] : k4_xboole_0(k1_xboole_0,A_14) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_70,plain,(
    ! [A_22,B_23] : k5_xboole_0(A_22,k4_xboole_0(B_23,A_22)) = k2_xboole_0(A_22,B_23) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_79,plain,(
    ! [A_14] : k5_xboole_0(A_14,k1_xboole_0) = k2_xboole_0(A_14,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_70])).

tff(c_83,plain,(
    ! [A_24] : k2_xboole_0(A_24,k1_xboole_0) = A_24 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_79])).

tff(c_129,plain,(
    ! [A_27] : k2_xboole_0(k1_xboole_0,A_27) = A_27 ),
    inference(superposition,[status(thm),theory(equality)],[c_83,c_2])).

tff(c_6,plain,(
    ! [A_5,B_6] : k4_xboole_0(k2_xboole_0(A_5,B_6),B_6) = k4_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_135,plain,(
    ! [A_27] : k4_xboole_0(k1_xboole_0,A_27) = k4_xboole_0(A_27,A_27) ),
    inference(superposition,[status(thm),theory(equality)],[c_129,c_6])).

tff(c_162,plain,(
    ! [A_27] : k4_xboole_0(A_27,A_27) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_135])).

tff(c_350,plain,(
    ! [A_36,B_37,C_38] : k4_xboole_0(k4_xboole_0(A_36,B_37),C_38) = k4_xboole_0(A_36,k2_xboole_0(B_37,C_38)) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_18,plain,(
    ! [A_16,B_17] : k5_xboole_0(A_16,k4_xboole_0(B_17,A_16)) = k2_xboole_0(A_16,B_17) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_4244,plain,(
    ! [C_116,A_117,B_118] : k5_xboole_0(C_116,k4_xboole_0(A_117,k2_xboole_0(B_118,C_116))) = k2_xboole_0(C_116,k4_xboole_0(A_117,B_118)) ),
    inference(superposition,[status(thm),theory(equality)],[c_350,c_18])).

tff(c_4341,plain,(
    ! [C_116,B_118] : k2_xboole_0(C_116,k4_xboole_0(k2_xboole_0(B_118,C_116),B_118)) = k5_xboole_0(C_116,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_162,c_4244])).

tff(c_4390,plain,(
    ! [C_119,B_120] : k2_xboole_0(C_119,k4_xboole_0(C_119,B_120)) = C_119 ),
    inference(demodulation,[status(thm),theory(equality)],[c_121,c_16,c_4341])).

tff(c_4779,plain,(
    ! [A_123,B_124] : k2_xboole_0(A_123,k3_xboole_0(A_123,B_124)) = A_123 ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_4390])).

tff(c_89,plain,(
    ! [A_24] : k2_xboole_0(k1_xboole_0,A_24) = A_24 ),
    inference(superposition,[status(thm),theory(equality)],[c_83,c_2])).

tff(c_400,plain,(
    ! [A_27,C_38] : k4_xboole_0(A_27,k2_xboole_0(A_27,C_38)) = k4_xboole_0(k1_xboole_0,C_38) ),
    inference(superposition,[status(thm),theory(equality)],[c_162,c_350])).

tff(c_443,plain,(
    ! [A_40,C_41] : k4_xboole_0(A_40,k2_xboole_0(A_40,C_41)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_400])).

tff(c_479,plain,(
    ! [A_1,B_2] : k4_xboole_0(A_1,k2_xboole_0(B_2,A_1)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_443])).

tff(c_580,plain,(
    ! [A_45,B_46] : k2_xboole_0(k4_xboole_0(A_45,B_46),k4_xboole_0(B_46,A_45)) = k5_xboole_0(A_45,B_46) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_1131,plain,(
    ! [B_59,A_60] : k2_xboole_0(k4_xboole_0(B_59,A_60),k4_xboole_0(A_60,B_59)) = k5_xboole_0(A_60,B_59) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_580])).

tff(c_1229,plain,(
    ! [B_6,A_5] : k2_xboole_0(k4_xboole_0(B_6,k2_xboole_0(A_5,B_6)),k4_xboole_0(A_5,B_6)) = k5_xboole_0(k2_xboole_0(A_5,B_6),B_6) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_1131])).

tff(c_1265,plain,(
    ! [A_5,B_6] : k5_xboole_0(k2_xboole_0(A_5,B_6),B_6) = k4_xboole_0(A_5,B_6) ),
    inference(demodulation,[status(thm),theory(equality)],[c_89,c_479,c_1229])).

tff(c_4827,plain,(
    ! [A_123,B_124] : k5_xboole_0(A_123,k3_xboole_0(A_123,B_124)) = k4_xboole_0(A_123,k3_xboole_0(A_123,B_124)) ),
    inference(superposition,[status(thm),theory(equality)],[c_4779,c_1265])).

tff(c_4918,plain,(
    ! [A_123,B_124] : k5_xboole_0(A_123,k3_xboole_0(A_123,B_124)) = k4_xboole_0(A_123,B_124) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_4827])).

tff(c_20,plain,(
    k5_xboole_0('#skF_1',k3_xboole_0('#skF_1','#skF_2')) != k4_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_9253,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4918,c_20])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:05:01 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.78/2.24  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.78/2.25  
% 5.78/2.25  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.78/2.25  %$ k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1
% 5.78/2.25  
% 5.78/2.25  %Foreground sorts:
% 5.78/2.25  
% 5.78/2.25  
% 5.78/2.25  %Background operators:
% 5.78/2.25  
% 5.78/2.25  
% 5.78/2.25  %Foreground operators:
% 5.78/2.25  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.78/2.25  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 5.78/2.25  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.78/2.25  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 5.78/2.25  tff('#skF_2', type, '#skF_2': $i).
% 5.78/2.25  tff('#skF_1', type, '#skF_1': $i).
% 5.78/2.25  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.78/2.25  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.78/2.25  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.78/2.25  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 5.78/2.25  
% 5.78/2.26  tff(f_35, axiom, (![A, B]: (k4_xboole_0(A, k3_xboole_0(A, B)) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_xboole_1)).
% 5.78/2.26  tff(f_37, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 5.78/2.26  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 5.78/2.26  tff(f_31, axiom, (![A, B]: (k4_xboole_0(k2_xboole_0(A, B), B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t40_xboole_1)).
% 5.78/2.26  tff(f_41, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 5.78/2.26  tff(f_39, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_boole)).
% 5.78/2.26  tff(f_43, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 5.78/2.26  tff(f_33, axiom, (![A, B, C]: (k4_xboole_0(k4_xboole_0(A, B), C) = k4_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_xboole_1)).
% 5.78/2.26  tff(f_29, axiom, (![A, B]: (k5_xboole_0(A, B) = k2_xboole_0(k4_xboole_0(A, B), k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d6_xboole_0)).
% 5.78/2.26  tff(f_46, negated_conjecture, ~(![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 5.78/2.26  tff(c_10, plain, (![A_10, B_11]: (k4_xboole_0(A_10, k3_xboole_0(A_10, B_11))=k4_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.78/2.26  tff(c_12, plain, (![A_12, B_13]: (k4_xboole_0(A_12, k4_xboole_0(A_12, B_13))=k3_xboole_0(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.78/2.26  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 5.78/2.26  tff(c_106, plain, (![A_25, B_26]: (k4_xboole_0(k2_xboole_0(A_25, B_26), B_26)=k4_xboole_0(A_25, B_26))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.78/2.26  tff(c_121, plain, (![B_2, A_1]: (k4_xboole_0(k2_xboole_0(B_2, A_1), B_2)=k4_xboole_0(A_1, B_2))), inference(superposition, [status(thm), theory('equality')], [c_2, c_106])).
% 5.78/2.26  tff(c_16, plain, (![A_15]: (k5_xboole_0(A_15, k1_xboole_0)=A_15)), inference(cnfTransformation, [status(thm)], [f_41])).
% 5.78/2.26  tff(c_14, plain, (![A_14]: (k4_xboole_0(k1_xboole_0, A_14)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 5.78/2.26  tff(c_70, plain, (![A_22, B_23]: (k5_xboole_0(A_22, k4_xboole_0(B_23, A_22))=k2_xboole_0(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_43])).
% 5.78/2.26  tff(c_79, plain, (![A_14]: (k5_xboole_0(A_14, k1_xboole_0)=k2_xboole_0(A_14, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_14, c_70])).
% 5.78/2.26  tff(c_83, plain, (![A_24]: (k2_xboole_0(A_24, k1_xboole_0)=A_24)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_79])).
% 5.78/2.26  tff(c_129, plain, (![A_27]: (k2_xboole_0(k1_xboole_0, A_27)=A_27)), inference(superposition, [status(thm), theory('equality')], [c_83, c_2])).
% 5.78/2.26  tff(c_6, plain, (![A_5, B_6]: (k4_xboole_0(k2_xboole_0(A_5, B_6), B_6)=k4_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.78/2.26  tff(c_135, plain, (![A_27]: (k4_xboole_0(k1_xboole_0, A_27)=k4_xboole_0(A_27, A_27))), inference(superposition, [status(thm), theory('equality')], [c_129, c_6])).
% 5.78/2.26  tff(c_162, plain, (![A_27]: (k4_xboole_0(A_27, A_27)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_135])).
% 5.78/2.26  tff(c_350, plain, (![A_36, B_37, C_38]: (k4_xboole_0(k4_xboole_0(A_36, B_37), C_38)=k4_xboole_0(A_36, k2_xboole_0(B_37, C_38)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 5.78/2.26  tff(c_18, plain, (![A_16, B_17]: (k5_xboole_0(A_16, k4_xboole_0(B_17, A_16))=k2_xboole_0(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_43])).
% 5.78/2.26  tff(c_4244, plain, (![C_116, A_117, B_118]: (k5_xboole_0(C_116, k4_xboole_0(A_117, k2_xboole_0(B_118, C_116)))=k2_xboole_0(C_116, k4_xboole_0(A_117, B_118)))), inference(superposition, [status(thm), theory('equality')], [c_350, c_18])).
% 5.78/2.26  tff(c_4341, plain, (![C_116, B_118]: (k2_xboole_0(C_116, k4_xboole_0(k2_xboole_0(B_118, C_116), B_118))=k5_xboole_0(C_116, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_162, c_4244])).
% 5.78/2.26  tff(c_4390, plain, (![C_119, B_120]: (k2_xboole_0(C_119, k4_xboole_0(C_119, B_120))=C_119)), inference(demodulation, [status(thm), theory('equality')], [c_121, c_16, c_4341])).
% 5.78/2.26  tff(c_4779, plain, (![A_123, B_124]: (k2_xboole_0(A_123, k3_xboole_0(A_123, B_124))=A_123)), inference(superposition, [status(thm), theory('equality')], [c_12, c_4390])).
% 5.78/2.26  tff(c_89, plain, (![A_24]: (k2_xboole_0(k1_xboole_0, A_24)=A_24)), inference(superposition, [status(thm), theory('equality')], [c_83, c_2])).
% 5.78/2.26  tff(c_400, plain, (![A_27, C_38]: (k4_xboole_0(A_27, k2_xboole_0(A_27, C_38))=k4_xboole_0(k1_xboole_0, C_38))), inference(superposition, [status(thm), theory('equality')], [c_162, c_350])).
% 5.78/2.26  tff(c_443, plain, (![A_40, C_41]: (k4_xboole_0(A_40, k2_xboole_0(A_40, C_41))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_400])).
% 5.78/2.26  tff(c_479, plain, (![A_1, B_2]: (k4_xboole_0(A_1, k2_xboole_0(B_2, A_1))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2, c_443])).
% 5.78/2.26  tff(c_580, plain, (![A_45, B_46]: (k2_xboole_0(k4_xboole_0(A_45, B_46), k4_xboole_0(B_46, A_45))=k5_xboole_0(A_45, B_46))), inference(cnfTransformation, [status(thm)], [f_29])).
% 5.78/2.26  tff(c_1131, plain, (![B_59, A_60]: (k2_xboole_0(k4_xboole_0(B_59, A_60), k4_xboole_0(A_60, B_59))=k5_xboole_0(A_60, B_59))), inference(superposition, [status(thm), theory('equality')], [c_2, c_580])).
% 5.78/2.26  tff(c_1229, plain, (![B_6, A_5]: (k2_xboole_0(k4_xboole_0(B_6, k2_xboole_0(A_5, B_6)), k4_xboole_0(A_5, B_6))=k5_xboole_0(k2_xboole_0(A_5, B_6), B_6))), inference(superposition, [status(thm), theory('equality')], [c_6, c_1131])).
% 5.78/2.26  tff(c_1265, plain, (![A_5, B_6]: (k5_xboole_0(k2_xboole_0(A_5, B_6), B_6)=k4_xboole_0(A_5, B_6))), inference(demodulation, [status(thm), theory('equality')], [c_89, c_479, c_1229])).
% 5.78/2.26  tff(c_4827, plain, (![A_123, B_124]: (k5_xboole_0(A_123, k3_xboole_0(A_123, B_124))=k4_xboole_0(A_123, k3_xboole_0(A_123, B_124)))), inference(superposition, [status(thm), theory('equality')], [c_4779, c_1265])).
% 5.78/2.26  tff(c_4918, plain, (![A_123, B_124]: (k5_xboole_0(A_123, k3_xboole_0(A_123, B_124))=k4_xboole_0(A_123, B_124))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_4827])).
% 5.78/2.26  tff(c_20, plain, (k5_xboole_0('#skF_1', k3_xboole_0('#skF_1', '#skF_2'))!=k4_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_46])).
% 5.78/2.26  tff(c_9253, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4918, c_20])).
% 5.78/2.26  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.78/2.26  
% 5.78/2.26  Inference rules
% 5.78/2.26  ----------------------
% 5.78/2.26  #Ref     : 0
% 5.78/2.26  #Sup     : 2301
% 5.78/2.26  #Fact    : 0
% 5.78/2.26  #Define  : 0
% 5.78/2.26  #Split   : 0
% 5.78/2.26  #Chain   : 0
% 5.78/2.26  #Close   : 0
% 5.78/2.26  
% 5.78/2.26  Ordering : KBO
% 5.78/2.26  
% 5.78/2.26  Simplification rules
% 5.78/2.26  ----------------------
% 5.78/2.26  #Subsume      : 6
% 5.78/2.26  #Demod        : 2775
% 5.78/2.26  #Tautology    : 1520
% 5.78/2.26  #SimpNegUnit  : 0
% 5.78/2.26  #BackRed      : 5
% 5.78/2.26  
% 5.78/2.26  #Partial instantiations: 0
% 5.78/2.26  #Strategies tried      : 1
% 5.78/2.26  
% 5.78/2.26  Timing (in seconds)
% 5.78/2.26  ----------------------
% 5.78/2.26  Preprocessing        : 0.27
% 5.78/2.26  Parsing              : 0.15
% 5.78/2.26  CNF conversion       : 0.02
% 5.78/2.26  Main loop            : 1.19
% 5.78/2.26  Inferencing          : 0.33
% 5.78/2.26  Reduction            : 0.61
% 5.78/2.26  Demodulation         : 0.52
% 5.78/2.26  BG Simplification    : 0.04
% 5.78/2.26  Subsumption          : 0.15
% 5.78/2.27  Abstraction          : 0.07
% 5.78/2.27  MUC search           : 0.00
% 5.78/2.27  Cooper               : 0.00
% 5.78/2.27  Total                : 1.49
% 5.78/2.27  Index Insertion      : 0.00
% 5.78/2.27  Index Deletion       : 0.00
% 5.78/2.27  Index Matching       : 0.00
% 5.78/2.27  BG Taut test         : 0.00
%------------------------------------------------------------------------------

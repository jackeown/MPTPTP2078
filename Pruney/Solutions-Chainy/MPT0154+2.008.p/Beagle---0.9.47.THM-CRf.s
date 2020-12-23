%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:46:05 EST 2020

% Result     : Theorem 9.44s
% Output     : CNFRefutation 9.44s
% Verified   : 
% Statistics : Number of formulae       :   55 (  83 expanded)
%              Number of leaves         :   24 (  37 expanded)
%              Depth                    :   12
%              Number of atoms          :   42 (  70 expanded)
%              Number of equality atoms :   41 (  69 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

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
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_45,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k2_xboole_0(k1_tarski(A),k2_tarski(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_enumset1)).

tff(f_43,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_xboole_0(k1_tarski(A),k1_tarski(B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).

tff(f_33,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_31,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_39,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_37,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_50,negated_conjecture,(
    ~ ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(c_10,plain,(
    ! [A_9] : k5_xboole_0(A_9,k1_xboole_0) = A_9 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_20,plain,(
    ! [A_18,B_19,C_20] : k2_xboole_0(k1_tarski(A_18),k2_tarski(B_19,C_20)) = k1_enumset1(A_18,B_19,C_20) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_249,plain,(
    ! [A_36,B_37] : k2_xboole_0(k1_tarski(A_36),k1_tarski(B_37)) = k2_tarski(A_36,B_37) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_8,plain,(
    ! [A_7,B_8] : k4_xboole_0(A_7,k2_xboole_0(A_7,B_8)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_255,plain,(
    ! [A_36,B_37] : k4_xboole_0(k1_tarski(A_36),k2_tarski(A_36,B_37)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_249,c_8])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_197,plain,(
    ! [A_32,B_33] : k5_xboole_0(A_32,k3_xboole_0(A_32,B_33)) = k4_xboole_0(A_32,B_33) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_217,plain,(
    ! [B_2,A_1] : k5_xboole_0(B_2,k3_xboole_0(A_1,B_2)) = k4_xboole_0(B_2,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_197])).

tff(c_67,plain,(
    ! [B_27,A_28] : k5_xboole_0(B_27,A_28) = k5_xboole_0(A_28,B_27) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_83,plain,(
    ! [A_28] : k5_xboole_0(k1_xboole_0,A_28) = A_28 ),
    inference(superposition,[status(thm),theory(equality)],[c_67,c_10])).

tff(c_6,plain,(
    ! [A_5,B_6] : k5_xboole_0(A_5,k3_xboole_0(A_5,B_6)) = k4_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_14,plain,(
    ! [A_13] : k5_xboole_0(A_13,A_13) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_364,plain,(
    ! [A_45,B_46,C_47] : k5_xboole_0(k5_xboole_0(A_45,B_46),C_47) = k5_xboole_0(A_45,k5_xboole_0(B_46,C_47)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_439,plain,(
    ! [A_13,C_47] : k5_xboole_0(A_13,k5_xboole_0(A_13,C_47)) = k5_xboole_0(k1_xboole_0,C_47) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_364])).

tff(c_453,plain,(
    ! [A_48,C_49] : k5_xboole_0(A_48,k5_xboole_0(A_48,C_49)) = C_49 ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_439])).

tff(c_1837,plain,(
    ! [A_87,B_88] : k5_xboole_0(A_87,k4_xboole_0(A_87,B_88)) = k3_xboole_0(A_87,B_88) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_453])).

tff(c_4,plain,(
    ! [B_4,A_3] : k5_xboole_0(B_4,A_3) = k5_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_1249,plain,(
    ! [B_79,A_80,B_81] : k5_xboole_0(B_79,k5_xboole_0(A_80,B_81)) = k5_xboole_0(A_80,k5_xboole_0(B_81,B_79)) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_364])).

tff(c_1488,plain,(
    ! [A_28,B_79] : k5_xboole_0(k1_xboole_0,k5_xboole_0(A_28,B_79)) = k5_xboole_0(B_79,A_28) ),
    inference(superposition,[status(thm),theory(equality)],[c_83,c_1249])).

tff(c_1843,plain,(
    ! [A_87,B_88] : k5_xboole_0(k4_xboole_0(A_87,B_88),A_87) = k5_xboole_0(k1_xboole_0,k3_xboole_0(A_87,B_88)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1837,c_1488])).

tff(c_1923,plain,(
    ! [A_87,B_88] : k5_xboole_0(k4_xboole_0(A_87,B_88),A_87) = k3_xboole_0(A_87,B_88) ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_1843])).

tff(c_16,plain,(
    ! [A_14,B_15] : k5_xboole_0(A_14,k4_xboole_0(B_15,A_14)) = k2_xboole_0(A_14,B_15) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_6685,plain,(
    ! [A_154,B_155,C_156] : k5_xboole_0(A_154,k5_xboole_0(k4_xboole_0(B_155,A_154),C_156)) = k5_xboole_0(k2_xboole_0(A_154,B_155),C_156) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_364])).

tff(c_6796,plain,(
    ! [B_88,A_87] : k5_xboole_0(k2_xboole_0(B_88,A_87),A_87) = k5_xboole_0(B_88,k3_xboole_0(A_87,B_88)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1923,c_6685])).

tff(c_7045,plain,(
    ! [B_161,A_162] : k5_xboole_0(k2_xboole_0(B_161,A_162),A_162) = k4_xboole_0(B_161,A_162) ),
    inference(demodulation,[status(thm),theory(equality)],[c_217,c_6796])).

tff(c_452,plain,(
    ! [A_13,C_47] : k5_xboole_0(A_13,k5_xboole_0(A_13,C_47)) = C_47 ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_439])).

tff(c_16547,plain,(
    ! [B_220,A_221] : k5_xboole_0(k2_xboole_0(B_220,A_221),k4_xboole_0(B_220,A_221)) = A_221 ),
    inference(superposition,[status(thm),theory(equality)],[c_7045,c_452])).

tff(c_16681,plain,(
    ! [A_36,B_37] : k5_xboole_0(k2_xboole_0(k1_tarski(A_36),k2_tarski(A_36,B_37)),k1_xboole_0) = k2_tarski(A_36,B_37) ),
    inference(superposition,[status(thm),theory(equality)],[c_255,c_16547])).

tff(c_16715,plain,(
    ! [A_36,B_37] : k1_enumset1(A_36,A_36,B_37) = k2_tarski(A_36,B_37) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_20,c_16681])).

tff(c_24,plain,(
    k1_enumset1('#skF_1','#skF_1','#skF_2') != k2_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_16719,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_16715,c_24])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:20:40 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.44/3.80  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.44/3.80  
% 9.44/3.80  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.44/3.81  %$ k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 9.44/3.81  
% 9.44/3.81  %Foreground sorts:
% 9.44/3.81  
% 9.44/3.81  
% 9.44/3.81  %Background operators:
% 9.44/3.81  
% 9.44/3.81  
% 9.44/3.81  %Foreground operators:
% 9.44/3.81  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.44/3.81  tff(k1_tarski, type, k1_tarski: $i > $i).
% 9.44/3.81  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 9.44/3.81  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 9.44/3.81  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 9.44/3.81  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 9.44/3.81  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 9.44/3.81  tff('#skF_2', type, '#skF_2': $i).
% 9.44/3.81  tff('#skF_1', type, '#skF_1': $i).
% 9.44/3.81  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.44/3.81  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.44/3.81  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 9.44/3.81  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 9.44/3.81  
% 9.44/3.82  tff(f_35, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 9.44/3.82  tff(f_45, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k2_xboole_0(k1_tarski(A), k2_tarski(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t42_enumset1)).
% 9.44/3.82  tff(f_43, axiom, (![A, B]: (k2_tarski(A, B) = k2_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_enumset1)).
% 9.44/3.82  tff(f_33, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_xboole_1)).
% 9.44/3.82  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 9.44/3.82  tff(f_31, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 9.44/3.82  tff(f_29, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 9.44/3.82  tff(f_39, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 9.44/3.82  tff(f_37, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_xboole_1)).
% 9.44/3.82  tff(f_41, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 9.44/3.82  tff(f_50, negated_conjecture, ~(![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 9.44/3.82  tff(c_10, plain, (![A_9]: (k5_xboole_0(A_9, k1_xboole_0)=A_9)), inference(cnfTransformation, [status(thm)], [f_35])).
% 9.44/3.82  tff(c_20, plain, (![A_18, B_19, C_20]: (k2_xboole_0(k1_tarski(A_18), k2_tarski(B_19, C_20))=k1_enumset1(A_18, B_19, C_20))), inference(cnfTransformation, [status(thm)], [f_45])).
% 9.44/3.82  tff(c_249, plain, (![A_36, B_37]: (k2_xboole_0(k1_tarski(A_36), k1_tarski(B_37))=k2_tarski(A_36, B_37))), inference(cnfTransformation, [status(thm)], [f_43])).
% 9.44/3.82  tff(c_8, plain, (![A_7, B_8]: (k4_xboole_0(A_7, k2_xboole_0(A_7, B_8))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 9.44/3.82  tff(c_255, plain, (![A_36, B_37]: (k4_xboole_0(k1_tarski(A_36), k2_tarski(A_36, B_37))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_249, c_8])).
% 9.44/3.82  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 9.44/3.82  tff(c_197, plain, (![A_32, B_33]: (k5_xboole_0(A_32, k3_xboole_0(A_32, B_33))=k4_xboole_0(A_32, B_33))), inference(cnfTransformation, [status(thm)], [f_31])).
% 9.44/3.82  tff(c_217, plain, (![B_2, A_1]: (k5_xboole_0(B_2, k3_xboole_0(A_1, B_2))=k4_xboole_0(B_2, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_197])).
% 9.44/3.82  tff(c_67, plain, (![B_27, A_28]: (k5_xboole_0(B_27, A_28)=k5_xboole_0(A_28, B_27))), inference(cnfTransformation, [status(thm)], [f_29])).
% 9.44/3.82  tff(c_83, plain, (![A_28]: (k5_xboole_0(k1_xboole_0, A_28)=A_28)), inference(superposition, [status(thm), theory('equality')], [c_67, c_10])).
% 9.44/3.82  tff(c_6, plain, (![A_5, B_6]: (k5_xboole_0(A_5, k3_xboole_0(A_5, B_6))=k4_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_31])).
% 9.44/3.82  tff(c_14, plain, (![A_13]: (k5_xboole_0(A_13, A_13)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 9.44/3.82  tff(c_364, plain, (![A_45, B_46, C_47]: (k5_xboole_0(k5_xboole_0(A_45, B_46), C_47)=k5_xboole_0(A_45, k5_xboole_0(B_46, C_47)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 9.44/3.82  tff(c_439, plain, (![A_13, C_47]: (k5_xboole_0(A_13, k5_xboole_0(A_13, C_47))=k5_xboole_0(k1_xboole_0, C_47))), inference(superposition, [status(thm), theory('equality')], [c_14, c_364])).
% 9.44/3.82  tff(c_453, plain, (![A_48, C_49]: (k5_xboole_0(A_48, k5_xboole_0(A_48, C_49))=C_49)), inference(demodulation, [status(thm), theory('equality')], [c_83, c_439])).
% 9.44/3.82  tff(c_1837, plain, (![A_87, B_88]: (k5_xboole_0(A_87, k4_xboole_0(A_87, B_88))=k3_xboole_0(A_87, B_88))), inference(superposition, [status(thm), theory('equality')], [c_6, c_453])).
% 9.44/3.82  tff(c_4, plain, (![B_4, A_3]: (k5_xboole_0(B_4, A_3)=k5_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 9.44/3.82  tff(c_1249, plain, (![B_79, A_80, B_81]: (k5_xboole_0(B_79, k5_xboole_0(A_80, B_81))=k5_xboole_0(A_80, k5_xboole_0(B_81, B_79)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_364])).
% 9.44/3.82  tff(c_1488, plain, (![A_28, B_79]: (k5_xboole_0(k1_xboole_0, k5_xboole_0(A_28, B_79))=k5_xboole_0(B_79, A_28))), inference(superposition, [status(thm), theory('equality')], [c_83, c_1249])).
% 9.44/3.82  tff(c_1843, plain, (![A_87, B_88]: (k5_xboole_0(k4_xboole_0(A_87, B_88), A_87)=k5_xboole_0(k1_xboole_0, k3_xboole_0(A_87, B_88)))), inference(superposition, [status(thm), theory('equality')], [c_1837, c_1488])).
% 9.44/3.82  tff(c_1923, plain, (![A_87, B_88]: (k5_xboole_0(k4_xboole_0(A_87, B_88), A_87)=k3_xboole_0(A_87, B_88))), inference(demodulation, [status(thm), theory('equality')], [c_83, c_1843])).
% 9.44/3.82  tff(c_16, plain, (![A_14, B_15]: (k5_xboole_0(A_14, k4_xboole_0(B_15, A_14))=k2_xboole_0(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_41])).
% 9.44/3.82  tff(c_6685, plain, (![A_154, B_155, C_156]: (k5_xboole_0(A_154, k5_xboole_0(k4_xboole_0(B_155, A_154), C_156))=k5_xboole_0(k2_xboole_0(A_154, B_155), C_156))), inference(superposition, [status(thm), theory('equality')], [c_16, c_364])).
% 9.44/3.82  tff(c_6796, plain, (![B_88, A_87]: (k5_xboole_0(k2_xboole_0(B_88, A_87), A_87)=k5_xboole_0(B_88, k3_xboole_0(A_87, B_88)))), inference(superposition, [status(thm), theory('equality')], [c_1923, c_6685])).
% 9.44/3.82  tff(c_7045, plain, (![B_161, A_162]: (k5_xboole_0(k2_xboole_0(B_161, A_162), A_162)=k4_xboole_0(B_161, A_162))), inference(demodulation, [status(thm), theory('equality')], [c_217, c_6796])).
% 9.44/3.82  tff(c_452, plain, (![A_13, C_47]: (k5_xboole_0(A_13, k5_xboole_0(A_13, C_47))=C_47)), inference(demodulation, [status(thm), theory('equality')], [c_83, c_439])).
% 9.44/3.82  tff(c_16547, plain, (![B_220, A_221]: (k5_xboole_0(k2_xboole_0(B_220, A_221), k4_xboole_0(B_220, A_221))=A_221)), inference(superposition, [status(thm), theory('equality')], [c_7045, c_452])).
% 9.44/3.82  tff(c_16681, plain, (![A_36, B_37]: (k5_xboole_0(k2_xboole_0(k1_tarski(A_36), k2_tarski(A_36, B_37)), k1_xboole_0)=k2_tarski(A_36, B_37))), inference(superposition, [status(thm), theory('equality')], [c_255, c_16547])).
% 9.44/3.82  tff(c_16715, plain, (![A_36, B_37]: (k1_enumset1(A_36, A_36, B_37)=k2_tarski(A_36, B_37))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_20, c_16681])).
% 9.44/3.82  tff(c_24, plain, (k1_enumset1('#skF_1', '#skF_1', '#skF_2')!=k2_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_50])).
% 9.44/3.82  tff(c_16719, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_16715, c_24])).
% 9.44/3.82  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.44/3.82  
% 9.44/3.82  Inference rules
% 9.44/3.82  ----------------------
% 9.44/3.82  #Ref     : 0
% 9.44/3.82  #Sup     : 4201
% 9.44/3.82  #Fact    : 0
% 9.44/3.82  #Define  : 0
% 9.44/3.82  #Split   : 0
% 9.44/3.82  #Chain   : 0
% 9.44/3.82  #Close   : 0
% 9.44/3.82  
% 9.44/3.82  Ordering : KBO
% 9.44/3.82  
% 9.44/3.82  Simplification rules
% 9.44/3.82  ----------------------
% 9.44/3.82  #Subsume      : 210
% 9.44/3.82  #Demod        : 3992
% 9.44/3.82  #Tautology    : 1895
% 9.44/3.82  #SimpNegUnit  : 0
% 9.44/3.82  #BackRed      : 2
% 9.44/3.82  
% 9.44/3.82  #Partial instantiations: 0
% 9.44/3.82  #Strategies tried      : 1
% 9.44/3.82  
% 9.44/3.82  Timing (in seconds)
% 9.44/3.82  ----------------------
% 9.44/3.82  Preprocessing        : 0.28
% 9.44/3.82  Parsing              : 0.14
% 9.44/3.82  CNF conversion       : 0.02
% 9.44/3.82  Main loop            : 2.79
% 9.44/3.82  Inferencing          : 0.56
% 9.44/3.82  Reduction            : 1.71
% 9.44/3.82  Demodulation         : 1.57
% 9.44/3.82  BG Simplification    : 0.08
% 9.44/3.82  Subsumption          : 0.33
% 9.44/3.82  Abstraction          : 0.12
% 9.44/3.82  MUC search           : 0.00
% 9.44/3.82  Cooper               : 0.00
% 9.44/3.82  Total                : 3.09
% 9.44/3.82  Index Insertion      : 0.00
% 9.44/3.82  Index Deletion       : 0.00
% 9.44/3.82  Index Matching       : 0.00
% 9.44/3.82  BG Taut test         : 0.00
%------------------------------------------------------------------------------

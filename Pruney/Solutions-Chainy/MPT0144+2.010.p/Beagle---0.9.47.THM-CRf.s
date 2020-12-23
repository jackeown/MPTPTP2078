%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:45:52 EST 2020

% Result     : Theorem 2.48s
% Output     : CNFRefutation 2.48s
% Verified   : 
% Statistics : Number of formulae       :   39 (  50 expanded)
%              Number of leaves         :   22 (  28 expanded)
%              Depth                    :    9
%              Number of atoms          :   23 (  34 expanded)
%              Number of equality atoms :   22 (  33 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k5_enumset1 > k3_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

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

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_35,axiom,(
    ! [A,B,C,D,E,F,G] : k5_enumset1(A,B,C,D,E,F,G) = k2_xboole_0(k2_tarski(A,B),k3_enumset1(C,D,E,F,G)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_enumset1)).

tff(f_29,axiom,(
    ! [A,B,C,D,E] : k3_enumset1(A,B,C,D,E) = k2_xboole_0(k1_enumset1(A,B,C),k2_tarski(D,E)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l57_enumset1)).

tff(f_31,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_xboole_0(k1_tarski(A),k1_tarski(B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).

tff(f_27,axiom,(
    ! [A,B,C] : k2_xboole_0(k2_xboole_0(A,B),C) = k2_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).

tff(f_33,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k2_xboole_0(k1_tarski(A),k2_tarski(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_enumset1)).

tff(f_38,negated_conjecture,(
    ~ ! [A,B,C,D,E,F,G] : k5_enumset1(A,B,C,D,E,F,G) = k2_xboole_0(k3_enumset1(A,B,C,D,E),k2_tarski(F,G)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_enumset1)).

tff(c_10,plain,(
    ! [G_20,E_18,C_16,D_17,F_19,A_14,B_15] : k2_xboole_0(k2_tarski(A_14,B_15),k3_enumset1(C_16,D_17,E_18,F_19,G_20)) = k5_enumset1(A_14,B_15,C_16,D_17,E_18,F_19,G_20) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_4,plain,(
    ! [B_5,D_7,A_4,E_8,C_6] : k2_xboole_0(k1_enumset1(A_4,B_5,C_6),k2_tarski(D_7,E_8)) = k3_enumset1(A_4,B_5,C_6,D_7,E_8) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_6,plain,(
    ! [A_9,B_10] : k2_xboole_0(k1_tarski(A_9),k1_tarski(B_10)) = k2_tarski(A_9,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_31,plain,(
    ! [A_26,B_27,C_28] : k2_xboole_0(k2_xboole_0(A_26,B_27),C_28) = k2_xboole_0(A_26,k2_xboole_0(B_27,C_28)) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_49,plain,(
    ! [A_9,B_10,C_28] : k2_xboole_0(k1_tarski(A_9),k2_xboole_0(k1_tarski(B_10),C_28)) = k2_xboole_0(k2_tarski(A_9,B_10),C_28) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_31])).

tff(c_8,plain,(
    ! [A_11,B_12,C_13] : k2_xboole_0(k1_tarski(A_11),k2_tarski(B_12,C_13)) = k1_enumset1(A_11,B_12,C_13) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_54,plain,(
    ! [A_29,B_30,C_31] : k2_xboole_0(k1_tarski(A_29),k2_xboole_0(k1_tarski(B_30),C_31)) = k2_xboole_0(k2_tarski(A_29,B_30),C_31) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_31])).

tff(c_123,plain,(
    ! [A_44,A_45,B_46,C_47] : k2_xboole_0(k2_tarski(A_44,A_45),k2_tarski(B_46,C_47)) = k2_xboole_0(k1_tarski(A_44),k1_enumset1(A_45,B_46,C_47)) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_54])).

tff(c_46,plain,(
    ! [A_11,B_12,C_13,C_28] : k2_xboole_0(k1_tarski(A_11),k2_xboole_0(k2_tarski(B_12,C_13),C_28)) = k2_xboole_0(k1_enumset1(A_11,B_12,C_13),C_28) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_31])).

tff(c_129,plain,(
    ! [C_47,A_45,A_44,B_46,A_11] : k2_xboole_0(k1_tarski(A_11),k2_xboole_0(k1_tarski(A_44),k1_enumset1(A_45,B_46,C_47))) = k2_xboole_0(k1_enumset1(A_11,A_44,A_45),k2_tarski(B_46,C_47)) ),
    inference(superposition,[status(thm),theory(equality)],[c_123,c_46])).

tff(c_183,plain,(
    ! [A_57,A_60,A_58,B_56,C_59] : k2_xboole_0(k2_tarski(A_58,A_60),k1_enumset1(A_57,B_56,C_59)) = k3_enumset1(A_58,A_60,A_57,B_56,C_59) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_49,c_129])).

tff(c_2,plain,(
    ! [A_1,B_2,C_3] : k2_xboole_0(k2_xboole_0(A_1,B_2),C_3) = k2_xboole_0(A_1,k2_xboole_0(B_2,C_3)) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_291,plain,(
    ! [A_81,C_84,B_79,A_83,A_80,C_82] : k2_xboole_0(k2_tarski(A_80,A_81),k2_xboole_0(k1_enumset1(A_83,B_79,C_84),C_82)) = k2_xboole_0(k3_enumset1(A_80,A_81,A_83,B_79,C_84),C_82) ),
    inference(superposition,[status(thm),theory(equality)],[c_183,c_2])).

tff(c_318,plain,(
    ! [B_5,D_7,A_4,A_81,E_8,C_6,A_80] : k2_xboole_0(k3_enumset1(A_80,A_81,A_4,B_5,C_6),k2_tarski(D_7,E_8)) = k2_xboole_0(k2_tarski(A_80,A_81),k3_enumset1(A_4,B_5,C_6,D_7,E_8)) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_291])).

tff(c_323,plain,(
    ! [B_5,D_7,A_4,A_81,E_8,C_6,A_80] : k2_xboole_0(k3_enumset1(A_80,A_81,A_4,B_5,C_6),k2_tarski(D_7,E_8)) = k5_enumset1(A_80,A_81,A_4,B_5,C_6,D_7,E_8) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_318])).

tff(c_12,plain,(
    k2_xboole_0(k3_enumset1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5'),k2_tarski('#skF_6','#skF_7')) != k5_enumset1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_451,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_323,c_12])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:03:20 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.48/1.43  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.48/1.43  
% 2.48/1.43  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.48/1.44  %$ k5_enumset1 > k3_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.48/1.44  
% 2.48/1.44  %Foreground sorts:
% 2.48/1.44  
% 2.48/1.44  
% 2.48/1.44  %Background operators:
% 2.48/1.44  
% 2.48/1.44  
% 2.48/1.44  %Foreground operators:
% 2.48/1.44  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.48/1.44  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.48/1.44  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.48/1.44  tff('#skF_7', type, '#skF_7': $i).
% 2.48/1.44  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.48/1.44  tff('#skF_5', type, '#skF_5': $i).
% 2.48/1.44  tff('#skF_6', type, '#skF_6': $i).
% 2.48/1.44  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.48/1.44  tff('#skF_2', type, '#skF_2': $i).
% 2.48/1.44  tff('#skF_3', type, '#skF_3': $i).
% 2.48/1.44  tff('#skF_1', type, '#skF_1': $i).
% 2.48/1.44  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.48/1.44  tff('#skF_4', type, '#skF_4': $i).
% 2.48/1.44  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.48/1.44  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.48/1.44  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.48/1.44  
% 2.48/1.45  tff(f_35, axiom, (![A, B, C, D, E, F, G]: (k5_enumset1(A, B, C, D, E, F, G) = k2_xboole_0(k2_tarski(A, B), k3_enumset1(C, D, E, F, G)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t57_enumset1)).
% 2.48/1.45  tff(f_29, axiom, (![A, B, C, D, E]: (k3_enumset1(A, B, C, D, E) = k2_xboole_0(k1_enumset1(A, B, C), k2_tarski(D, E)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l57_enumset1)).
% 2.48/1.45  tff(f_31, axiom, (![A, B]: (k2_tarski(A, B) = k2_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_enumset1)).
% 2.48/1.45  tff(f_27, axiom, (![A, B, C]: (k2_xboole_0(k2_xboole_0(A, B), C) = k2_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_1)).
% 2.48/1.45  tff(f_33, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k2_xboole_0(k1_tarski(A), k2_tarski(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t42_enumset1)).
% 2.48/1.45  tff(f_38, negated_conjecture, ~(![A, B, C, D, E, F, G]: (k5_enumset1(A, B, C, D, E, F, G) = k2_xboole_0(k3_enumset1(A, B, C, D, E), k2_tarski(F, G)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_enumset1)).
% 2.48/1.45  tff(c_10, plain, (![G_20, E_18, C_16, D_17, F_19, A_14, B_15]: (k2_xboole_0(k2_tarski(A_14, B_15), k3_enumset1(C_16, D_17, E_18, F_19, G_20))=k5_enumset1(A_14, B_15, C_16, D_17, E_18, F_19, G_20))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.48/1.45  tff(c_4, plain, (![B_5, D_7, A_4, E_8, C_6]: (k2_xboole_0(k1_enumset1(A_4, B_5, C_6), k2_tarski(D_7, E_8))=k3_enumset1(A_4, B_5, C_6, D_7, E_8))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.48/1.45  tff(c_6, plain, (![A_9, B_10]: (k2_xboole_0(k1_tarski(A_9), k1_tarski(B_10))=k2_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.48/1.45  tff(c_31, plain, (![A_26, B_27, C_28]: (k2_xboole_0(k2_xboole_0(A_26, B_27), C_28)=k2_xboole_0(A_26, k2_xboole_0(B_27, C_28)))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.48/1.45  tff(c_49, plain, (![A_9, B_10, C_28]: (k2_xboole_0(k1_tarski(A_9), k2_xboole_0(k1_tarski(B_10), C_28))=k2_xboole_0(k2_tarski(A_9, B_10), C_28))), inference(superposition, [status(thm), theory('equality')], [c_6, c_31])).
% 2.48/1.45  tff(c_8, plain, (![A_11, B_12, C_13]: (k2_xboole_0(k1_tarski(A_11), k2_tarski(B_12, C_13))=k1_enumset1(A_11, B_12, C_13))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.48/1.45  tff(c_54, plain, (![A_29, B_30, C_31]: (k2_xboole_0(k1_tarski(A_29), k2_xboole_0(k1_tarski(B_30), C_31))=k2_xboole_0(k2_tarski(A_29, B_30), C_31))), inference(superposition, [status(thm), theory('equality')], [c_6, c_31])).
% 2.48/1.45  tff(c_123, plain, (![A_44, A_45, B_46, C_47]: (k2_xboole_0(k2_tarski(A_44, A_45), k2_tarski(B_46, C_47))=k2_xboole_0(k1_tarski(A_44), k1_enumset1(A_45, B_46, C_47)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_54])).
% 2.48/1.45  tff(c_46, plain, (![A_11, B_12, C_13, C_28]: (k2_xboole_0(k1_tarski(A_11), k2_xboole_0(k2_tarski(B_12, C_13), C_28))=k2_xboole_0(k1_enumset1(A_11, B_12, C_13), C_28))), inference(superposition, [status(thm), theory('equality')], [c_8, c_31])).
% 2.48/1.45  tff(c_129, plain, (![C_47, A_45, A_44, B_46, A_11]: (k2_xboole_0(k1_tarski(A_11), k2_xboole_0(k1_tarski(A_44), k1_enumset1(A_45, B_46, C_47)))=k2_xboole_0(k1_enumset1(A_11, A_44, A_45), k2_tarski(B_46, C_47)))), inference(superposition, [status(thm), theory('equality')], [c_123, c_46])).
% 2.48/1.45  tff(c_183, plain, (![A_57, A_60, A_58, B_56, C_59]: (k2_xboole_0(k2_tarski(A_58, A_60), k1_enumset1(A_57, B_56, C_59))=k3_enumset1(A_58, A_60, A_57, B_56, C_59))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_49, c_129])).
% 2.48/1.45  tff(c_2, plain, (![A_1, B_2, C_3]: (k2_xboole_0(k2_xboole_0(A_1, B_2), C_3)=k2_xboole_0(A_1, k2_xboole_0(B_2, C_3)))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.48/1.45  tff(c_291, plain, (![A_81, C_84, B_79, A_83, A_80, C_82]: (k2_xboole_0(k2_tarski(A_80, A_81), k2_xboole_0(k1_enumset1(A_83, B_79, C_84), C_82))=k2_xboole_0(k3_enumset1(A_80, A_81, A_83, B_79, C_84), C_82))), inference(superposition, [status(thm), theory('equality')], [c_183, c_2])).
% 2.48/1.45  tff(c_318, plain, (![B_5, D_7, A_4, A_81, E_8, C_6, A_80]: (k2_xboole_0(k3_enumset1(A_80, A_81, A_4, B_5, C_6), k2_tarski(D_7, E_8))=k2_xboole_0(k2_tarski(A_80, A_81), k3_enumset1(A_4, B_5, C_6, D_7, E_8)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_291])).
% 2.48/1.45  tff(c_323, plain, (![B_5, D_7, A_4, A_81, E_8, C_6, A_80]: (k2_xboole_0(k3_enumset1(A_80, A_81, A_4, B_5, C_6), k2_tarski(D_7, E_8))=k5_enumset1(A_80, A_81, A_4, B_5, C_6, D_7, E_8))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_318])).
% 2.48/1.45  tff(c_12, plain, (k2_xboole_0(k3_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5'), k2_tarski('#skF_6', '#skF_7'))!=k5_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.48/1.45  tff(c_451, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_323, c_12])).
% 2.48/1.45  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.48/1.45  
% 2.48/1.45  Inference rules
% 2.48/1.45  ----------------------
% 2.48/1.45  #Ref     : 0
% 2.48/1.45  #Sup     : 109
% 2.48/1.45  #Fact    : 0
% 2.48/1.45  #Define  : 0
% 2.48/1.45  #Split   : 0
% 2.48/1.45  #Chain   : 0
% 2.48/1.45  #Close   : 0
% 2.48/1.45  
% 2.48/1.45  Ordering : KBO
% 2.48/1.45  
% 2.48/1.45  Simplification rules
% 2.48/1.45  ----------------------
% 2.48/1.45  #Subsume      : 0
% 2.48/1.45  #Demod        : 85
% 2.48/1.45  #Tautology    : 65
% 2.48/1.45  #SimpNegUnit  : 0
% 2.48/1.45  #BackRed      : 2
% 2.48/1.45  
% 2.48/1.45  #Partial instantiations: 0
% 2.48/1.45  #Strategies tried      : 1
% 2.48/1.45  
% 2.48/1.45  Timing (in seconds)
% 2.48/1.45  ----------------------
% 2.78/1.45  Preprocessing        : 0.32
% 2.78/1.45  Parsing              : 0.17
% 2.78/1.45  CNF conversion       : 0.02
% 2.78/1.45  Main loop            : 0.32
% 2.78/1.45  Inferencing          : 0.14
% 2.78/1.45  Reduction            : 0.11
% 2.78/1.45  Demodulation         : 0.09
% 2.78/1.45  BG Simplification    : 0.02
% 2.78/1.45  Subsumption          : 0.04
% 2.78/1.45  Abstraction          : 0.03
% 2.78/1.45  MUC search           : 0.00
% 2.78/1.45  Cooper               : 0.00
% 2.78/1.45  Total                : 0.67
% 2.78/1.45  Index Insertion      : 0.00
% 2.78/1.45  Index Deletion       : 0.00
% 2.78/1.45  Index Matching       : 0.00
% 2.78/1.45  BG Taut test         : 0.00
%------------------------------------------------------------------------------

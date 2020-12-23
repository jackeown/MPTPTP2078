%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:45:54 EST 2020

% Result     : Theorem 2.46s
% Output     : CNFRefutation 2.46s
% Verified   : 
% Statistics : Number of formulae       :   42 (  49 expanded)
%              Number of leaves         :   24 (  28 expanded)
%              Depth                    :    9
%              Number of atoms          :   25 (  32 expanded)
%              Number of equality atoms :   24 (  31 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k5_enumset1 > k4_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

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

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

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

tff(f_37,axiom,(
    ! [A,B,C,D,E,F,G] : k5_enumset1(A,B,C,D,E,F,G) = k2_xboole_0(k1_enumset1(A,B,C),k2_enumset1(D,E,F,G)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t58_enumset1)).

tff(f_35,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k1_tarski(A),k1_enumset1(B,C,D)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_enumset1)).

tff(f_33,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k2_xboole_0(k1_tarski(A),k2_tarski(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_enumset1)).

tff(f_31,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_xboole_0(k1_tarski(A),k1_tarski(B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).

tff(f_27,axiom,(
    ! [A,B,C] : k2_xboole_0(k2_xboole_0(A,B),C) = k2_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).

tff(f_29,axiom,(
    ! [A,B,C,D,E,F] : k4_enumset1(A,B,C,D,E,F) = k2_xboole_0(k1_enumset1(A,B,C),k1_enumset1(D,E,F)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l62_enumset1)).

tff(f_40,negated_conjecture,(
    ~ ! [A,B,C,D,E,F,G] : k5_enumset1(A,B,C,D,E,F,G) = k2_xboole_0(k4_enumset1(A,B,C,D,E,F),k1_tarski(G)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_enumset1)).

tff(c_12,plain,(
    ! [A_19,C_21,D_22,B_20,F_24,E_23,G_25] : k2_xboole_0(k1_enumset1(A_19,B_20,C_21),k2_enumset1(D_22,E_23,F_24,G_25)) = k5_enumset1(A_19,B_20,C_21,D_22,E_23,F_24,G_25) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_10,plain,(
    ! [A_15,B_16,C_17,D_18] : k2_xboole_0(k1_tarski(A_15),k1_enumset1(B_16,C_17,D_18)) = k2_enumset1(A_15,B_16,C_17,D_18) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_8,plain,(
    ! [A_12,B_13,C_14] : k2_xboole_0(k1_tarski(A_12),k2_tarski(B_13,C_14)) = k1_enumset1(A_12,B_13,C_14) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_6,plain,(
    ! [A_10,B_11] : k2_xboole_0(k1_tarski(A_10),k1_tarski(B_11)) = k2_tarski(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_33,plain,(
    ! [A_31,B_32,C_33] : k2_xboole_0(k2_xboole_0(A_31,B_32),C_33) = k2_xboole_0(A_31,k2_xboole_0(B_32,C_33)) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_68,plain,(
    ! [A_38,B_39,C_40] : k2_xboole_0(k1_tarski(A_38),k2_xboole_0(k1_tarski(B_39),C_40)) = k2_xboole_0(k2_tarski(A_38,B_39),C_40) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_33])).

tff(c_92,plain,(
    ! [A_38,A_10,B_11] : k2_xboole_0(k2_tarski(A_38,A_10),k1_tarski(B_11)) = k2_xboole_0(k1_tarski(A_38),k2_tarski(A_10,B_11)) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_68])).

tff(c_97,plain,(
    ! [A_38,A_10,B_11] : k2_xboole_0(k2_tarski(A_38,A_10),k1_tarski(B_11)) = k1_enumset1(A_38,A_10,B_11) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_92])).

tff(c_134,plain,(
    ! [A_54,B_55,C_56,C_57] : k2_xboole_0(k1_tarski(A_54),k2_xboole_0(k2_tarski(B_55,C_56),C_57)) = k2_xboole_0(k1_enumset1(A_54,B_55,C_56),C_57) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_33])).

tff(c_152,plain,(
    ! [A_54,A_38,A_10,B_11] : k2_xboole_0(k1_enumset1(A_54,A_38,A_10),k1_tarski(B_11)) = k2_xboole_0(k1_tarski(A_54),k1_enumset1(A_38,A_10,B_11)) ),
    inference(superposition,[status(thm),theory(equality)],[c_97,c_134])).

tff(c_156,plain,(
    ! [A_54,A_38,A_10,B_11] : k2_xboole_0(k1_enumset1(A_54,A_38,A_10),k1_tarski(B_11)) = k2_enumset1(A_54,A_38,A_10,B_11) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_152])).

tff(c_98,plain,(
    ! [A_46,D_44,C_43,F_42,E_45,B_41] : k2_xboole_0(k1_enumset1(A_46,B_41,C_43),k1_enumset1(D_44,E_45,F_42)) = k4_enumset1(A_46,B_41,C_43,D_44,E_45,F_42) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_2,plain,(
    ! [A_1,B_2,C_3] : k2_xboole_0(k2_xboole_0(A_1,B_2),C_3) = k2_xboole_0(A_1,k2_xboole_0(B_2,C_3)) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_398,plain,(
    ! [E_115,B_121,F_117,A_120,C_119,D_118,C_116] : k2_xboole_0(k1_enumset1(A_120,B_121,C_116),k2_xboole_0(k1_enumset1(D_118,E_115,F_117),C_119)) = k2_xboole_0(k4_enumset1(A_120,B_121,C_116,D_118,E_115,F_117),C_119) ),
    inference(superposition,[status(thm),theory(equality)],[c_98,c_2])).

tff(c_428,plain,(
    ! [B_11,A_10,B_121,A_120,A_38,C_116,A_54] : k2_xboole_0(k4_enumset1(A_120,B_121,C_116,A_54,A_38,A_10),k1_tarski(B_11)) = k2_xboole_0(k1_enumset1(A_120,B_121,C_116),k2_enumset1(A_54,A_38,A_10,B_11)) ),
    inference(superposition,[status(thm),theory(equality)],[c_156,c_398])).

tff(c_436,plain,(
    ! [B_11,A_10,B_121,A_120,A_38,C_116,A_54] : k2_xboole_0(k4_enumset1(A_120,B_121,C_116,A_54,A_38,A_10),k1_tarski(B_11)) = k5_enumset1(A_120,B_121,C_116,A_54,A_38,A_10,B_11) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_428])).

tff(c_14,plain,(
    k2_xboole_0(k4_enumset1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),k1_tarski('#skF_7')) != k5_enumset1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_457,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_436,c_14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.35  % Computer   : n010.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 10:56:44 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.46/1.33  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.46/1.33  
% 2.46/1.33  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.46/1.33  %$ k5_enumset1 > k4_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.46/1.33  
% 2.46/1.33  %Foreground sorts:
% 2.46/1.33  
% 2.46/1.33  
% 2.46/1.33  %Background operators:
% 2.46/1.33  
% 2.46/1.33  
% 2.46/1.33  %Foreground operators:
% 2.46/1.33  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.46/1.33  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.46/1.33  tff('#skF_7', type, '#skF_7': $i).
% 2.46/1.33  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.46/1.33  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.46/1.33  tff('#skF_5', type, '#skF_5': $i).
% 2.46/1.33  tff('#skF_6', type, '#skF_6': $i).
% 2.46/1.33  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.46/1.33  tff('#skF_2', type, '#skF_2': $i).
% 2.46/1.33  tff('#skF_3', type, '#skF_3': $i).
% 2.46/1.33  tff('#skF_1', type, '#skF_1': $i).
% 2.46/1.33  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.46/1.33  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.46/1.33  tff('#skF_4', type, '#skF_4': $i).
% 2.46/1.33  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.46/1.33  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.46/1.33  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.46/1.33  
% 2.46/1.34  tff(f_37, axiom, (![A, B, C, D, E, F, G]: (k5_enumset1(A, B, C, D, E, F, G) = k2_xboole_0(k1_enumset1(A, B, C), k2_enumset1(D, E, F, G)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t58_enumset1)).
% 2.46/1.34  tff(f_35, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k1_tarski(A), k1_enumset1(B, C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_enumset1)).
% 2.46/1.34  tff(f_33, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k2_xboole_0(k1_tarski(A), k2_tarski(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t42_enumset1)).
% 2.46/1.34  tff(f_31, axiom, (![A, B]: (k2_tarski(A, B) = k2_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_enumset1)).
% 2.46/1.34  tff(f_27, axiom, (![A, B, C]: (k2_xboole_0(k2_xboole_0(A, B), C) = k2_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_1)).
% 2.46/1.34  tff(f_29, axiom, (![A, B, C, D, E, F]: (k4_enumset1(A, B, C, D, E, F) = k2_xboole_0(k1_enumset1(A, B, C), k1_enumset1(D, E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l62_enumset1)).
% 2.46/1.34  tff(f_40, negated_conjecture, ~(![A, B, C, D, E, F, G]: (k5_enumset1(A, B, C, D, E, F, G) = k2_xboole_0(k4_enumset1(A, B, C, D, E, F), k1_tarski(G)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_enumset1)).
% 2.46/1.34  tff(c_12, plain, (![A_19, C_21, D_22, B_20, F_24, E_23, G_25]: (k2_xboole_0(k1_enumset1(A_19, B_20, C_21), k2_enumset1(D_22, E_23, F_24, G_25))=k5_enumset1(A_19, B_20, C_21, D_22, E_23, F_24, G_25))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.46/1.34  tff(c_10, plain, (![A_15, B_16, C_17, D_18]: (k2_xboole_0(k1_tarski(A_15), k1_enumset1(B_16, C_17, D_18))=k2_enumset1(A_15, B_16, C_17, D_18))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.46/1.34  tff(c_8, plain, (![A_12, B_13, C_14]: (k2_xboole_0(k1_tarski(A_12), k2_tarski(B_13, C_14))=k1_enumset1(A_12, B_13, C_14))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.46/1.34  tff(c_6, plain, (![A_10, B_11]: (k2_xboole_0(k1_tarski(A_10), k1_tarski(B_11))=k2_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.46/1.34  tff(c_33, plain, (![A_31, B_32, C_33]: (k2_xboole_0(k2_xboole_0(A_31, B_32), C_33)=k2_xboole_0(A_31, k2_xboole_0(B_32, C_33)))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.46/1.34  tff(c_68, plain, (![A_38, B_39, C_40]: (k2_xboole_0(k1_tarski(A_38), k2_xboole_0(k1_tarski(B_39), C_40))=k2_xboole_0(k2_tarski(A_38, B_39), C_40))), inference(superposition, [status(thm), theory('equality')], [c_6, c_33])).
% 2.46/1.34  tff(c_92, plain, (![A_38, A_10, B_11]: (k2_xboole_0(k2_tarski(A_38, A_10), k1_tarski(B_11))=k2_xboole_0(k1_tarski(A_38), k2_tarski(A_10, B_11)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_68])).
% 2.46/1.34  tff(c_97, plain, (![A_38, A_10, B_11]: (k2_xboole_0(k2_tarski(A_38, A_10), k1_tarski(B_11))=k1_enumset1(A_38, A_10, B_11))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_92])).
% 2.46/1.34  tff(c_134, plain, (![A_54, B_55, C_56, C_57]: (k2_xboole_0(k1_tarski(A_54), k2_xboole_0(k2_tarski(B_55, C_56), C_57))=k2_xboole_0(k1_enumset1(A_54, B_55, C_56), C_57))), inference(superposition, [status(thm), theory('equality')], [c_8, c_33])).
% 2.46/1.34  tff(c_152, plain, (![A_54, A_38, A_10, B_11]: (k2_xboole_0(k1_enumset1(A_54, A_38, A_10), k1_tarski(B_11))=k2_xboole_0(k1_tarski(A_54), k1_enumset1(A_38, A_10, B_11)))), inference(superposition, [status(thm), theory('equality')], [c_97, c_134])).
% 2.46/1.34  tff(c_156, plain, (![A_54, A_38, A_10, B_11]: (k2_xboole_0(k1_enumset1(A_54, A_38, A_10), k1_tarski(B_11))=k2_enumset1(A_54, A_38, A_10, B_11))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_152])).
% 2.46/1.34  tff(c_98, plain, (![A_46, D_44, C_43, F_42, E_45, B_41]: (k2_xboole_0(k1_enumset1(A_46, B_41, C_43), k1_enumset1(D_44, E_45, F_42))=k4_enumset1(A_46, B_41, C_43, D_44, E_45, F_42))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.46/1.34  tff(c_2, plain, (![A_1, B_2, C_3]: (k2_xboole_0(k2_xboole_0(A_1, B_2), C_3)=k2_xboole_0(A_1, k2_xboole_0(B_2, C_3)))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.46/1.34  tff(c_398, plain, (![E_115, B_121, F_117, A_120, C_119, D_118, C_116]: (k2_xboole_0(k1_enumset1(A_120, B_121, C_116), k2_xboole_0(k1_enumset1(D_118, E_115, F_117), C_119))=k2_xboole_0(k4_enumset1(A_120, B_121, C_116, D_118, E_115, F_117), C_119))), inference(superposition, [status(thm), theory('equality')], [c_98, c_2])).
% 2.46/1.34  tff(c_428, plain, (![B_11, A_10, B_121, A_120, A_38, C_116, A_54]: (k2_xboole_0(k4_enumset1(A_120, B_121, C_116, A_54, A_38, A_10), k1_tarski(B_11))=k2_xboole_0(k1_enumset1(A_120, B_121, C_116), k2_enumset1(A_54, A_38, A_10, B_11)))), inference(superposition, [status(thm), theory('equality')], [c_156, c_398])).
% 2.46/1.34  tff(c_436, plain, (![B_11, A_10, B_121, A_120, A_38, C_116, A_54]: (k2_xboole_0(k4_enumset1(A_120, B_121, C_116, A_54, A_38, A_10), k1_tarski(B_11))=k5_enumset1(A_120, B_121, C_116, A_54, A_38, A_10, B_11))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_428])).
% 2.46/1.34  tff(c_14, plain, (k2_xboole_0(k4_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), k1_tarski('#skF_7'))!=k5_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.46/1.34  tff(c_457, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_436, c_14])).
% 2.46/1.34  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.46/1.34  
% 2.46/1.34  Inference rules
% 2.46/1.34  ----------------------
% 2.46/1.34  #Ref     : 0
% 2.46/1.34  #Sup     : 112
% 2.46/1.34  #Fact    : 0
% 2.46/1.34  #Define  : 0
% 2.46/1.34  #Split   : 0
% 2.46/1.34  #Chain   : 0
% 2.46/1.34  #Close   : 0
% 2.46/1.34  
% 2.46/1.34  Ordering : KBO
% 2.46/1.34  
% 2.46/1.34  Simplification rules
% 2.46/1.34  ----------------------
% 2.46/1.34  #Subsume      : 0
% 2.46/1.34  #Demod        : 65
% 2.46/1.34  #Tautology    : 63
% 2.46/1.34  #SimpNegUnit  : 0
% 2.46/1.34  #BackRed      : 1
% 2.46/1.34  
% 2.46/1.34  #Partial instantiations: 0
% 2.46/1.34  #Strategies tried      : 1
% 2.46/1.34  
% 2.46/1.34  Timing (in seconds)
% 2.46/1.35  ----------------------
% 2.46/1.35  Preprocessing        : 0.27
% 2.46/1.35  Parsing              : 0.15
% 2.46/1.35  CNF conversion       : 0.02
% 2.46/1.35  Main loop            : 0.30
% 2.46/1.35  Inferencing          : 0.13
% 2.46/1.35  Reduction            : 0.10
% 2.46/1.35  Demodulation         : 0.08
% 2.46/1.35  BG Simplification    : 0.02
% 2.46/1.35  Subsumption          : 0.04
% 2.46/1.35  Abstraction          : 0.02
% 2.46/1.35  MUC search           : 0.00
% 2.46/1.35  Cooper               : 0.00
% 2.46/1.35  Total                : 0.60
% 2.46/1.35  Index Insertion      : 0.00
% 2.46/1.35  Index Deletion       : 0.00
% 2.46/1.35  Index Matching       : 0.00
% 2.46/1.35  BG Taut test         : 0.00
%------------------------------------------------------------------------------

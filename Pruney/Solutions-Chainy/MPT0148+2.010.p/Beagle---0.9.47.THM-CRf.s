%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:45:58 EST 2020

% Result     : Theorem 4.50s
% Output     : CNFRefutation 4.50s
% Verified   : 
% Statistics : Number of formulae       :   43 (  44 expanded)
%              Number of leaves         :   28 (  29 expanded)
%              Depth                    :    7
%              Number of atoms          :   22 (  23 expanded)
%              Number of equality atoms :   21 (  22 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_8 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

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

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

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

tff(f_41,axiom,(
    ! [A,B,C,D,E,F,G,H] : k6_enumset1(A,B,C,D,E,F,G,H) = k2_xboole_0(k1_tarski(A),k5_enumset1(B,C,D,E,F,G,H)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_enumset1)).

tff(f_39,axiom,(
    ! [A,B,C,D,E,F,G] : k5_enumset1(A,B,C,D,E,F,G) = k2_xboole_0(k1_tarski(A),k4_enumset1(B,C,D,E,F,G)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_enumset1)).

tff(f_37,axiom,(
    ! [A,B,C,D,E,F] : k4_enumset1(A,B,C,D,E,F) = k2_xboole_0(k1_tarski(A),k3_enumset1(B,C,D,E,F)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_enumset1)).

tff(f_33,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_xboole_0(k1_tarski(A),k1_tarski(B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).

tff(f_27,axiom,(
    ! [A,B,C] : k2_xboole_0(k2_xboole_0(A,B),C) = k2_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).

tff(f_35,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k2_xboole_0(k1_tarski(A),k2_tarski(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_enumset1)).

tff(f_44,negated_conjecture,(
    ~ ! [A,B,C,D,E,F,G,H] : k6_enumset1(A,B,C,D,E,F,G,H) = k2_xboole_0(k1_enumset1(A,B,C),k3_enumset1(D,E,F,G,H)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_enumset1)).

tff(c_16,plain,(
    ! [C_29,D_30,B_28,G_33,F_32,A_27,E_31,H_34] : k2_xboole_0(k1_tarski(A_27),k5_enumset1(B_28,C_29,D_30,E_31,F_32,G_33,H_34)) = k6_enumset1(A_27,B_28,C_29,D_30,E_31,F_32,G_33,H_34) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_14,plain,(
    ! [C_22,D_23,A_20,B_21,F_25,G_26,E_24] : k2_xboole_0(k1_tarski(A_20),k4_enumset1(B_21,C_22,D_23,E_24,F_25,G_26)) = k5_enumset1(A_20,B_21,C_22,D_23,E_24,F_25,G_26) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_12,plain,(
    ! [E_18,C_16,D_17,F_19,A_14,B_15] : k2_xboole_0(k1_tarski(A_14),k3_enumset1(B_15,C_16,D_17,E_18,F_19)) = k4_enumset1(A_14,B_15,C_16,D_17,E_18,F_19) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_8,plain,(
    ! [A_9,B_10] : k2_xboole_0(k1_tarski(A_9),k1_tarski(B_10)) = k2_tarski(A_9,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_65,plain,(
    ! [A_42,B_43,C_44] : k2_xboole_0(k2_xboole_0(A_42,B_43),C_44) = k2_xboole_0(A_42,k2_xboole_0(B_43,C_44)) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_142,plain,(
    ! [A_57,B_58,C_59] : k2_xboole_0(k1_tarski(A_57),k2_xboole_0(k1_tarski(B_58),C_59)) = k2_xboole_0(k2_tarski(A_57,B_58),C_59) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_65])).

tff(c_160,plain,(
    ! [A_57,E_18,C_16,D_17,F_19,A_14,B_15] : k2_xboole_0(k2_tarski(A_57,A_14),k3_enumset1(B_15,C_16,D_17,E_18,F_19)) = k2_xboole_0(k1_tarski(A_57),k4_enumset1(A_14,B_15,C_16,D_17,E_18,F_19)) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_142])).

tff(c_1164,plain,(
    ! [B_148,C_147,E_144,A_149,F_145,A_150,D_146] : k2_xboole_0(k2_tarski(A_150,A_149),k3_enumset1(B_148,C_147,D_146,E_144,F_145)) = k5_enumset1(A_150,A_149,B_148,C_147,D_146,E_144,F_145) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_160])).

tff(c_85,plain,(
    ! [A_45,B_46,C_47] : k2_xboole_0(k1_tarski(A_45),k2_tarski(B_46,C_47)) = k1_enumset1(A_45,B_46,C_47) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_2,plain,(
    ! [A_1,B_2,C_3] : k2_xboole_0(k2_xboole_0(A_1,B_2),C_3) = k2_xboole_0(A_1,k2_xboole_0(B_2,C_3)) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_91,plain,(
    ! [A_45,B_46,C_47,C_3] : k2_xboole_0(k1_tarski(A_45),k2_xboole_0(k2_tarski(B_46,C_47),C_3)) = k2_xboole_0(k1_enumset1(A_45,B_46,C_47),C_3) ),
    inference(superposition,[status(thm),theory(equality)],[c_85,c_2])).

tff(c_1191,plain,(
    ! [B_148,C_147,E_144,A_45,A_149,F_145,A_150,D_146] : k2_xboole_0(k1_enumset1(A_45,A_150,A_149),k3_enumset1(B_148,C_147,D_146,E_144,F_145)) = k2_xboole_0(k1_tarski(A_45),k5_enumset1(A_150,A_149,B_148,C_147,D_146,E_144,F_145)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1164,c_91])).

tff(c_1203,plain,(
    ! [B_148,C_147,E_144,A_45,A_149,F_145,A_150,D_146] : k2_xboole_0(k1_enumset1(A_45,A_150,A_149),k3_enumset1(B_148,C_147,D_146,E_144,F_145)) = k6_enumset1(A_45,A_150,A_149,B_148,C_147,D_146,E_144,F_145) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_1191])).

tff(c_18,plain,(
    k2_xboole_0(k1_enumset1('#skF_1','#skF_2','#skF_3'),k3_enumset1('#skF_4','#skF_5','#skF_6','#skF_7','#skF_8')) != k6_enumset1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_1887,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1203,c_18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:52:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.50/1.86  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.50/1.86  
% 4.50/1.86  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.50/1.86  %$ k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_8 > #skF_4
% 4.50/1.86  
% 4.50/1.86  %Foreground sorts:
% 4.50/1.86  
% 4.50/1.86  
% 4.50/1.86  %Background operators:
% 4.50/1.86  
% 4.50/1.86  
% 4.50/1.86  %Foreground operators:
% 4.50/1.86  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.50/1.86  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.50/1.86  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.50/1.86  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 4.50/1.86  tff('#skF_7', type, '#skF_7': $i).
% 4.50/1.86  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 4.50/1.86  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.50/1.86  tff('#skF_5', type, '#skF_5': $i).
% 4.50/1.86  tff('#skF_6', type, '#skF_6': $i).
% 4.50/1.86  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.50/1.86  tff('#skF_2', type, '#skF_2': $i).
% 4.50/1.86  tff('#skF_3', type, '#skF_3': $i).
% 4.50/1.86  tff('#skF_1', type, '#skF_1': $i).
% 4.50/1.86  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 4.50/1.86  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 4.50/1.86  tff('#skF_8', type, '#skF_8': $i).
% 4.50/1.86  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.50/1.86  tff('#skF_4', type, '#skF_4': $i).
% 4.50/1.86  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.50/1.86  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.50/1.86  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 4.50/1.86  
% 4.50/1.88  tff(f_41, axiom, (![A, B, C, D, E, F, G, H]: (k6_enumset1(A, B, C, D, E, F, G, H) = k2_xboole_0(k1_tarski(A), k5_enumset1(B, C, D, E, F, G, H)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t62_enumset1)).
% 4.50/1.88  tff(f_39, axiom, (![A, B, C, D, E, F, G]: (k5_enumset1(A, B, C, D, E, F, G) = k2_xboole_0(k1_tarski(A), k4_enumset1(B, C, D, E, F, G)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t56_enumset1)).
% 4.50/1.88  tff(f_37, axiom, (![A, B, C, D, E, F]: (k4_enumset1(A, B, C, D, E, F) = k2_xboole_0(k1_tarski(A), k3_enumset1(B, C, D, E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_enumset1)).
% 4.50/1.88  tff(f_33, axiom, (![A, B]: (k2_tarski(A, B) = k2_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_enumset1)).
% 4.50/1.88  tff(f_27, axiom, (![A, B, C]: (k2_xboole_0(k2_xboole_0(A, B), C) = k2_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_1)).
% 4.50/1.88  tff(f_35, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k2_xboole_0(k1_tarski(A), k2_tarski(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t42_enumset1)).
% 4.50/1.88  tff(f_44, negated_conjecture, ~(![A, B, C, D, E, F, G, H]: (k6_enumset1(A, B, C, D, E, F, G, H) = k2_xboole_0(k1_enumset1(A, B, C), k3_enumset1(D, E, F, G, H)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_enumset1)).
% 4.50/1.88  tff(c_16, plain, (![C_29, D_30, B_28, G_33, F_32, A_27, E_31, H_34]: (k2_xboole_0(k1_tarski(A_27), k5_enumset1(B_28, C_29, D_30, E_31, F_32, G_33, H_34))=k6_enumset1(A_27, B_28, C_29, D_30, E_31, F_32, G_33, H_34))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.50/1.88  tff(c_14, plain, (![C_22, D_23, A_20, B_21, F_25, G_26, E_24]: (k2_xboole_0(k1_tarski(A_20), k4_enumset1(B_21, C_22, D_23, E_24, F_25, G_26))=k5_enumset1(A_20, B_21, C_22, D_23, E_24, F_25, G_26))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.50/1.88  tff(c_12, plain, (![E_18, C_16, D_17, F_19, A_14, B_15]: (k2_xboole_0(k1_tarski(A_14), k3_enumset1(B_15, C_16, D_17, E_18, F_19))=k4_enumset1(A_14, B_15, C_16, D_17, E_18, F_19))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.50/1.88  tff(c_8, plain, (![A_9, B_10]: (k2_xboole_0(k1_tarski(A_9), k1_tarski(B_10))=k2_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.50/1.88  tff(c_65, plain, (![A_42, B_43, C_44]: (k2_xboole_0(k2_xboole_0(A_42, B_43), C_44)=k2_xboole_0(A_42, k2_xboole_0(B_43, C_44)))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.50/1.88  tff(c_142, plain, (![A_57, B_58, C_59]: (k2_xboole_0(k1_tarski(A_57), k2_xboole_0(k1_tarski(B_58), C_59))=k2_xboole_0(k2_tarski(A_57, B_58), C_59))), inference(superposition, [status(thm), theory('equality')], [c_8, c_65])).
% 4.50/1.88  tff(c_160, plain, (![A_57, E_18, C_16, D_17, F_19, A_14, B_15]: (k2_xboole_0(k2_tarski(A_57, A_14), k3_enumset1(B_15, C_16, D_17, E_18, F_19))=k2_xboole_0(k1_tarski(A_57), k4_enumset1(A_14, B_15, C_16, D_17, E_18, F_19)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_142])).
% 4.50/1.88  tff(c_1164, plain, (![B_148, C_147, E_144, A_149, F_145, A_150, D_146]: (k2_xboole_0(k2_tarski(A_150, A_149), k3_enumset1(B_148, C_147, D_146, E_144, F_145))=k5_enumset1(A_150, A_149, B_148, C_147, D_146, E_144, F_145))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_160])).
% 4.50/1.88  tff(c_85, plain, (![A_45, B_46, C_47]: (k2_xboole_0(k1_tarski(A_45), k2_tarski(B_46, C_47))=k1_enumset1(A_45, B_46, C_47))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.50/1.88  tff(c_2, plain, (![A_1, B_2, C_3]: (k2_xboole_0(k2_xboole_0(A_1, B_2), C_3)=k2_xboole_0(A_1, k2_xboole_0(B_2, C_3)))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.50/1.88  tff(c_91, plain, (![A_45, B_46, C_47, C_3]: (k2_xboole_0(k1_tarski(A_45), k2_xboole_0(k2_tarski(B_46, C_47), C_3))=k2_xboole_0(k1_enumset1(A_45, B_46, C_47), C_3))), inference(superposition, [status(thm), theory('equality')], [c_85, c_2])).
% 4.50/1.88  tff(c_1191, plain, (![B_148, C_147, E_144, A_45, A_149, F_145, A_150, D_146]: (k2_xboole_0(k1_enumset1(A_45, A_150, A_149), k3_enumset1(B_148, C_147, D_146, E_144, F_145))=k2_xboole_0(k1_tarski(A_45), k5_enumset1(A_150, A_149, B_148, C_147, D_146, E_144, F_145)))), inference(superposition, [status(thm), theory('equality')], [c_1164, c_91])).
% 4.50/1.88  tff(c_1203, plain, (![B_148, C_147, E_144, A_45, A_149, F_145, A_150, D_146]: (k2_xboole_0(k1_enumset1(A_45, A_150, A_149), k3_enumset1(B_148, C_147, D_146, E_144, F_145))=k6_enumset1(A_45, A_150, A_149, B_148, C_147, D_146, E_144, F_145))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_1191])).
% 4.50/1.88  tff(c_18, plain, (k2_xboole_0(k1_enumset1('#skF_1', '#skF_2', '#skF_3'), k3_enumset1('#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8'))!=k6_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_44])).
% 4.50/1.88  tff(c_1887, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1203, c_18])).
% 4.50/1.88  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.50/1.88  
% 4.50/1.88  Inference rules
% 4.50/1.88  ----------------------
% 4.50/1.88  #Ref     : 0
% 4.50/1.88  #Sup     : 465
% 4.50/1.88  #Fact    : 0
% 4.50/1.88  #Define  : 0
% 4.50/1.88  #Split   : 0
% 4.50/1.88  #Chain   : 0
% 4.50/1.88  #Close   : 0
% 4.50/1.88  
% 4.50/1.88  Ordering : KBO
% 4.50/1.88  
% 4.50/1.88  Simplification rules
% 4.50/1.88  ----------------------
% 4.50/1.88  #Subsume      : 0
% 4.50/1.88  #Demod        : 1039
% 4.50/1.88  #Tautology    : 249
% 4.50/1.88  #SimpNegUnit  : 0
% 4.50/1.88  #BackRed      : 1
% 4.50/1.88  
% 4.50/1.88  #Partial instantiations: 0
% 4.50/1.88  #Strategies tried      : 1
% 4.50/1.88  
% 4.50/1.88  Timing (in seconds)
% 4.50/1.88  ----------------------
% 4.50/1.88  Preprocessing        : 0.28
% 4.50/1.88  Parsing              : 0.16
% 4.50/1.88  CNF conversion       : 0.02
% 4.50/1.88  Main loop            : 0.80
% 4.50/1.88  Inferencing          : 0.30
% 4.50/1.88  Reduction            : 0.36
% 4.50/1.88  Demodulation         : 0.32
% 4.50/1.88  BG Simplification    : 0.05
% 4.50/1.88  Subsumption          : 0.07
% 4.50/1.88  Abstraction          : 0.07
% 4.50/1.88  MUC search           : 0.00
% 4.50/1.88  Cooper               : 0.00
% 4.50/1.88  Total                : 1.11
% 4.50/1.88  Index Insertion      : 0.00
% 4.50/1.88  Index Deletion       : 0.00
% 4.50/1.88  Index Matching       : 0.00
% 4.50/1.88  BG Taut test         : 0.00
%------------------------------------------------------------------------------

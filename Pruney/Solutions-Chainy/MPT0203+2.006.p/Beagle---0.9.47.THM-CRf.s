%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:47:12 EST 2020

% Result     : Theorem 1.95s
% Output     : CNFRefutation 1.95s
% Verified   : 
% Statistics : Number of formulae       :   39 (  42 expanded)
%              Number of leaves         :   25 (  27 expanded)
%              Depth                    :    6
%              Number of atoms          :   20 (  23 expanded)
%              Number of equality atoms :   19 (  22 expanded)
%              Maximal formula depth    :   11 (   6 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k7_enumset1 > k6_enumset1 > k4_enumset1 > k3_enumset1 > k1_enumset1 > k2_xboole_0 > #nlpp > k1_tarski > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_9 > #skF_8 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k7_enumset1,type,(
    k7_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

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

tff('#skF_9',type,(
    '#skF_9': $i )).

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

tff(f_29,axiom,(
    ! [A,B,C,D,E,F,G,H,I] : k7_enumset1(A,B,C,D,E,F,G,H,I) = k2_xboole_0(k1_tarski(A),k6_enumset1(B,C,D,E,F,G,H,I)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t127_enumset1)).

tff(f_35,axiom,(
    ! [A,B,C,D,E,F,G,H] : k6_enumset1(A,B,C,D,E,F,G,H) = k2_xboole_0(k3_enumset1(A,B,C,D,E),k1_enumset1(F,G,H)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_enumset1)).

tff(f_31,axiom,(
    ! [A,B,C,D,E,F] : k4_enumset1(A,B,C,D,E,F) = k2_xboole_0(k1_tarski(A),k3_enumset1(B,C,D,E,F)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_enumset1)).

tff(f_27,axiom,(
    ! [A,B,C] : k2_xboole_0(k2_xboole_0(A,B),C) = k2_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).

tff(f_33,axiom,(
    ! [A,B,C,D,E,F] : k4_enumset1(A,B,C,D,E,F) = k2_xboole_0(k1_enumset1(A,B,C),k1_enumset1(D,E,F)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t53_enumset1)).

tff(f_38,negated_conjecture,(
    ~ ! [A,B,C,D,E,F,G,H,I] : k7_enumset1(A,B,C,D,E,F,G,H,I) = k2_xboole_0(k1_enumset1(A,B,C),k4_enumset1(D,E,F,G,H,I)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t129_enumset1)).

tff(c_4,plain,(
    ! [B_5,D_7,A_4,G_10,E_8,C_6,F_9,I_12,H_11] : k2_xboole_0(k1_tarski(A_4),k6_enumset1(B_5,C_6,D_7,E_8,F_9,G_10,H_11,I_12)) = k7_enumset1(A_4,B_5,C_6,D_7,E_8,F_9,G_10,H_11,I_12) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_10,plain,(
    ! [A_25,G_31,F_30,E_29,H_32,C_27,D_28,B_26] : k2_xboole_0(k3_enumset1(A_25,B_26,C_27,D_28,E_29),k1_enumset1(F_30,G_31,H_32)) = k6_enumset1(A_25,B_26,C_27,D_28,E_29,F_30,G_31,H_32) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_30,plain,(
    ! [B_38,D_37,F_36,E_39,A_40,C_41] : k2_xboole_0(k1_tarski(A_40),k3_enumset1(B_38,C_41,D_37,E_39,F_36)) = k4_enumset1(A_40,B_38,C_41,D_37,E_39,F_36) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_2,plain,(
    ! [A_1,B_2,C_3] : k2_xboole_0(k2_xboole_0(A_1,B_2),C_3) = k2_xboole_0(A_1,k2_xboole_0(B_2,C_3)) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_88,plain,(
    ! [D_63,A_65,B_64,F_67,E_68,C_69,C_66] : k2_xboole_0(k1_tarski(A_65),k2_xboole_0(k3_enumset1(B_64,C_66,D_63,E_68,F_67),C_69)) = k2_xboole_0(k4_enumset1(A_65,B_64,C_66,D_63,E_68,F_67),C_69) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_2])).

tff(c_100,plain,(
    ! [A_25,G_31,A_65,F_30,E_29,H_32,C_27,D_28,B_26] : k2_xboole_0(k4_enumset1(A_65,A_25,B_26,C_27,D_28,E_29),k1_enumset1(F_30,G_31,H_32)) = k2_xboole_0(k1_tarski(A_65),k6_enumset1(A_25,B_26,C_27,D_28,E_29,F_30,G_31,H_32)) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_88])).

tff(c_151,plain,(
    ! [A_25,G_31,A_65,F_30,E_29,H_32,C_27,D_28,B_26] : k2_xboole_0(k4_enumset1(A_65,A_25,B_26,C_27,D_28,E_29),k1_enumset1(F_30,G_31,H_32)) = k7_enumset1(A_65,A_25,B_26,C_27,D_28,E_29,F_30,G_31,H_32) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_100])).

tff(c_8,plain,(
    ! [A_19,C_21,D_22,B_20,F_24,E_23] : k2_xboole_0(k1_enumset1(A_19,B_20,C_21),k1_enumset1(D_22,E_23,F_24)) = k4_enumset1(A_19,B_20,C_21,D_22,E_23,F_24) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_42,plain,(
    ! [C_42,F_46,E_43,A_45,D_47,B_44] : k2_xboole_0(k1_enumset1(A_45,B_44,C_42),k1_enumset1(D_47,E_43,F_46)) = k4_enumset1(A_45,B_44,C_42,D_47,E_43,F_46) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_66,plain,(
    ! [B_59,A_58,D_56,E_62,C_57,C_61,F_60] : k2_xboole_0(k1_enumset1(A_58,B_59,C_57),k2_xboole_0(k1_enumset1(D_56,E_62,F_60),C_61)) = k2_xboole_0(k4_enumset1(A_58,B_59,C_57,D_56,E_62,F_60),C_61) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_2])).

tff(c_84,plain,(
    ! [A_19,B_59,A_58,C_57,C_21,D_22,B_20,F_24,E_23] : k2_xboole_0(k4_enumset1(A_58,B_59,C_57,A_19,B_20,C_21),k1_enumset1(D_22,E_23,F_24)) = k2_xboole_0(k1_enumset1(A_58,B_59,C_57),k4_enumset1(A_19,B_20,C_21,D_22,E_23,F_24)) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_66])).

tff(c_152,plain,(
    ! [A_19,B_59,A_58,C_57,C_21,D_22,B_20,F_24,E_23] : k2_xboole_0(k1_enumset1(A_58,B_59,C_57),k4_enumset1(A_19,B_20,C_21,D_22,E_23,F_24)) = k7_enumset1(A_58,B_59,C_57,A_19,B_20,C_21,D_22,E_23,F_24) ),
    inference(demodulation,[status(thm),theory(equality)],[c_151,c_84])).

tff(c_12,plain,(
    k2_xboole_0(k1_enumset1('#skF_1','#skF_2','#skF_3'),k4_enumset1('#skF_4','#skF_5','#skF_6','#skF_7','#skF_8','#skF_9')) != k7_enumset1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7','#skF_8','#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_167,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_152,c_12])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n003.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:52:57 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.95/1.20  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.95/1.20  
% 1.95/1.20  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.95/1.20  %$ k7_enumset1 > k6_enumset1 > k4_enumset1 > k3_enumset1 > k1_enumset1 > k2_xboole_0 > #nlpp > k1_tarski > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_9 > #skF_8 > #skF_4
% 1.95/1.20  
% 1.95/1.20  %Foreground sorts:
% 1.95/1.20  
% 1.95/1.20  
% 1.95/1.20  %Background operators:
% 1.95/1.20  
% 1.95/1.20  
% 1.95/1.20  %Foreground operators:
% 1.95/1.20  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.95/1.20  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.95/1.20  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 1.95/1.20  tff(k7_enumset1, type, k7_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 1.95/1.20  tff('#skF_7', type, '#skF_7': $i).
% 1.95/1.20  tff('#skF_5', type, '#skF_5': $i).
% 1.95/1.20  tff('#skF_6', type, '#skF_6': $i).
% 1.95/1.20  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.95/1.20  tff('#skF_2', type, '#skF_2': $i).
% 1.95/1.20  tff('#skF_3', type, '#skF_3': $i).
% 1.95/1.20  tff('#skF_1', type, '#skF_1': $i).
% 1.95/1.20  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 1.95/1.20  tff('#skF_9', type, '#skF_9': $i).
% 1.95/1.20  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 1.95/1.20  tff('#skF_8', type, '#skF_8': $i).
% 1.95/1.20  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.95/1.20  tff('#skF_4', type, '#skF_4': $i).
% 1.95/1.20  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.95/1.20  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.95/1.20  
% 1.95/1.21  tff(f_29, axiom, (![A, B, C, D, E, F, G, H, I]: (k7_enumset1(A, B, C, D, E, F, G, H, I) = k2_xboole_0(k1_tarski(A), k6_enumset1(B, C, D, E, F, G, H, I)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t127_enumset1)).
% 1.95/1.21  tff(f_35, axiom, (![A, B, C, D, E, F, G, H]: (k6_enumset1(A, B, C, D, E, F, G, H) = k2_xboole_0(k3_enumset1(A, B, C, D, E), k1_enumset1(F, G, H)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t66_enumset1)).
% 1.95/1.21  tff(f_31, axiom, (![A, B, C, D, E, F]: (k4_enumset1(A, B, C, D, E, F) = k2_xboole_0(k1_tarski(A), k3_enumset1(B, C, D, E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_enumset1)).
% 1.95/1.21  tff(f_27, axiom, (![A, B, C]: (k2_xboole_0(k2_xboole_0(A, B), C) = k2_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_1)).
% 1.95/1.21  tff(f_33, axiom, (![A, B, C, D, E, F]: (k4_enumset1(A, B, C, D, E, F) = k2_xboole_0(k1_enumset1(A, B, C), k1_enumset1(D, E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t53_enumset1)).
% 1.95/1.21  tff(f_38, negated_conjecture, ~(![A, B, C, D, E, F, G, H, I]: (k7_enumset1(A, B, C, D, E, F, G, H, I) = k2_xboole_0(k1_enumset1(A, B, C), k4_enumset1(D, E, F, G, H, I)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t129_enumset1)).
% 1.95/1.21  tff(c_4, plain, (![B_5, D_7, A_4, G_10, E_8, C_6, F_9, I_12, H_11]: (k2_xboole_0(k1_tarski(A_4), k6_enumset1(B_5, C_6, D_7, E_8, F_9, G_10, H_11, I_12))=k7_enumset1(A_4, B_5, C_6, D_7, E_8, F_9, G_10, H_11, I_12))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.95/1.21  tff(c_10, plain, (![A_25, G_31, F_30, E_29, H_32, C_27, D_28, B_26]: (k2_xboole_0(k3_enumset1(A_25, B_26, C_27, D_28, E_29), k1_enumset1(F_30, G_31, H_32))=k6_enumset1(A_25, B_26, C_27, D_28, E_29, F_30, G_31, H_32))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.95/1.21  tff(c_30, plain, (![B_38, D_37, F_36, E_39, A_40, C_41]: (k2_xboole_0(k1_tarski(A_40), k3_enumset1(B_38, C_41, D_37, E_39, F_36))=k4_enumset1(A_40, B_38, C_41, D_37, E_39, F_36))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.95/1.21  tff(c_2, plain, (![A_1, B_2, C_3]: (k2_xboole_0(k2_xboole_0(A_1, B_2), C_3)=k2_xboole_0(A_1, k2_xboole_0(B_2, C_3)))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.95/1.21  tff(c_88, plain, (![D_63, A_65, B_64, F_67, E_68, C_69, C_66]: (k2_xboole_0(k1_tarski(A_65), k2_xboole_0(k3_enumset1(B_64, C_66, D_63, E_68, F_67), C_69))=k2_xboole_0(k4_enumset1(A_65, B_64, C_66, D_63, E_68, F_67), C_69))), inference(superposition, [status(thm), theory('equality')], [c_30, c_2])).
% 1.95/1.21  tff(c_100, plain, (![A_25, G_31, A_65, F_30, E_29, H_32, C_27, D_28, B_26]: (k2_xboole_0(k4_enumset1(A_65, A_25, B_26, C_27, D_28, E_29), k1_enumset1(F_30, G_31, H_32))=k2_xboole_0(k1_tarski(A_65), k6_enumset1(A_25, B_26, C_27, D_28, E_29, F_30, G_31, H_32)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_88])).
% 1.95/1.21  tff(c_151, plain, (![A_25, G_31, A_65, F_30, E_29, H_32, C_27, D_28, B_26]: (k2_xboole_0(k4_enumset1(A_65, A_25, B_26, C_27, D_28, E_29), k1_enumset1(F_30, G_31, H_32))=k7_enumset1(A_65, A_25, B_26, C_27, D_28, E_29, F_30, G_31, H_32))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_100])).
% 1.95/1.21  tff(c_8, plain, (![A_19, C_21, D_22, B_20, F_24, E_23]: (k2_xboole_0(k1_enumset1(A_19, B_20, C_21), k1_enumset1(D_22, E_23, F_24))=k4_enumset1(A_19, B_20, C_21, D_22, E_23, F_24))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.95/1.21  tff(c_42, plain, (![C_42, F_46, E_43, A_45, D_47, B_44]: (k2_xboole_0(k1_enumset1(A_45, B_44, C_42), k1_enumset1(D_47, E_43, F_46))=k4_enumset1(A_45, B_44, C_42, D_47, E_43, F_46))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.95/1.21  tff(c_66, plain, (![B_59, A_58, D_56, E_62, C_57, C_61, F_60]: (k2_xboole_0(k1_enumset1(A_58, B_59, C_57), k2_xboole_0(k1_enumset1(D_56, E_62, F_60), C_61))=k2_xboole_0(k4_enumset1(A_58, B_59, C_57, D_56, E_62, F_60), C_61))), inference(superposition, [status(thm), theory('equality')], [c_42, c_2])).
% 1.95/1.21  tff(c_84, plain, (![A_19, B_59, A_58, C_57, C_21, D_22, B_20, F_24, E_23]: (k2_xboole_0(k4_enumset1(A_58, B_59, C_57, A_19, B_20, C_21), k1_enumset1(D_22, E_23, F_24))=k2_xboole_0(k1_enumset1(A_58, B_59, C_57), k4_enumset1(A_19, B_20, C_21, D_22, E_23, F_24)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_66])).
% 1.95/1.21  tff(c_152, plain, (![A_19, B_59, A_58, C_57, C_21, D_22, B_20, F_24, E_23]: (k2_xboole_0(k1_enumset1(A_58, B_59, C_57), k4_enumset1(A_19, B_20, C_21, D_22, E_23, F_24))=k7_enumset1(A_58, B_59, C_57, A_19, B_20, C_21, D_22, E_23, F_24))), inference(demodulation, [status(thm), theory('equality')], [c_151, c_84])).
% 1.95/1.21  tff(c_12, plain, (k2_xboole_0(k1_enumset1('#skF_1', '#skF_2', '#skF_3'), k4_enumset1('#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_9'))!=k7_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_9')), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.95/1.21  tff(c_167, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_152, c_12])).
% 1.95/1.21  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.95/1.21  
% 1.95/1.21  Inference rules
% 1.95/1.21  ----------------------
% 1.95/1.21  #Ref     : 0
% 1.95/1.21  #Sup     : 38
% 1.95/1.21  #Fact    : 0
% 1.95/1.21  #Define  : 0
% 1.95/1.21  #Split   : 0
% 1.95/1.21  #Chain   : 0
% 1.95/1.21  #Close   : 0
% 1.95/1.21  
% 1.95/1.21  Ordering : KBO
% 1.95/1.21  
% 1.95/1.21  Simplification rules
% 1.95/1.21  ----------------------
% 1.95/1.21  #Subsume      : 0
% 1.95/1.21  #Demod        : 19
% 1.95/1.21  #Tautology    : 25
% 1.95/1.21  #SimpNegUnit  : 0
% 1.95/1.21  #BackRed      : 2
% 1.95/1.21  
% 1.95/1.21  #Partial instantiations: 0
% 1.95/1.21  #Strategies tried      : 1
% 1.95/1.21  
% 1.95/1.21  Timing (in seconds)
% 1.95/1.21  ----------------------
% 1.95/1.22  Preprocessing        : 0.25
% 1.95/1.22  Parsing              : 0.13
% 1.95/1.22  CNF conversion       : 0.02
% 1.95/1.22  Main loop            : 0.17
% 1.95/1.22  Inferencing          : 0.08
% 1.95/1.22  Reduction            : 0.05
% 1.95/1.22  Demodulation         : 0.05
% 1.95/1.22  BG Simplification    : 0.02
% 1.95/1.22  Subsumption          : 0.02
% 1.95/1.22  Abstraction          : 0.02
% 1.95/1.22  MUC search           : 0.00
% 1.95/1.22  Cooper               : 0.00
% 1.95/1.22  Total                : 0.45
% 1.95/1.22  Index Insertion      : 0.00
% 1.95/1.22  Index Deletion       : 0.00
% 1.95/1.22  Index Matching       : 0.00
% 1.95/1.22  BG Taut test         : 0.00
%------------------------------------------------------------------------------

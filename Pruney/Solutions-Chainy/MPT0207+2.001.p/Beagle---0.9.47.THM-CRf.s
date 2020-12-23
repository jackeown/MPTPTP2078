%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:47:13 EST 2020

% Result     : Theorem 2.10s
% Output     : CNFRefutation 2.10s
% Verified   : 
% Statistics : Number of formulae       :   37 (  79 expanded)
%              Number of leaves         :   23 (  39 expanded)
%              Depth                    :    6
%              Number of atoms          :   19 (  61 expanded)
%              Number of equality atoms :   18 (  60 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k7_enumset1 > k5_enumset1 > k3_enumset1 > k2_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_9 > #skF_8 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k7_enumset1,type,(
    k7_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

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

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

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

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_29,axiom,(
    ! [A,B,C,D,E,F,G,H,I] : k7_enumset1(A,B,C,D,E,F,G,H,I) = k2_xboole_0(k2_enumset1(A,B,C,D),k3_enumset1(E,F,G,H,I)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l142_enumset1)).

tff(f_33,axiom,(
    ! [A,B,C,D,E,F,G,H,I] : k7_enumset1(A,B,C,D,E,F,G,H,I) = k2_xboole_0(k3_enumset1(A,B,C,D,E),k2_enumset1(F,G,H,I)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t131_enumset1)).

tff(f_31,axiom,(
    ! [A,B,C,D,E,F,G,H,I] : k7_enumset1(A,B,C,D,E,F,G,H,I) = k2_xboole_0(k2_tarski(A,B),k5_enumset1(C,D,E,F,G,H,I)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t128_enumset1)).

tff(f_36,negated_conjecture,(
    ~ ! [A,B,C,D,E,F,G,H,I] : k7_enumset1(A,B,C,D,E,F,G,H,I) = k2_xboole_0(k5_enumset1(A,B,C,D,E,F,G),k2_tarski(H,I)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t133_enumset1)).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_67,plain,(
    ! [A_46,H_47,B_49,F_45,C_48,E_42,I_44,D_43,G_41] : k2_xboole_0(k2_enumset1(A_46,B_49,C_48,D_43),k3_enumset1(E_42,F_45,G_41,H_47,I_44)) = k7_enumset1(A_46,B_49,C_48,D_43,E_42,F_45,G_41,H_47,I_44) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_109,plain,(
    ! [H_64,A_66,E_62,D_59,I_67,C_65,F_61,B_60,G_63] : k2_xboole_0(k3_enumset1(E_62,F_61,G_63,H_64,I_67),k2_enumset1(A_66,B_60,C_65,D_59)) = k7_enumset1(A_66,B_60,C_65,D_59,E_62,F_61,G_63,H_64,I_67) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_67])).

tff(c_8,plain,(
    ! [A_21,B_22,H_28,D_24,C_23,I_29,G_27,F_26,E_25] : k2_xboole_0(k3_enumset1(A_21,B_22,C_23,D_24,E_25),k2_enumset1(F_26,G_27,H_28,I_29)) = k7_enumset1(A_21,B_22,C_23,D_24,E_25,F_26,G_27,H_28,I_29) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_115,plain,(
    ! [H_64,A_66,E_62,D_59,I_67,C_65,F_61,B_60,G_63] : k7_enumset1(E_62,F_61,G_63,H_64,I_67,A_66,B_60,C_65,D_59) = k7_enumset1(A_66,B_60,C_65,D_59,E_62,F_61,G_63,H_64,I_67) ),
    inference(superposition,[status(thm),theory(equality)],[c_109,c_8])).

tff(c_141,plain,(
    ! [C_70,I_68,A_72,G_73,E_74,D_75,H_76,B_71,F_69] : k7_enumset1(E_74,F_69,G_73,H_76,I_68,A_72,B_71,C_70,D_75) = k7_enumset1(A_72,B_71,C_70,D_75,E_74,F_69,G_73,H_76,I_68) ),
    inference(superposition,[status(thm),theory(equality)],[c_109,c_8])).

tff(c_156,plain,(
    ! [H_64,A_66,E_62,D_59,I_67,C_65,F_61,B_60,G_63] : k7_enumset1(F_61,G_63,H_64,I_67,A_66,B_60,C_65,D_59,E_62) = k7_enumset1(E_62,F_61,G_63,H_64,I_67,A_66,B_60,C_65,D_59) ),
    inference(superposition,[status(thm),theory(equality)],[c_115,c_141])).

tff(c_6,plain,(
    ! [E_16,D_15,I_20,H_19,F_17,C_14,A_12,B_13,G_18] : k2_xboole_0(k2_tarski(A_12,B_13),k5_enumset1(C_14,D_15,E_16,F_17,G_18,H_19,I_20)) = k7_enumset1(A_12,B_13,C_14,D_15,E_16,F_17,G_18,H_19,I_20) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_10,plain,(
    k2_xboole_0(k5_enumset1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'),k2_tarski('#skF_8','#skF_9')) != k7_enumset1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7','#skF_8','#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_11,plain,(
    k2_xboole_0(k2_tarski('#skF_8','#skF_9'),k5_enumset1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7')) != k7_enumset1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7','#skF_8','#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_10])).

tff(c_12,plain,(
    k7_enumset1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7','#skF_8','#skF_9') != k7_enumset1('#skF_8','#skF_9','#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_11])).

tff(c_140,plain,(
    k7_enumset1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7','#skF_8','#skF_9') != k7_enumset1('#skF_4','#skF_5','#skF_6','#skF_7','#skF_8','#skF_9','#skF_1','#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_115,c_12])).

tff(c_171,plain,(
    k7_enumset1('#skF_8','#skF_9','#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7') != k7_enumset1('#skF_4','#skF_5','#skF_6','#skF_7','#skF_8','#skF_9','#skF_1','#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_156,c_156,c_140])).

tff(c_174,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_115,c_171])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:15:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.10/1.30  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.10/1.30  
% 2.10/1.30  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.10/1.31  %$ k7_enumset1 > k5_enumset1 > k3_enumset1 > k2_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_9 > #skF_8 > #skF_4
% 2.10/1.31  
% 2.10/1.31  %Foreground sorts:
% 2.10/1.31  
% 2.10/1.31  
% 2.10/1.31  %Background operators:
% 2.10/1.31  
% 2.10/1.31  
% 2.10/1.31  %Foreground operators:
% 2.10/1.31  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.10/1.31  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.10/1.31  tff(k7_enumset1, type, k7_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.10/1.31  tff('#skF_7', type, '#skF_7': $i).
% 2.10/1.31  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.10/1.31  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.10/1.31  tff('#skF_5', type, '#skF_5': $i).
% 2.10/1.31  tff('#skF_6', type, '#skF_6': $i).
% 2.10/1.31  tff('#skF_2', type, '#skF_2': $i).
% 2.10/1.31  tff('#skF_3', type, '#skF_3': $i).
% 2.10/1.31  tff('#skF_1', type, '#skF_1': $i).
% 2.10/1.31  tff('#skF_9', type, '#skF_9': $i).
% 2.10/1.31  tff('#skF_8', type, '#skF_8': $i).
% 2.10/1.31  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.10/1.31  tff('#skF_4', type, '#skF_4': $i).
% 2.10/1.31  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.10/1.31  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.10/1.31  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.10/1.31  
% 2.10/1.32  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 2.10/1.32  tff(f_29, axiom, (![A, B, C, D, E, F, G, H, I]: (k7_enumset1(A, B, C, D, E, F, G, H, I) = k2_xboole_0(k2_enumset1(A, B, C, D), k3_enumset1(E, F, G, H, I)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l142_enumset1)).
% 2.10/1.32  tff(f_33, axiom, (![A, B, C, D, E, F, G, H, I]: (k7_enumset1(A, B, C, D, E, F, G, H, I) = k2_xboole_0(k3_enumset1(A, B, C, D, E), k2_enumset1(F, G, H, I)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t131_enumset1)).
% 2.10/1.32  tff(f_31, axiom, (![A, B, C, D, E, F, G, H, I]: (k7_enumset1(A, B, C, D, E, F, G, H, I) = k2_xboole_0(k2_tarski(A, B), k5_enumset1(C, D, E, F, G, H, I)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t128_enumset1)).
% 2.10/1.32  tff(f_36, negated_conjecture, ~(![A, B, C, D, E, F, G, H, I]: (k7_enumset1(A, B, C, D, E, F, G, H, I) = k2_xboole_0(k5_enumset1(A, B, C, D, E, F, G), k2_tarski(H, I)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t133_enumset1)).
% 2.10/1.32  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.10/1.32  tff(c_67, plain, (![A_46, H_47, B_49, F_45, C_48, E_42, I_44, D_43, G_41]: (k2_xboole_0(k2_enumset1(A_46, B_49, C_48, D_43), k3_enumset1(E_42, F_45, G_41, H_47, I_44))=k7_enumset1(A_46, B_49, C_48, D_43, E_42, F_45, G_41, H_47, I_44))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.10/1.32  tff(c_109, plain, (![H_64, A_66, E_62, D_59, I_67, C_65, F_61, B_60, G_63]: (k2_xboole_0(k3_enumset1(E_62, F_61, G_63, H_64, I_67), k2_enumset1(A_66, B_60, C_65, D_59))=k7_enumset1(A_66, B_60, C_65, D_59, E_62, F_61, G_63, H_64, I_67))), inference(superposition, [status(thm), theory('equality')], [c_2, c_67])).
% 2.10/1.32  tff(c_8, plain, (![A_21, B_22, H_28, D_24, C_23, I_29, G_27, F_26, E_25]: (k2_xboole_0(k3_enumset1(A_21, B_22, C_23, D_24, E_25), k2_enumset1(F_26, G_27, H_28, I_29))=k7_enumset1(A_21, B_22, C_23, D_24, E_25, F_26, G_27, H_28, I_29))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.10/1.32  tff(c_115, plain, (![H_64, A_66, E_62, D_59, I_67, C_65, F_61, B_60, G_63]: (k7_enumset1(E_62, F_61, G_63, H_64, I_67, A_66, B_60, C_65, D_59)=k7_enumset1(A_66, B_60, C_65, D_59, E_62, F_61, G_63, H_64, I_67))), inference(superposition, [status(thm), theory('equality')], [c_109, c_8])).
% 2.10/1.32  tff(c_141, plain, (![C_70, I_68, A_72, G_73, E_74, D_75, H_76, B_71, F_69]: (k7_enumset1(E_74, F_69, G_73, H_76, I_68, A_72, B_71, C_70, D_75)=k7_enumset1(A_72, B_71, C_70, D_75, E_74, F_69, G_73, H_76, I_68))), inference(superposition, [status(thm), theory('equality')], [c_109, c_8])).
% 2.10/1.32  tff(c_156, plain, (![H_64, A_66, E_62, D_59, I_67, C_65, F_61, B_60, G_63]: (k7_enumset1(F_61, G_63, H_64, I_67, A_66, B_60, C_65, D_59, E_62)=k7_enumset1(E_62, F_61, G_63, H_64, I_67, A_66, B_60, C_65, D_59))), inference(superposition, [status(thm), theory('equality')], [c_115, c_141])).
% 2.10/1.32  tff(c_6, plain, (![E_16, D_15, I_20, H_19, F_17, C_14, A_12, B_13, G_18]: (k2_xboole_0(k2_tarski(A_12, B_13), k5_enumset1(C_14, D_15, E_16, F_17, G_18, H_19, I_20))=k7_enumset1(A_12, B_13, C_14, D_15, E_16, F_17, G_18, H_19, I_20))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.10/1.32  tff(c_10, plain, (k2_xboole_0(k5_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'), k2_tarski('#skF_8', '#skF_9'))!=k7_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_9')), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.10/1.32  tff(c_11, plain, (k2_xboole_0(k2_tarski('#skF_8', '#skF_9'), k5_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'))!=k7_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_10])).
% 2.10/1.32  tff(c_12, plain, (k7_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_9')!=k7_enumset1('#skF_8', '#skF_9', '#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_6, c_11])).
% 2.10/1.32  tff(c_140, plain, (k7_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_9')!=k7_enumset1('#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_9', '#skF_1', '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_115, c_12])).
% 2.10/1.32  tff(c_171, plain, (k7_enumset1('#skF_8', '#skF_9', '#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7')!=k7_enumset1('#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_9', '#skF_1', '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_156, c_156, c_140])).
% 2.10/1.32  tff(c_174, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_115, c_171])).
% 2.10/1.32  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.10/1.32  
% 2.10/1.32  Inference rules
% 2.10/1.32  ----------------------
% 2.10/1.32  #Ref     : 0
% 2.10/1.32  #Sup     : 42
% 2.10/1.32  #Fact    : 0
% 2.10/1.32  #Define  : 0
% 2.10/1.32  #Split   : 0
% 2.10/1.32  #Chain   : 0
% 2.10/1.32  #Close   : 0
% 2.10/1.32  
% 2.10/1.32  Ordering : KBO
% 2.10/1.32  
% 2.10/1.32  Simplification rules
% 2.10/1.32  ----------------------
% 2.10/1.32  #Subsume      : 1
% 2.10/1.32  #Demod        : 11
% 2.10/1.32  #Tautology    : 25
% 2.10/1.32  #SimpNegUnit  : 0
% 2.10/1.32  #BackRed      : 2
% 2.10/1.32  
% 2.10/1.32  #Partial instantiations: 0
% 2.10/1.32  #Strategies tried      : 1
% 2.10/1.32  
% 2.10/1.32  Timing (in seconds)
% 2.10/1.32  ----------------------
% 2.10/1.32  Preprocessing        : 0.30
% 2.10/1.32  Parsing              : 0.17
% 2.10/1.32  CNF conversion       : 0.02
% 2.10/1.32  Main loop            : 0.23
% 2.10/1.32  Inferencing          : 0.10
% 2.10/1.32  Reduction            : 0.09
% 2.10/1.32  Demodulation         : 0.08
% 2.10/1.32  BG Simplification    : 0.02
% 2.10/1.32  Subsumption          : 0.03
% 2.10/1.32  Abstraction          : 0.02
% 2.10/1.32  MUC search           : 0.00
% 2.10/1.32  Cooper               : 0.00
% 2.10/1.32  Total                : 0.57
% 2.10/1.32  Index Insertion      : 0.00
% 2.10/1.32  Index Deletion       : 0.00
% 2.10/1.32  Index Matching       : 0.00
% 2.10/1.32  BG Taut test         : 0.00
%------------------------------------------------------------------------------

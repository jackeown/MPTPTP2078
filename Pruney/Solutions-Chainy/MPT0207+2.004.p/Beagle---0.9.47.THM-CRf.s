%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:47:13 EST 2020

% Result     : Theorem 2.06s
% Output     : CNFRefutation 2.06s
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_31,axiom,(
    ! [A,B,C,D,E,F,G,H,I] : k7_enumset1(A,B,C,D,E,F,G,H,I) = k2_xboole_0(k2_enumset1(A,B,C,D),k3_enumset1(E,F,G,H,I)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t130_enumset1)).

tff(f_33,axiom,(
    ! [A,B,C,D,E,F,G,H,I] : k7_enumset1(A,B,C,D,E,F,G,H,I) = k2_xboole_0(k3_enumset1(A,B,C,D,E),k2_enumset1(F,G,H,I)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t131_enumset1)).

tff(f_29,axiom,(
    ! [A,B,C,D,E,F,G,H,I] : k7_enumset1(A,B,C,D,E,F,G,H,I) = k2_xboole_0(k2_tarski(A,B),k5_enumset1(C,D,E,F,G,H,I)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t128_enumset1)).

tff(f_36,negated_conjecture,(
    ~ ! [A,B,C,D,E,F,G,H,I] : k7_enumset1(A,B,C,D,E,F,G,H,I) = k2_xboole_0(k5_enumset1(A,B,C,D,E,F,G),k2_tarski(H,I)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t133_enumset1)).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_46,plain,(
    ! [C_39,A_35,B_33,F_38,G_32,D_37,E_36,I_40,H_34] : k2_xboole_0(k2_enumset1(A_35,B_33,C_39,D_37),k3_enumset1(E_36,F_38,G_32,H_34,I_40)) = k7_enumset1(A_35,B_33,C_39,D_37,E_36,F_38,G_32,H_34,I_40) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_134,plain,(
    ! [D_70,I_75,C_74,G_76,F_72,E_69,B_71,H_73,A_68] : k2_xboole_0(k3_enumset1(E_69,F_72,G_76,H_73,I_75),k2_enumset1(A_68,B_71,C_74,D_70)) = k7_enumset1(A_68,B_71,C_74,D_70,E_69,F_72,G_76,H_73,I_75) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_46])).

tff(c_8,plain,(
    ! [A_21,B_22,H_28,D_24,C_23,I_29,G_27,F_26,E_25] : k2_xboole_0(k3_enumset1(A_21,B_22,C_23,D_24,E_25),k2_enumset1(F_26,G_27,H_28,I_29)) = k7_enumset1(A_21,B_22,C_23,D_24,E_25,F_26,G_27,H_28,I_29) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_140,plain,(
    ! [D_70,I_75,C_74,G_76,F_72,E_69,B_71,H_73,A_68] : k7_enumset1(E_69,F_72,G_76,H_73,I_75,A_68,B_71,C_74,D_70) = k7_enumset1(A_68,B_71,C_74,D_70,E_69,F_72,G_76,H_73,I_75) ),
    inference(superposition,[status(thm),theory(equality)],[c_134,c_8])).

tff(c_166,plain,(
    ! [F_80,G_78,C_79,B_81,D_84,H_85,A_83,I_77,E_82] : k7_enumset1(E_82,F_80,G_78,H_85,I_77,A_83,B_81,C_79,D_84) = k7_enumset1(A_83,B_81,C_79,D_84,E_82,F_80,G_78,H_85,I_77) ),
    inference(superposition,[status(thm),theory(equality)],[c_134,c_8])).

tff(c_178,plain,(
    ! [F_80,G_78,C_79,B_81,D_84,H_85,A_83,I_77,E_82] : k7_enumset1(I_77,A_83,B_81,C_79,D_84,E_82,F_80,G_78,H_85) = k7_enumset1(A_83,B_81,C_79,D_84,E_82,F_80,G_78,H_85,I_77) ),
    inference(superposition,[status(thm),theory(equality)],[c_166,c_140])).

tff(c_4,plain,(
    ! [A_3,F_8,D_6,I_11,C_5,H_10,G_9,E_7,B_4] : k2_xboole_0(k2_tarski(A_3,B_4),k5_enumset1(C_5,D_6,E_7,F_8,G_9,H_10,I_11)) = k7_enumset1(A_3,B_4,C_5,D_6,E_7,F_8,G_9,H_10,I_11) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_10,plain,(
    k2_xboole_0(k5_enumset1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'),k2_tarski('#skF_8','#skF_9')) != k7_enumset1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7','#skF_8','#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_11,plain,(
    k2_xboole_0(k2_tarski('#skF_8','#skF_9'),k5_enumset1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7')) != k7_enumset1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7','#skF_8','#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_10])).

tff(c_12,plain,(
    k7_enumset1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7','#skF_8','#skF_9') != k7_enumset1('#skF_8','#skF_9','#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_11])).

tff(c_165,plain,(
    k7_enumset1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7','#skF_8','#skF_9') != k7_enumset1('#skF_4','#skF_5','#skF_6','#skF_7','#skF_8','#skF_9','#skF_1','#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_140,c_12])).

tff(c_195,plain,(
    k7_enumset1('#skF_8','#skF_9','#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7') != k7_enumset1('#skF_4','#skF_5','#skF_6','#skF_7','#skF_8','#skF_9','#skF_1','#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_178,c_178,c_165])).

tff(c_198,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_140,c_195])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:41:12 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.06/1.26  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.06/1.26  
% 2.06/1.26  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.06/1.26  %$ k7_enumset1 > k5_enumset1 > k3_enumset1 > k2_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_9 > #skF_8 > #skF_4
% 2.06/1.26  
% 2.06/1.26  %Foreground sorts:
% 2.06/1.26  
% 2.06/1.26  
% 2.06/1.26  %Background operators:
% 2.06/1.26  
% 2.06/1.26  
% 2.06/1.26  %Foreground operators:
% 2.06/1.26  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.06/1.26  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.06/1.26  tff(k7_enumset1, type, k7_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.06/1.26  tff('#skF_7', type, '#skF_7': $i).
% 2.06/1.26  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.06/1.26  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.06/1.26  tff('#skF_5', type, '#skF_5': $i).
% 2.06/1.26  tff('#skF_6', type, '#skF_6': $i).
% 2.06/1.26  tff('#skF_2', type, '#skF_2': $i).
% 2.06/1.26  tff('#skF_3', type, '#skF_3': $i).
% 2.06/1.26  tff('#skF_1', type, '#skF_1': $i).
% 2.06/1.26  tff('#skF_9', type, '#skF_9': $i).
% 2.06/1.26  tff('#skF_8', type, '#skF_8': $i).
% 2.06/1.26  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.06/1.26  tff('#skF_4', type, '#skF_4': $i).
% 2.06/1.26  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.06/1.26  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.06/1.26  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.06/1.26  
% 2.06/1.27  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 2.06/1.27  tff(f_31, axiom, (![A, B, C, D, E, F, G, H, I]: (k7_enumset1(A, B, C, D, E, F, G, H, I) = k2_xboole_0(k2_enumset1(A, B, C, D), k3_enumset1(E, F, G, H, I)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t130_enumset1)).
% 2.06/1.27  tff(f_33, axiom, (![A, B, C, D, E, F, G, H, I]: (k7_enumset1(A, B, C, D, E, F, G, H, I) = k2_xboole_0(k3_enumset1(A, B, C, D, E), k2_enumset1(F, G, H, I)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t131_enumset1)).
% 2.06/1.27  tff(f_29, axiom, (![A, B, C, D, E, F, G, H, I]: (k7_enumset1(A, B, C, D, E, F, G, H, I) = k2_xboole_0(k2_tarski(A, B), k5_enumset1(C, D, E, F, G, H, I)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t128_enumset1)).
% 2.06/1.27  tff(f_36, negated_conjecture, ~(![A, B, C, D, E, F, G, H, I]: (k7_enumset1(A, B, C, D, E, F, G, H, I) = k2_xboole_0(k5_enumset1(A, B, C, D, E, F, G), k2_tarski(H, I)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t133_enumset1)).
% 2.06/1.27  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.06/1.27  tff(c_46, plain, (![C_39, A_35, B_33, F_38, G_32, D_37, E_36, I_40, H_34]: (k2_xboole_0(k2_enumset1(A_35, B_33, C_39, D_37), k3_enumset1(E_36, F_38, G_32, H_34, I_40))=k7_enumset1(A_35, B_33, C_39, D_37, E_36, F_38, G_32, H_34, I_40))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.06/1.27  tff(c_134, plain, (![D_70, I_75, C_74, G_76, F_72, E_69, B_71, H_73, A_68]: (k2_xboole_0(k3_enumset1(E_69, F_72, G_76, H_73, I_75), k2_enumset1(A_68, B_71, C_74, D_70))=k7_enumset1(A_68, B_71, C_74, D_70, E_69, F_72, G_76, H_73, I_75))), inference(superposition, [status(thm), theory('equality')], [c_2, c_46])).
% 2.06/1.27  tff(c_8, plain, (![A_21, B_22, H_28, D_24, C_23, I_29, G_27, F_26, E_25]: (k2_xboole_0(k3_enumset1(A_21, B_22, C_23, D_24, E_25), k2_enumset1(F_26, G_27, H_28, I_29))=k7_enumset1(A_21, B_22, C_23, D_24, E_25, F_26, G_27, H_28, I_29))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.06/1.27  tff(c_140, plain, (![D_70, I_75, C_74, G_76, F_72, E_69, B_71, H_73, A_68]: (k7_enumset1(E_69, F_72, G_76, H_73, I_75, A_68, B_71, C_74, D_70)=k7_enumset1(A_68, B_71, C_74, D_70, E_69, F_72, G_76, H_73, I_75))), inference(superposition, [status(thm), theory('equality')], [c_134, c_8])).
% 2.06/1.27  tff(c_166, plain, (![F_80, G_78, C_79, B_81, D_84, H_85, A_83, I_77, E_82]: (k7_enumset1(E_82, F_80, G_78, H_85, I_77, A_83, B_81, C_79, D_84)=k7_enumset1(A_83, B_81, C_79, D_84, E_82, F_80, G_78, H_85, I_77))), inference(superposition, [status(thm), theory('equality')], [c_134, c_8])).
% 2.06/1.27  tff(c_178, plain, (![F_80, G_78, C_79, B_81, D_84, H_85, A_83, I_77, E_82]: (k7_enumset1(I_77, A_83, B_81, C_79, D_84, E_82, F_80, G_78, H_85)=k7_enumset1(A_83, B_81, C_79, D_84, E_82, F_80, G_78, H_85, I_77))), inference(superposition, [status(thm), theory('equality')], [c_166, c_140])).
% 2.06/1.27  tff(c_4, plain, (![A_3, F_8, D_6, I_11, C_5, H_10, G_9, E_7, B_4]: (k2_xboole_0(k2_tarski(A_3, B_4), k5_enumset1(C_5, D_6, E_7, F_8, G_9, H_10, I_11))=k7_enumset1(A_3, B_4, C_5, D_6, E_7, F_8, G_9, H_10, I_11))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.06/1.27  tff(c_10, plain, (k2_xboole_0(k5_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'), k2_tarski('#skF_8', '#skF_9'))!=k7_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_9')), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.06/1.27  tff(c_11, plain, (k2_xboole_0(k2_tarski('#skF_8', '#skF_9'), k5_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'))!=k7_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_10])).
% 2.06/1.27  tff(c_12, plain, (k7_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_9')!=k7_enumset1('#skF_8', '#skF_9', '#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_11])).
% 2.06/1.27  tff(c_165, plain, (k7_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_9')!=k7_enumset1('#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_9', '#skF_1', '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_140, c_12])).
% 2.06/1.27  tff(c_195, plain, (k7_enumset1('#skF_8', '#skF_9', '#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7')!=k7_enumset1('#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_9', '#skF_1', '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_178, c_178, c_165])).
% 2.06/1.27  tff(c_198, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_140, c_195])).
% 2.06/1.27  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.06/1.27  
% 2.06/1.27  Inference rules
% 2.06/1.27  ----------------------
% 2.06/1.27  #Ref     : 0
% 2.06/1.27  #Sup     : 48
% 2.06/1.27  #Fact    : 0
% 2.06/1.27  #Define  : 0
% 2.06/1.27  #Split   : 0
% 2.06/1.27  #Chain   : 0
% 2.06/1.27  #Close   : 0
% 2.06/1.27  
% 2.06/1.27  Ordering : KBO
% 2.06/1.27  
% 2.06/1.27  Simplification rules
% 2.06/1.27  ----------------------
% 2.06/1.27  #Subsume      : 1
% 2.06/1.27  #Demod        : 14
% 2.06/1.27  #Tautology    : 30
% 2.06/1.27  #SimpNegUnit  : 0
% 2.06/1.27  #BackRed      : 2
% 2.06/1.27  
% 2.06/1.27  #Partial instantiations: 0
% 2.06/1.27  #Strategies tried      : 1
% 2.06/1.27  
% 2.06/1.27  Timing (in seconds)
% 2.06/1.27  ----------------------
% 2.06/1.28  Preprocessing        : 0.26
% 2.06/1.28  Parsing              : 0.14
% 2.06/1.28  CNF conversion       : 0.02
% 2.06/1.28  Main loop            : 0.19
% 2.06/1.28  Inferencing          : 0.08
% 2.06/1.28  Reduction            : 0.07
% 2.06/1.28  Demodulation         : 0.06
% 2.06/1.28  BG Simplification    : 0.01
% 2.06/1.28  Subsumption          : 0.02
% 2.06/1.28  Abstraction          : 0.02
% 2.06/1.28  MUC search           : 0.00
% 2.06/1.28  Cooper               : 0.00
% 2.06/1.28  Total                : 0.47
% 2.06/1.28  Index Insertion      : 0.00
% 2.06/1.28  Index Deletion       : 0.00
% 2.06/1.28  Index Matching       : 0.00
% 2.06/1.28  BG Taut test         : 0.00
%------------------------------------------------------------------------------

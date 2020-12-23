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
% DateTime   : Thu Dec  3 09:45:49 EST 2020

% Result     : Theorem 2.69s
% Output     : CNFRefutation 3.02s
% Verified   : 
% Statistics : Number of formulae       :   39 (  51 expanded)
%              Number of leaves         :   23 (  29 expanded)
%              Depth                    :    8
%              Number of atoms          :   22 (  34 expanded)
%              Number of equality atoms :   21 (  33 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k5_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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
    ! [A,B,C,D,E,F,G] : k5_enumset1(A,B,C,D,E,F,G) = k2_xboole_0(k2_tarski(A,B),k3_enumset1(C,D,E,F,G)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_enumset1)).

tff(f_31,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_xboole_0(k1_tarski(A),k1_tarski(B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).

tff(f_27,axiom,(
    ! [A,B,C] : k2_xboole_0(k2_xboole_0(A,B),C) = k2_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).

tff(f_35,axiom,(
    ! [A,B,C,D,E] : k3_enumset1(A,B,C,D,E) = k2_xboole_0(k1_tarski(A),k2_enumset1(B,C,D,E)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_enumset1)).

tff(f_33,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k2_xboole_0(k2_tarski(A,B),k1_tarski(C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_enumset1)).

tff(f_40,negated_conjecture,(
    ~ ! [A,B,C,D,E,F,G] : k5_enumset1(A,B,C,D,E,F,G) = k2_xboole_0(k1_enumset1(A,B,C),k2_enumset1(D,E,F,G)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_enumset1)).

tff(c_12,plain,(
    ! [E_22,G_24,D_21,F_23,A_18,C_20,B_19] : k2_xboole_0(k2_tarski(A_18,B_19),k3_enumset1(C_20,D_21,E_22,F_23,G_24)) = k5_enumset1(A_18,B_19,C_20,D_21,E_22,F_23,G_24) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_6,plain,(
    ! [A_8,B_9] : k2_xboole_0(k1_tarski(A_8),k1_tarski(B_9)) = k2_tarski(A_8,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_33,plain,(
    ! [A_30,B_31,C_32] : k2_xboole_0(k2_xboole_0(A_30,B_31),C_32) = k2_xboole_0(A_30,k2_xboole_0(B_31,C_32)) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_51,plain,(
    ! [A_8,B_9,C_32] : k2_xboole_0(k1_tarski(A_8),k2_xboole_0(k1_tarski(B_9),C_32)) = k2_xboole_0(k2_tarski(A_8,B_9),C_32) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_33])).

tff(c_91,plain,(
    ! [D_40,C_44,E_42,A_43,B_41] : k2_xboole_0(k1_tarski(A_43),k2_enumset1(B_41,C_44,D_40,E_42)) = k3_enumset1(A_43,B_41,C_44,D_40,E_42) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_411,plain,(
    ! [A_116,A_115,D_113,E_114,C_118,B_117] : k2_xboole_0(k2_tarski(A_115,A_116),k2_enumset1(B_117,C_118,D_113,E_114)) = k2_xboole_0(k1_tarski(A_115),k3_enumset1(A_116,B_117,C_118,D_113,E_114)) ),
    inference(superposition,[status(thm),theory(equality)],[c_91,c_51])).

tff(c_8,plain,(
    ! [A_10,B_11,C_12] : k2_xboole_0(k2_tarski(A_10,B_11),k1_tarski(C_12)) = k1_enumset1(A_10,B_11,C_12) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_68,plain,(
    ! [A_37,B_38,C_39] : k2_xboole_0(k1_tarski(A_37),k2_xboole_0(k1_tarski(B_38),C_39)) = k2_xboole_0(k2_tarski(A_37,B_38),C_39) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_33])).

tff(c_86,plain,(
    ! [A_37,A_8,B_9] : k2_xboole_0(k2_tarski(A_37,A_8),k1_tarski(B_9)) = k2_xboole_0(k1_tarski(A_37),k2_tarski(A_8,B_9)) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_68])).

tff(c_106,plain,(
    ! [A_45,A_46,B_47] : k2_xboole_0(k1_tarski(A_45),k2_tarski(A_46,B_47)) = k1_enumset1(A_45,A_46,B_47) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_86])).

tff(c_2,plain,(
    ! [A_1,B_2,C_3] : k2_xboole_0(k2_xboole_0(A_1,B_2),C_3) = k2_xboole_0(A_1,k2_xboole_0(B_2,C_3)) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_115,plain,(
    ! [A_45,A_46,B_47,C_3] : k2_xboole_0(k1_tarski(A_45),k2_xboole_0(k2_tarski(A_46,B_47),C_3)) = k2_xboole_0(k1_enumset1(A_45,A_46,B_47),C_3) ),
    inference(superposition,[status(thm),theory(equality)],[c_106,c_2])).

tff(c_420,plain,(
    ! [A_116,A_45,A_115,D_113,E_114,C_118,B_117] : k2_xboole_0(k1_tarski(A_45),k2_xboole_0(k1_tarski(A_115),k3_enumset1(A_116,B_117,C_118,D_113,E_114))) = k2_xboole_0(k1_enumset1(A_45,A_115,A_116),k2_enumset1(B_117,C_118,D_113,E_114)) ),
    inference(superposition,[status(thm),theory(equality)],[c_411,c_115])).

tff(c_429,plain,(
    ! [A_116,A_45,A_115,D_113,E_114,C_118,B_117] : k2_xboole_0(k1_enumset1(A_45,A_115,A_116),k2_enumset1(B_117,C_118,D_113,E_114)) = k5_enumset1(A_45,A_115,A_116,B_117,C_118,D_113,E_114) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_51,c_420])).

tff(c_14,plain,(
    k2_xboole_0(k1_enumset1('#skF_1','#skF_2','#skF_3'),k2_enumset1('#skF_4','#skF_5','#skF_6','#skF_7')) != k5_enumset1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_539,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_429,c_14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:29:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.69/1.49  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.69/1.49  
% 2.69/1.49  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.02/1.50  %$ k5_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.02/1.50  
% 3.02/1.50  %Foreground sorts:
% 3.02/1.50  
% 3.02/1.50  
% 3.02/1.50  %Background operators:
% 3.02/1.50  
% 3.02/1.50  
% 3.02/1.50  %Foreground operators:
% 3.02/1.50  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.02/1.50  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.02/1.50  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.02/1.50  tff('#skF_7', type, '#skF_7': $i).
% 3.02/1.50  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.02/1.50  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.02/1.50  tff('#skF_5', type, '#skF_5': $i).
% 3.02/1.50  tff('#skF_6', type, '#skF_6': $i).
% 3.02/1.50  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.02/1.50  tff('#skF_2', type, '#skF_2': $i).
% 3.02/1.50  tff('#skF_3', type, '#skF_3': $i).
% 3.02/1.50  tff('#skF_1', type, '#skF_1': $i).
% 3.02/1.50  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.02/1.50  tff('#skF_4', type, '#skF_4': $i).
% 3.02/1.50  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.02/1.50  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.02/1.50  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.02/1.50  
% 3.02/1.51  tff(f_37, axiom, (![A, B, C, D, E, F, G]: (k5_enumset1(A, B, C, D, E, F, G) = k2_xboole_0(k2_tarski(A, B), k3_enumset1(C, D, E, F, G)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t57_enumset1)).
% 3.02/1.51  tff(f_31, axiom, (![A, B]: (k2_tarski(A, B) = k2_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_enumset1)).
% 3.02/1.51  tff(f_27, axiom, (![A, B, C]: (k2_xboole_0(k2_xboole_0(A, B), C) = k2_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_1)).
% 3.02/1.51  tff(f_35, axiom, (![A, B, C, D, E]: (k3_enumset1(A, B, C, D, E) = k2_xboole_0(k1_tarski(A), k2_enumset1(B, C, D, E)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_enumset1)).
% 3.02/1.51  tff(f_33, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k2_xboole_0(k2_tarski(A, B), k1_tarski(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_enumset1)).
% 3.02/1.51  tff(f_40, negated_conjecture, ~(![A, B, C, D, E, F, G]: (k5_enumset1(A, B, C, D, E, F, G) = k2_xboole_0(k1_enumset1(A, B, C), k2_enumset1(D, E, F, G)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t58_enumset1)).
% 3.02/1.51  tff(c_12, plain, (![E_22, G_24, D_21, F_23, A_18, C_20, B_19]: (k2_xboole_0(k2_tarski(A_18, B_19), k3_enumset1(C_20, D_21, E_22, F_23, G_24))=k5_enumset1(A_18, B_19, C_20, D_21, E_22, F_23, G_24))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.02/1.51  tff(c_6, plain, (![A_8, B_9]: (k2_xboole_0(k1_tarski(A_8), k1_tarski(B_9))=k2_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.02/1.51  tff(c_33, plain, (![A_30, B_31, C_32]: (k2_xboole_0(k2_xboole_0(A_30, B_31), C_32)=k2_xboole_0(A_30, k2_xboole_0(B_31, C_32)))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.02/1.51  tff(c_51, plain, (![A_8, B_9, C_32]: (k2_xboole_0(k1_tarski(A_8), k2_xboole_0(k1_tarski(B_9), C_32))=k2_xboole_0(k2_tarski(A_8, B_9), C_32))), inference(superposition, [status(thm), theory('equality')], [c_6, c_33])).
% 3.02/1.51  tff(c_91, plain, (![D_40, C_44, E_42, A_43, B_41]: (k2_xboole_0(k1_tarski(A_43), k2_enumset1(B_41, C_44, D_40, E_42))=k3_enumset1(A_43, B_41, C_44, D_40, E_42))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.02/1.51  tff(c_411, plain, (![A_116, A_115, D_113, E_114, C_118, B_117]: (k2_xboole_0(k2_tarski(A_115, A_116), k2_enumset1(B_117, C_118, D_113, E_114))=k2_xboole_0(k1_tarski(A_115), k3_enumset1(A_116, B_117, C_118, D_113, E_114)))), inference(superposition, [status(thm), theory('equality')], [c_91, c_51])).
% 3.02/1.51  tff(c_8, plain, (![A_10, B_11, C_12]: (k2_xboole_0(k2_tarski(A_10, B_11), k1_tarski(C_12))=k1_enumset1(A_10, B_11, C_12))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.02/1.51  tff(c_68, plain, (![A_37, B_38, C_39]: (k2_xboole_0(k1_tarski(A_37), k2_xboole_0(k1_tarski(B_38), C_39))=k2_xboole_0(k2_tarski(A_37, B_38), C_39))), inference(superposition, [status(thm), theory('equality')], [c_6, c_33])).
% 3.02/1.51  tff(c_86, plain, (![A_37, A_8, B_9]: (k2_xboole_0(k2_tarski(A_37, A_8), k1_tarski(B_9))=k2_xboole_0(k1_tarski(A_37), k2_tarski(A_8, B_9)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_68])).
% 3.02/1.51  tff(c_106, plain, (![A_45, A_46, B_47]: (k2_xboole_0(k1_tarski(A_45), k2_tarski(A_46, B_47))=k1_enumset1(A_45, A_46, B_47))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_86])).
% 3.02/1.51  tff(c_2, plain, (![A_1, B_2, C_3]: (k2_xboole_0(k2_xboole_0(A_1, B_2), C_3)=k2_xboole_0(A_1, k2_xboole_0(B_2, C_3)))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.02/1.51  tff(c_115, plain, (![A_45, A_46, B_47, C_3]: (k2_xboole_0(k1_tarski(A_45), k2_xboole_0(k2_tarski(A_46, B_47), C_3))=k2_xboole_0(k1_enumset1(A_45, A_46, B_47), C_3))), inference(superposition, [status(thm), theory('equality')], [c_106, c_2])).
% 3.02/1.51  tff(c_420, plain, (![A_116, A_45, A_115, D_113, E_114, C_118, B_117]: (k2_xboole_0(k1_tarski(A_45), k2_xboole_0(k1_tarski(A_115), k3_enumset1(A_116, B_117, C_118, D_113, E_114)))=k2_xboole_0(k1_enumset1(A_45, A_115, A_116), k2_enumset1(B_117, C_118, D_113, E_114)))), inference(superposition, [status(thm), theory('equality')], [c_411, c_115])).
% 3.02/1.51  tff(c_429, plain, (![A_116, A_45, A_115, D_113, E_114, C_118, B_117]: (k2_xboole_0(k1_enumset1(A_45, A_115, A_116), k2_enumset1(B_117, C_118, D_113, E_114))=k5_enumset1(A_45, A_115, A_116, B_117, C_118, D_113, E_114))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_51, c_420])).
% 3.02/1.51  tff(c_14, plain, (k2_xboole_0(k1_enumset1('#skF_1', '#skF_2', '#skF_3'), k2_enumset1('#skF_4', '#skF_5', '#skF_6', '#skF_7'))!=k5_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.02/1.51  tff(c_539, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_429, c_14])).
% 3.02/1.51  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.02/1.51  
% 3.02/1.51  Inference rules
% 3.02/1.51  ----------------------
% 3.02/1.51  #Ref     : 0
% 3.02/1.51  #Sup     : 135
% 3.02/1.51  #Fact    : 0
% 3.02/1.51  #Define  : 0
% 3.02/1.51  #Split   : 0
% 3.02/1.51  #Chain   : 0
% 3.02/1.51  #Close   : 0
% 3.02/1.51  
% 3.02/1.51  Ordering : KBO
% 3.02/1.51  
% 3.02/1.51  Simplification rules
% 3.02/1.51  ----------------------
% 3.02/1.51  #Subsume      : 0
% 3.02/1.51  #Demod        : 73
% 3.02/1.51  #Tautology    : 71
% 3.02/1.51  #SimpNegUnit  : 0
% 3.02/1.51  #BackRed      : 2
% 3.02/1.51  
% 3.02/1.51  #Partial instantiations: 0
% 3.02/1.51  #Strategies tried      : 1
% 3.02/1.51  
% 3.02/1.52  Timing (in seconds)
% 3.02/1.52  ----------------------
% 3.02/1.52  Preprocessing        : 0.30
% 3.02/1.52  Parsing              : 0.16
% 3.02/1.52  CNF conversion       : 0.02
% 3.02/1.52  Main loop            : 0.39
% 3.02/1.52  Inferencing          : 0.18
% 3.02/1.52  Reduction            : 0.13
% 3.02/1.52  Demodulation         : 0.11
% 3.02/1.52  BG Simplification    : 0.03
% 3.02/1.52  Subsumption          : 0.04
% 3.02/1.52  Abstraction          : 0.03
% 3.02/1.52  MUC search           : 0.00
% 3.02/1.52  Cooper               : 0.00
% 3.02/1.52  Total                : 0.72
% 3.02/1.52  Index Insertion      : 0.00
% 3.02/1.52  Index Deletion       : 0.00
% 3.02/1.52  Index Matching       : 0.00
% 3.02/1.52  BG Taut test         : 0.00
%------------------------------------------------------------------------------

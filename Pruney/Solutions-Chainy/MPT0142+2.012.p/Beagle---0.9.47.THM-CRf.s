%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:45:50 EST 2020

% Result     : Theorem 3.43s
% Output     : CNFRefutation 3.43s
% Verified   : 
% Statistics : Number of formulae       :   40 (  45 expanded)
%              Number of leaves         :   26 (  29 expanded)
%              Depth                    :    6
%              Number of atoms          :   20 (  25 expanded)
%              Number of equality atoms :   19 (  24 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(f_41,axiom,(
    ! [A,B,C,D,E,F,G] : k5_enumset1(A,B,C,D,E,F,G) = k2_xboole_0(k2_tarski(A,B),k3_enumset1(C,D,E,F,G)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_enumset1)).

tff(f_33,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_xboole_0(k1_tarski(A),k1_tarski(B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).

tff(f_27,axiom,(
    ! [A,B,C] : k2_xboole_0(k2_xboole_0(A,B),C) = k2_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).

tff(f_37,axiom,(
    ! [A,B,C,D,E] : k3_enumset1(A,B,C,D,E) = k2_xboole_0(k1_tarski(A),k2_enumset1(B,C,D,E)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_enumset1)).

tff(f_35,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k2_xboole_0(k1_tarski(A),k2_tarski(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_enumset1)).

tff(f_44,negated_conjecture,(
    ~ ! [A,B,C,D,E,F,G] : k5_enumset1(A,B,C,D,E,F,G) = k2_xboole_0(k1_enumset1(A,B,C),k2_enumset1(D,E,F,G)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t58_enumset1)).

tff(c_16,plain,(
    ! [B_27,D_29,G_32,A_26,E_30,F_31,C_28] : k2_xboole_0(k2_tarski(A_26,B_27),k3_enumset1(C_28,D_29,E_30,F_31,G_32)) = k5_enumset1(A_26,B_27,C_28,D_29,E_30,F_31,G_32) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_8,plain,(
    ! [A_9,B_10] : k2_xboole_0(k1_tarski(A_9),k1_tarski(B_10)) = k2_tarski(A_9,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_65,plain,(
    ! [A_40,B_41,C_42] : k2_xboole_0(k2_xboole_0(A_40,B_41),C_42) = k2_xboole_0(A_40,k2_xboole_0(B_41,C_42)) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_80,plain,(
    ! [A_9,B_10,C_42] : k2_xboole_0(k1_tarski(A_9),k2_xboole_0(k1_tarski(B_10),C_42)) = k2_xboole_0(k2_tarski(A_9,B_10),C_42) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_65])).

tff(c_12,plain,(
    ! [E_18,C_16,D_17,A_14,B_15] : k2_xboole_0(k1_tarski(A_14),k2_enumset1(B_15,C_16,D_17,E_18)) = k3_enumset1(A_14,B_15,C_16,D_17,E_18) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_142,plain,(
    ! [A_54,B_55,C_56] : k2_xboole_0(k1_tarski(A_54),k2_xboole_0(k1_tarski(B_55),C_56)) = k2_xboole_0(k2_tarski(A_54,B_55),C_56) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_65])).

tff(c_851,plain,(
    ! [A_124,B_126,C_125,A_127,E_122,D_123] : k2_xboole_0(k2_tarski(A_124,A_127),k2_enumset1(B_126,C_125,D_123,E_122)) = k2_xboole_0(k1_tarski(A_124),k3_enumset1(A_127,B_126,C_125,D_123,E_122)) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_142])).

tff(c_85,plain,(
    ! [A_43,B_44,C_45] : k2_xboole_0(k1_tarski(A_43),k2_tarski(B_44,C_45)) = k1_enumset1(A_43,B_44,C_45) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_2,plain,(
    ! [A_1,B_2,C_3] : k2_xboole_0(k2_xboole_0(A_1,B_2),C_3) = k2_xboole_0(A_1,k2_xboole_0(B_2,C_3)) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_91,plain,(
    ! [A_43,B_44,C_45,C_3] : k2_xboole_0(k1_tarski(A_43),k2_xboole_0(k2_tarski(B_44,C_45),C_3)) = k2_xboole_0(k1_enumset1(A_43,B_44,C_45),C_3) ),
    inference(superposition,[status(thm),theory(equality)],[c_85,c_2])).

tff(c_872,plain,(
    ! [A_124,B_126,C_125,A_127,E_122,D_123,A_43] : k2_xboole_0(k1_tarski(A_43),k2_xboole_0(k1_tarski(A_124),k3_enumset1(A_127,B_126,C_125,D_123,E_122))) = k2_xboole_0(k1_enumset1(A_43,A_124,A_127),k2_enumset1(B_126,C_125,D_123,E_122)) ),
    inference(superposition,[status(thm),theory(equality)],[c_851,c_91])).

tff(c_883,plain,(
    ! [A_124,B_126,C_125,A_127,E_122,D_123,A_43] : k2_xboole_0(k1_enumset1(A_43,A_124,A_127),k2_enumset1(B_126,C_125,D_123,E_122)) = k5_enumset1(A_43,A_124,A_127,B_126,C_125,D_123,E_122) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_80,c_872])).

tff(c_18,plain,(
    k2_xboole_0(k1_enumset1('#skF_1','#skF_2','#skF_3'),k2_enumset1('#skF_4','#skF_5','#skF_6','#skF_7')) != k5_enumset1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_889,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_883,c_18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n006.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 17:43:07 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.43/1.50  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.43/1.50  
% 3.43/1.50  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.43/1.50  %$ k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.43/1.50  
% 3.43/1.50  %Foreground sorts:
% 3.43/1.50  
% 3.43/1.50  
% 3.43/1.50  %Background operators:
% 3.43/1.50  
% 3.43/1.50  
% 3.43/1.50  %Foreground operators:
% 3.43/1.50  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.43/1.50  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.43/1.50  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.43/1.50  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.43/1.50  tff('#skF_7', type, '#skF_7': $i).
% 3.43/1.50  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.43/1.50  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.43/1.50  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.43/1.50  tff('#skF_5', type, '#skF_5': $i).
% 3.43/1.50  tff('#skF_6', type, '#skF_6': $i).
% 3.43/1.50  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.43/1.50  tff('#skF_2', type, '#skF_2': $i).
% 3.43/1.50  tff('#skF_3', type, '#skF_3': $i).
% 3.43/1.50  tff('#skF_1', type, '#skF_1': $i).
% 3.43/1.50  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.43/1.50  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.43/1.50  tff('#skF_4', type, '#skF_4': $i).
% 3.43/1.50  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.43/1.50  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.43/1.50  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.43/1.50  
% 3.43/1.51  tff(f_41, axiom, (![A, B, C, D, E, F, G]: (k5_enumset1(A, B, C, D, E, F, G) = k2_xboole_0(k2_tarski(A, B), k3_enumset1(C, D, E, F, G)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t57_enumset1)).
% 3.43/1.51  tff(f_33, axiom, (![A, B]: (k2_tarski(A, B) = k2_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_enumset1)).
% 3.43/1.51  tff(f_27, axiom, (![A, B, C]: (k2_xboole_0(k2_xboole_0(A, B), C) = k2_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_1)).
% 3.43/1.51  tff(f_37, axiom, (![A, B, C, D, E]: (k3_enumset1(A, B, C, D, E) = k2_xboole_0(k1_tarski(A), k2_enumset1(B, C, D, E)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_enumset1)).
% 3.43/1.51  tff(f_35, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k2_xboole_0(k1_tarski(A), k2_tarski(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t42_enumset1)).
% 3.43/1.51  tff(f_44, negated_conjecture, ~(![A, B, C, D, E, F, G]: (k5_enumset1(A, B, C, D, E, F, G) = k2_xboole_0(k1_enumset1(A, B, C), k2_enumset1(D, E, F, G)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t58_enumset1)).
% 3.43/1.51  tff(c_16, plain, (![B_27, D_29, G_32, A_26, E_30, F_31, C_28]: (k2_xboole_0(k2_tarski(A_26, B_27), k3_enumset1(C_28, D_29, E_30, F_31, G_32))=k5_enumset1(A_26, B_27, C_28, D_29, E_30, F_31, G_32))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.43/1.51  tff(c_8, plain, (![A_9, B_10]: (k2_xboole_0(k1_tarski(A_9), k1_tarski(B_10))=k2_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.43/1.51  tff(c_65, plain, (![A_40, B_41, C_42]: (k2_xboole_0(k2_xboole_0(A_40, B_41), C_42)=k2_xboole_0(A_40, k2_xboole_0(B_41, C_42)))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.43/1.51  tff(c_80, plain, (![A_9, B_10, C_42]: (k2_xboole_0(k1_tarski(A_9), k2_xboole_0(k1_tarski(B_10), C_42))=k2_xboole_0(k2_tarski(A_9, B_10), C_42))), inference(superposition, [status(thm), theory('equality')], [c_8, c_65])).
% 3.43/1.51  tff(c_12, plain, (![E_18, C_16, D_17, A_14, B_15]: (k2_xboole_0(k1_tarski(A_14), k2_enumset1(B_15, C_16, D_17, E_18))=k3_enumset1(A_14, B_15, C_16, D_17, E_18))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.43/1.51  tff(c_142, plain, (![A_54, B_55, C_56]: (k2_xboole_0(k1_tarski(A_54), k2_xboole_0(k1_tarski(B_55), C_56))=k2_xboole_0(k2_tarski(A_54, B_55), C_56))), inference(superposition, [status(thm), theory('equality')], [c_8, c_65])).
% 3.43/1.51  tff(c_851, plain, (![A_124, B_126, C_125, A_127, E_122, D_123]: (k2_xboole_0(k2_tarski(A_124, A_127), k2_enumset1(B_126, C_125, D_123, E_122))=k2_xboole_0(k1_tarski(A_124), k3_enumset1(A_127, B_126, C_125, D_123, E_122)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_142])).
% 3.43/1.51  tff(c_85, plain, (![A_43, B_44, C_45]: (k2_xboole_0(k1_tarski(A_43), k2_tarski(B_44, C_45))=k1_enumset1(A_43, B_44, C_45))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.43/1.51  tff(c_2, plain, (![A_1, B_2, C_3]: (k2_xboole_0(k2_xboole_0(A_1, B_2), C_3)=k2_xboole_0(A_1, k2_xboole_0(B_2, C_3)))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.43/1.51  tff(c_91, plain, (![A_43, B_44, C_45, C_3]: (k2_xboole_0(k1_tarski(A_43), k2_xboole_0(k2_tarski(B_44, C_45), C_3))=k2_xboole_0(k1_enumset1(A_43, B_44, C_45), C_3))), inference(superposition, [status(thm), theory('equality')], [c_85, c_2])).
% 3.43/1.51  tff(c_872, plain, (![A_124, B_126, C_125, A_127, E_122, D_123, A_43]: (k2_xboole_0(k1_tarski(A_43), k2_xboole_0(k1_tarski(A_124), k3_enumset1(A_127, B_126, C_125, D_123, E_122)))=k2_xboole_0(k1_enumset1(A_43, A_124, A_127), k2_enumset1(B_126, C_125, D_123, E_122)))), inference(superposition, [status(thm), theory('equality')], [c_851, c_91])).
% 3.43/1.51  tff(c_883, plain, (![A_124, B_126, C_125, A_127, E_122, D_123, A_43]: (k2_xboole_0(k1_enumset1(A_43, A_124, A_127), k2_enumset1(B_126, C_125, D_123, E_122))=k5_enumset1(A_43, A_124, A_127, B_126, C_125, D_123, E_122))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_80, c_872])).
% 3.43/1.51  tff(c_18, plain, (k2_xboole_0(k1_enumset1('#skF_1', '#skF_2', '#skF_3'), k2_enumset1('#skF_4', '#skF_5', '#skF_6', '#skF_7'))!=k5_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.43/1.51  tff(c_889, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_883, c_18])).
% 3.43/1.51  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.43/1.51  
% 3.43/1.51  Inference rules
% 3.43/1.51  ----------------------
% 3.43/1.51  #Ref     : 0
% 3.43/1.51  #Sup     : 219
% 3.43/1.51  #Fact    : 0
% 3.43/1.51  #Define  : 0
% 3.43/1.51  #Split   : 0
% 3.43/1.51  #Chain   : 0
% 3.43/1.51  #Close   : 0
% 3.43/1.51  
% 3.43/1.51  Ordering : KBO
% 3.43/1.51  
% 3.43/1.51  Simplification rules
% 3.43/1.51  ----------------------
% 3.43/1.51  #Subsume      : 0
% 3.43/1.51  #Demod        : 303
% 3.43/1.51  #Tautology    : 103
% 3.43/1.51  #SimpNegUnit  : 0
% 3.43/1.51  #BackRed      : 1
% 3.43/1.51  
% 3.43/1.51  #Partial instantiations: 0
% 3.43/1.51  #Strategies tried      : 1
% 3.43/1.51  
% 3.43/1.51  Timing (in seconds)
% 3.43/1.51  ----------------------
% 3.43/1.52  Preprocessing        : 0.29
% 3.43/1.52  Parsing              : 0.16
% 3.43/1.52  CNF conversion       : 0.02
% 3.43/1.52  Main loop            : 0.47
% 3.43/1.52  Inferencing          : 0.19
% 3.43/1.52  Reduction            : 0.19
% 3.43/1.52  Demodulation         : 0.16
% 3.43/1.52  BG Simplification    : 0.03
% 3.43/1.52  Subsumption          : 0.05
% 3.43/1.52  Abstraction          : 0.04
% 3.43/1.52  MUC search           : 0.00
% 3.43/1.52  Cooper               : 0.00
% 3.43/1.52  Total                : 0.79
% 3.43/1.52  Index Insertion      : 0.00
% 3.43/1.52  Index Deletion       : 0.00
% 3.52/1.52  Index Matching       : 0.00
% 3.52/1.52  BG Taut test         : 0.00
%------------------------------------------------------------------------------

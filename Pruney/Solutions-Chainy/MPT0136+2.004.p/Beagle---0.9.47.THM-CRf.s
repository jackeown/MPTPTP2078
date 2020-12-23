%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:45:44 EST 2020

% Result     : Theorem 2.05s
% Output     : CNFRefutation 2.05s
% Verified   : 
% Statistics : Number of formulae       :   35 (  41 expanded)
%              Number of leaves         :   22 (  25 expanded)
%              Depth                    :    6
%              Number of atoms          :   19 (  25 expanded)
%              Number of equality atoms :   18 (  24 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

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

tff(f_29,axiom,(
    ! [A,B,C,D,E,F] : k4_enumset1(A,B,C,D,E,F) = k2_xboole_0(k1_enumset1(A,B,C),k1_enumset1(D,E,F)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l62_enumset1)).

tff(f_31,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_xboole_0(k1_tarski(A),k1_tarski(B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).

tff(f_27,axiom,(
    ! [A,B,C] : k2_xboole_0(k2_xboole_0(A,B),C) = k2_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).

tff(f_35,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k1_tarski(A),k1_enumset1(B,C,D)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_enumset1)).

tff(f_33,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k2_xboole_0(k1_tarski(A),k2_tarski(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_enumset1)).

tff(f_40,negated_conjecture,(
    ~ ! [A,B,C,D,E,F] : k4_enumset1(A,B,C,D,E,F) = k2_xboole_0(k2_tarski(A,B),k2_enumset1(C,D,E,F)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_enumset1)).

tff(c_4,plain,(
    ! [B_5,D_7,A_4,E_8,C_6,F_9] : k2_xboole_0(k1_enumset1(A_4,B_5,C_6),k1_enumset1(D_7,E_8,F_9)) = k4_enumset1(A_4,B_5,C_6,D_7,E_8,F_9) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_6,plain,(
    ! [A_10,B_11] : k2_xboole_0(k1_tarski(A_10),k1_tarski(B_11)) = k2_tarski(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_33,plain,(
    ! [A_30,B_31,C_32] : k2_xboole_0(k2_xboole_0(A_30,B_31),C_32) = k2_xboole_0(A_30,k2_xboole_0(B_31,C_32)) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_51,plain,(
    ! [A_10,B_11,C_32] : k2_xboole_0(k1_tarski(A_10),k2_xboole_0(k1_tarski(B_11),C_32)) = k2_xboole_0(k2_tarski(A_10,B_11),C_32) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_33])).

tff(c_10,plain,(
    ! [A_15,B_16,C_17,D_18] : k2_xboole_0(k1_tarski(A_15),k1_enumset1(B_16,C_17,D_18)) = k2_enumset1(A_15,B_16,C_17,D_18) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_68,plain,(
    ! [A_37,B_38,C_39] : k2_xboole_0(k1_tarski(A_37),k2_xboole_0(k1_tarski(B_38),C_39)) = k2_xboole_0(k2_tarski(A_37,B_38),C_39) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_33])).

tff(c_274,plain,(
    ! [A_87,D_85,C_83,A_84,B_86] : k2_xboole_0(k2_tarski(A_84,A_87),k1_enumset1(B_86,C_83,D_85)) = k2_xboole_0(k1_tarski(A_84),k2_enumset1(A_87,B_86,C_83,D_85)) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_68])).

tff(c_8,plain,(
    ! [A_12,B_13,C_14] : k2_xboole_0(k1_tarski(A_12),k2_tarski(B_13,C_14)) = k1_enumset1(A_12,B_13,C_14) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_48,plain,(
    ! [A_12,B_13,C_14,C_32] : k2_xboole_0(k1_tarski(A_12),k2_xboole_0(k2_tarski(B_13,C_14),C_32)) = k2_xboole_0(k1_enumset1(A_12,B_13,C_14),C_32) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_33])).

tff(c_280,plain,(
    ! [A_87,D_85,C_83,A_12,A_84,B_86] : k2_xboole_0(k1_tarski(A_12),k2_xboole_0(k1_tarski(A_84),k2_enumset1(A_87,B_86,C_83,D_85))) = k2_xboole_0(k1_enumset1(A_12,A_84,A_87),k1_enumset1(B_86,C_83,D_85)) ),
    inference(superposition,[status(thm),theory(equality)],[c_274,c_48])).

tff(c_288,plain,(
    ! [A_87,D_85,C_83,A_12,A_84,B_86] : k2_xboole_0(k2_tarski(A_12,A_84),k2_enumset1(A_87,B_86,C_83,D_85)) = k4_enumset1(A_12,A_84,A_87,B_86,C_83,D_85) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_51,c_280])).

tff(c_14,plain,(
    k2_xboole_0(k2_tarski('#skF_1','#skF_2'),k2_enumset1('#skF_3','#skF_4','#skF_5','#skF_6')) != k4_enumset1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_349,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_288,c_14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n025.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 13:06:20 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.05/1.30  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.05/1.30  
% 2.05/1.30  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.05/1.31  %$ k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.05/1.31  
% 2.05/1.31  %Foreground sorts:
% 2.05/1.31  
% 2.05/1.31  
% 2.05/1.31  %Background operators:
% 2.05/1.31  
% 2.05/1.31  
% 2.05/1.31  %Foreground operators:
% 2.05/1.31  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.05/1.31  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.05/1.31  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.05/1.31  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.05/1.31  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.05/1.31  tff('#skF_5', type, '#skF_5': $i).
% 2.05/1.31  tff('#skF_6', type, '#skF_6': $i).
% 2.05/1.31  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.05/1.31  tff('#skF_2', type, '#skF_2': $i).
% 2.05/1.31  tff('#skF_3', type, '#skF_3': $i).
% 2.05/1.31  tff('#skF_1', type, '#skF_1': $i).
% 2.05/1.31  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.05/1.31  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.05/1.31  tff('#skF_4', type, '#skF_4': $i).
% 2.05/1.31  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.05/1.31  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.05/1.31  
% 2.05/1.32  tff(f_29, axiom, (![A, B, C, D, E, F]: (k4_enumset1(A, B, C, D, E, F) = k2_xboole_0(k1_enumset1(A, B, C), k1_enumset1(D, E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l62_enumset1)).
% 2.05/1.32  tff(f_31, axiom, (![A, B]: (k2_tarski(A, B) = k2_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_enumset1)).
% 2.05/1.32  tff(f_27, axiom, (![A, B, C]: (k2_xboole_0(k2_xboole_0(A, B), C) = k2_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_1)).
% 2.05/1.32  tff(f_35, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k1_tarski(A), k1_enumset1(B, C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_enumset1)).
% 2.05/1.32  tff(f_33, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k2_xboole_0(k1_tarski(A), k2_tarski(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t42_enumset1)).
% 2.05/1.32  tff(f_40, negated_conjecture, ~(![A, B, C, D, E, F]: (k4_enumset1(A, B, C, D, E, F) = k2_xboole_0(k2_tarski(A, B), k2_enumset1(C, D, E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_enumset1)).
% 2.05/1.32  tff(c_4, plain, (![B_5, D_7, A_4, E_8, C_6, F_9]: (k2_xboole_0(k1_enumset1(A_4, B_5, C_6), k1_enumset1(D_7, E_8, F_9))=k4_enumset1(A_4, B_5, C_6, D_7, E_8, F_9))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.05/1.32  tff(c_6, plain, (![A_10, B_11]: (k2_xboole_0(k1_tarski(A_10), k1_tarski(B_11))=k2_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.05/1.32  tff(c_33, plain, (![A_30, B_31, C_32]: (k2_xboole_0(k2_xboole_0(A_30, B_31), C_32)=k2_xboole_0(A_30, k2_xboole_0(B_31, C_32)))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.05/1.32  tff(c_51, plain, (![A_10, B_11, C_32]: (k2_xboole_0(k1_tarski(A_10), k2_xboole_0(k1_tarski(B_11), C_32))=k2_xboole_0(k2_tarski(A_10, B_11), C_32))), inference(superposition, [status(thm), theory('equality')], [c_6, c_33])).
% 2.05/1.32  tff(c_10, plain, (![A_15, B_16, C_17, D_18]: (k2_xboole_0(k1_tarski(A_15), k1_enumset1(B_16, C_17, D_18))=k2_enumset1(A_15, B_16, C_17, D_18))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.05/1.32  tff(c_68, plain, (![A_37, B_38, C_39]: (k2_xboole_0(k1_tarski(A_37), k2_xboole_0(k1_tarski(B_38), C_39))=k2_xboole_0(k2_tarski(A_37, B_38), C_39))), inference(superposition, [status(thm), theory('equality')], [c_6, c_33])).
% 2.05/1.32  tff(c_274, plain, (![A_87, D_85, C_83, A_84, B_86]: (k2_xboole_0(k2_tarski(A_84, A_87), k1_enumset1(B_86, C_83, D_85))=k2_xboole_0(k1_tarski(A_84), k2_enumset1(A_87, B_86, C_83, D_85)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_68])).
% 2.05/1.32  tff(c_8, plain, (![A_12, B_13, C_14]: (k2_xboole_0(k1_tarski(A_12), k2_tarski(B_13, C_14))=k1_enumset1(A_12, B_13, C_14))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.05/1.32  tff(c_48, plain, (![A_12, B_13, C_14, C_32]: (k2_xboole_0(k1_tarski(A_12), k2_xboole_0(k2_tarski(B_13, C_14), C_32))=k2_xboole_0(k1_enumset1(A_12, B_13, C_14), C_32))), inference(superposition, [status(thm), theory('equality')], [c_8, c_33])).
% 2.05/1.32  tff(c_280, plain, (![A_87, D_85, C_83, A_12, A_84, B_86]: (k2_xboole_0(k1_tarski(A_12), k2_xboole_0(k1_tarski(A_84), k2_enumset1(A_87, B_86, C_83, D_85)))=k2_xboole_0(k1_enumset1(A_12, A_84, A_87), k1_enumset1(B_86, C_83, D_85)))), inference(superposition, [status(thm), theory('equality')], [c_274, c_48])).
% 2.05/1.32  tff(c_288, plain, (![A_87, D_85, C_83, A_12, A_84, B_86]: (k2_xboole_0(k2_tarski(A_12, A_84), k2_enumset1(A_87, B_86, C_83, D_85))=k4_enumset1(A_12, A_84, A_87, B_86, C_83, D_85))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_51, c_280])).
% 2.05/1.32  tff(c_14, plain, (k2_xboole_0(k2_tarski('#skF_1', '#skF_2'), k2_enumset1('#skF_3', '#skF_4', '#skF_5', '#skF_6'))!=k4_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.05/1.32  tff(c_349, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_288, c_14])).
% 2.05/1.32  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.05/1.32  
% 2.05/1.32  Inference rules
% 2.05/1.32  ----------------------
% 2.05/1.32  #Ref     : 0
% 2.05/1.32  #Sup     : 87
% 2.05/1.32  #Fact    : 0
% 2.05/1.32  #Define  : 0
% 2.05/1.32  #Split   : 0
% 2.05/1.32  #Chain   : 0
% 2.05/1.32  #Close   : 0
% 2.05/1.32  
% 2.05/1.32  Ordering : KBO
% 2.05/1.32  
% 2.05/1.32  Simplification rules
% 2.05/1.32  ----------------------
% 2.05/1.32  #Subsume      : 0
% 2.05/1.32  #Demod        : 41
% 2.05/1.32  #Tautology    : 45
% 2.05/1.32  #SimpNegUnit  : 0
% 2.05/1.32  #BackRed      : 1
% 2.05/1.32  
% 2.05/1.32  #Partial instantiations: 0
% 2.05/1.32  #Strategies tried      : 1
% 2.05/1.32  
% 2.05/1.32  Timing (in seconds)
% 2.05/1.32  ----------------------
% 2.05/1.32  Preprocessing        : 0.28
% 2.05/1.32  Parsing              : 0.16
% 2.05/1.32  CNF conversion       : 0.02
% 2.05/1.32  Main loop            : 0.26
% 2.05/1.32  Inferencing          : 0.12
% 2.05/1.32  Reduction            : 0.08
% 2.05/1.32  Demodulation         : 0.07
% 2.05/1.32  BG Simplification    : 0.02
% 2.40/1.32  Subsumption          : 0.03
% 2.40/1.32  Abstraction          : 0.02
% 2.40/1.32  MUC search           : 0.00
% 2.40/1.32  Cooper               : 0.00
% 2.40/1.32  Total                : 0.56
% 2.40/1.32  Index Insertion      : 0.00
% 2.40/1.32  Index Deletion       : 0.00
% 2.40/1.32  Index Matching       : 0.00
% 2.40/1.32  BG Taut test         : 0.00
%------------------------------------------------------------------------------

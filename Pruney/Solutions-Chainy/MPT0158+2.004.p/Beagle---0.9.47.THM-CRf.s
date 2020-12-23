%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:46:19 EST 2020

% Result     : Theorem 2.28s
% Output     : CNFRefutation 2.31s
% Verified   : 
% Statistics : Number of formulae       :   33 (  33 expanded)
%              Number of leaves         :   22 (  22 expanded)
%              Depth                    :    6
%              Number of atoms          :   17 (  17 expanded)
%              Number of equality atoms :   16 (  16 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k5_enumset1 > k4_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

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

tff(f_27,axiom,(
    ! [A,B,C,D,E,F] : k4_enumset1(A,B,C,D,E,F) = k2_xboole_0(k1_enumset1(A,B,C),k1_enumset1(D,E,F)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l62_enumset1)).

tff(f_31,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k2_xboole_0(k2_tarski(A,B),k1_tarski(C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_enumset1)).

tff(f_35,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_33,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k1_enumset1(A,B,C),k1_tarski(D)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_enumset1)).

tff(f_29,axiom,(
    ! [A,B,C,D,E,F,G] : k5_enumset1(A,B,C,D,E,F,G) = k2_xboole_0(k2_enumset1(A,B,C,D),k1_enumset1(E,F,G)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l68_enumset1)).

tff(f_38,negated_conjecture,(
    ~ ! [A,B,C,D,E,F] : k5_enumset1(A,A,B,C,D,E,F) = k4_enumset1(A,B,C,D,E,F) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

tff(c_2,plain,(
    ! [B_2,C_3,A_1,E_5,D_4,F_6] : k2_xboole_0(k1_enumset1(A_1,B_2,C_3),k1_enumset1(D_4,E_5,F_6)) = k4_enumset1(A_1,B_2,C_3,D_4,E_5,F_6) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_6,plain,(
    ! [A_14,B_15,C_16] : k2_xboole_0(k2_tarski(A_14,B_15),k1_tarski(C_16)) = k1_enumset1(A_14,B_15,C_16) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_10,plain,(
    ! [A_21,B_22] : k1_enumset1(A_21,A_21,B_22) = k2_tarski(A_21,B_22) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_31,plain,(
    ! [A_28,B_29,C_30,D_31] : k2_xboole_0(k1_enumset1(A_28,B_29,C_30),k1_tarski(D_31)) = k2_enumset1(A_28,B_29,C_30,D_31) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_40,plain,(
    ! [A_21,B_22,D_31] : k2_xboole_0(k2_tarski(A_21,B_22),k1_tarski(D_31)) = k2_enumset1(A_21,A_21,B_22,D_31) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_31])).

tff(c_43,plain,(
    ! [A_21,B_22,D_31] : k2_enumset1(A_21,A_21,B_22,D_31) = k1_enumset1(A_21,B_22,D_31) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_40])).

tff(c_153,plain,(
    ! [D_55,E_61,A_58,B_56,C_57,G_59,F_60] : k2_xboole_0(k2_enumset1(A_58,B_56,C_57,D_55),k1_enumset1(E_61,F_60,G_59)) = k5_enumset1(A_58,B_56,C_57,D_55,E_61,F_60,G_59) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_162,plain,(
    ! [A_21,B_22,E_61,D_31,G_59,F_60] : k5_enumset1(A_21,A_21,B_22,D_31,E_61,F_60,G_59) = k2_xboole_0(k1_enumset1(A_21,B_22,D_31),k1_enumset1(E_61,F_60,G_59)) ),
    inference(superposition,[status(thm),theory(equality)],[c_43,c_153])).

tff(c_168,plain,(
    ! [A_21,B_22,E_61,D_31,G_59,F_60] : k5_enumset1(A_21,A_21,B_22,D_31,E_61,F_60,G_59) = k4_enumset1(A_21,B_22,D_31,E_61,F_60,G_59) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_162])).

tff(c_12,plain,(
    k5_enumset1('#skF_1','#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6') != k4_enumset1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_171,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_168,c_12])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:06:30 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.28/1.52  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.28/1.53  
% 2.28/1.53  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.31/1.53  %$ k5_enumset1 > k4_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.31/1.53  
% 2.31/1.53  %Foreground sorts:
% 2.31/1.53  
% 2.31/1.53  
% 2.31/1.53  %Background operators:
% 2.31/1.53  
% 2.31/1.53  
% 2.31/1.53  %Foreground operators:
% 2.31/1.53  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.31/1.53  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.31/1.53  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.31/1.53  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.31/1.53  tff('#skF_5', type, '#skF_5': $i).
% 2.31/1.53  tff('#skF_6', type, '#skF_6': $i).
% 2.31/1.53  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.31/1.53  tff('#skF_2', type, '#skF_2': $i).
% 2.31/1.53  tff('#skF_3', type, '#skF_3': $i).
% 2.31/1.53  tff('#skF_1', type, '#skF_1': $i).
% 2.31/1.53  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.31/1.53  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.31/1.53  tff('#skF_4', type, '#skF_4': $i).
% 2.31/1.53  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.31/1.53  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.31/1.53  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.31/1.53  
% 2.31/1.55  tff(f_27, axiom, (![A, B, C, D, E, F]: (k4_enumset1(A, B, C, D, E, F) = k2_xboole_0(k1_enumset1(A, B, C), k1_enumset1(D, E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l62_enumset1)).
% 2.31/1.55  tff(f_31, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k2_xboole_0(k2_tarski(A, B), k1_tarski(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_enumset1)).
% 2.31/1.55  tff(f_35, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 2.31/1.55  tff(f_33, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k1_enumset1(A, B, C), k1_tarski(D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_enumset1)).
% 2.31/1.55  tff(f_29, axiom, (![A, B, C, D, E, F, G]: (k5_enumset1(A, B, C, D, E, F, G) = k2_xboole_0(k2_enumset1(A, B, C, D), k1_enumset1(E, F, G)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l68_enumset1)).
% 2.31/1.55  tff(f_38, negated_conjecture, ~(![A, B, C, D, E, F]: (k5_enumset1(A, A, B, C, D, E, F) = k4_enumset1(A, B, C, D, E, F))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_enumset1)).
% 2.31/1.55  tff(c_2, plain, (![B_2, C_3, A_1, E_5, D_4, F_6]: (k2_xboole_0(k1_enumset1(A_1, B_2, C_3), k1_enumset1(D_4, E_5, F_6))=k4_enumset1(A_1, B_2, C_3, D_4, E_5, F_6))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.31/1.55  tff(c_6, plain, (![A_14, B_15, C_16]: (k2_xboole_0(k2_tarski(A_14, B_15), k1_tarski(C_16))=k1_enumset1(A_14, B_15, C_16))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.31/1.55  tff(c_10, plain, (![A_21, B_22]: (k1_enumset1(A_21, A_21, B_22)=k2_tarski(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.31/1.55  tff(c_31, plain, (![A_28, B_29, C_30, D_31]: (k2_xboole_0(k1_enumset1(A_28, B_29, C_30), k1_tarski(D_31))=k2_enumset1(A_28, B_29, C_30, D_31))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.31/1.55  tff(c_40, plain, (![A_21, B_22, D_31]: (k2_xboole_0(k2_tarski(A_21, B_22), k1_tarski(D_31))=k2_enumset1(A_21, A_21, B_22, D_31))), inference(superposition, [status(thm), theory('equality')], [c_10, c_31])).
% 2.31/1.55  tff(c_43, plain, (![A_21, B_22, D_31]: (k2_enumset1(A_21, A_21, B_22, D_31)=k1_enumset1(A_21, B_22, D_31))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_40])).
% 2.31/1.55  tff(c_153, plain, (![D_55, E_61, A_58, B_56, C_57, G_59, F_60]: (k2_xboole_0(k2_enumset1(A_58, B_56, C_57, D_55), k1_enumset1(E_61, F_60, G_59))=k5_enumset1(A_58, B_56, C_57, D_55, E_61, F_60, G_59))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.31/1.55  tff(c_162, plain, (![A_21, B_22, E_61, D_31, G_59, F_60]: (k5_enumset1(A_21, A_21, B_22, D_31, E_61, F_60, G_59)=k2_xboole_0(k1_enumset1(A_21, B_22, D_31), k1_enumset1(E_61, F_60, G_59)))), inference(superposition, [status(thm), theory('equality')], [c_43, c_153])).
% 2.31/1.55  tff(c_168, plain, (![A_21, B_22, E_61, D_31, G_59, F_60]: (k5_enumset1(A_21, A_21, B_22, D_31, E_61, F_60, G_59)=k4_enumset1(A_21, B_22, D_31, E_61, F_60, G_59))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_162])).
% 2.31/1.55  tff(c_12, plain, (k5_enumset1('#skF_1', '#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')!=k4_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.31/1.55  tff(c_171, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_168, c_12])).
% 2.31/1.55  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.31/1.55  
% 2.31/1.55  Inference rules
% 2.31/1.55  ----------------------
% 2.31/1.55  #Ref     : 0
% 2.31/1.55  #Sup     : 37
% 2.31/1.55  #Fact    : 0
% 2.31/1.55  #Define  : 0
% 2.31/1.55  #Split   : 0
% 2.31/1.55  #Chain   : 0
% 2.31/1.55  #Close   : 0
% 2.31/1.55  
% 2.31/1.55  Ordering : KBO
% 2.31/1.55  
% 2.31/1.55  Simplification rules
% 2.31/1.55  ----------------------
% 2.31/1.55  #Subsume      : 1
% 2.31/1.55  #Demod        : 11
% 2.31/1.55  #Tautology    : 30
% 2.31/1.55  #SimpNegUnit  : 0
% 2.31/1.55  #BackRed      : 1
% 2.31/1.55  
% 2.31/1.55  #Partial instantiations: 0
% 2.31/1.55  #Strategies tried      : 1
% 2.31/1.55  
% 2.31/1.55  Timing (in seconds)
% 2.31/1.55  ----------------------
% 2.31/1.55  Preprocessing        : 0.43
% 2.31/1.55  Parsing              : 0.22
% 2.31/1.55  CNF conversion       : 0.03
% 2.31/1.55  Main loop            : 0.23
% 2.31/1.55  Inferencing          : 0.11
% 2.31/1.55  Reduction            : 0.07
% 2.31/1.55  Demodulation         : 0.06
% 2.31/1.55  BG Simplification    : 0.02
% 2.31/1.55  Subsumption          : 0.02
% 2.31/1.55  Abstraction          : 0.02
% 2.31/1.55  MUC search           : 0.00
% 2.31/1.55  Cooper               : 0.00
% 2.31/1.55  Total                : 0.70
% 2.31/1.55  Index Insertion      : 0.00
% 2.31/1.55  Index Deletion       : 0.00
% 2.31/1.55  Index Matching       : 0.00
% 2.31/1.55  BG Taut test         : 0.00
%------------------------------------------------------------------------------

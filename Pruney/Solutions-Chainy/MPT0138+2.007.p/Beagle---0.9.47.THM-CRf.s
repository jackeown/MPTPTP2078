%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:45:45 EST 2020

% Result     : Theorem 2.06s
% Output     : CNFRefutation 2.06s
% Verified   : 
% Statistics : Number of formulae       :   36 (  38 expanded)
%              Number of leaves         :   21 (  23 expanded)
%              Depth                    :    5
%              Number of atoms          :   21 (  23 expanded)
%              Number of equality atoms :   20 (  22 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k4_enumset1 > k3_enumset1 > k2_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(f_35,axiom,(
    ! [A,B,C,D,E,F] : k4_enumset1(A,B,C,D,E,F) = k2_xboole_0(k1_tarski(A),k3_enumset1(B,C,D,E,F)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_enumset1)).

tff(f_33,axiom,(
    ! [A,B,C,D,E] : k3_enumset1(A,B,C,D,E) = k2_xboole_0(k1_tarski(A),k2_enumset1(B,C,D,E)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_enumset1)).

tff(f_31,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_xboole_0(k1_tarski(A),k1_tarski(B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).

tff(f_27,axiom,(
    ! [A,B,C] : k2_xboole_0(k2_xboole_0(A,B),C) = k2_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).

tff(f_29,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k2_tarski(A,B),k2_tarski(C,D)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l53_enumset1)).

tff(f_38,negated_conjecture,(
    ~ ! [A,B,C,D,E,F] : k4_enumset1(A,B,C,D,E,F) = k2_xboole_0(k2_enumset1(A,B,C,D),k2_tarski(E,F)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_enumset1)).

tff(c_10,plain,(
    ! [B_16,A_15,D_18,E_19,F_20,C_17] : k2_xboole_0(k1_tarski(A_15),k3_enumset1(B_16,C_17,D_18,E_19,F_20)) = k4_enumset1(A_15,B_16,C_17,D_18,E_19,F_20) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_89,plain,(
    ! [D_39,B_36,E_37,A_38,C_40] : k2_xboole_0(k1_tarski(A_38),k2_enumset1(B_36,C_40,D_39,E_37)) = k3_enumset1(A_38,B_36,C_40,D_39,E_37) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_6,plain,(
    ! [A_8,B_9] : k2_xboole_0(k1_tarski(A_8),k1_tarski(B_9)) = k2_tarski(A_8,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_22,plain,(
    ! [A_23,B_24,C_25] : k2_xboole_0(k2_xboole_0(A_23,B_24),C_25) = k2_xboole_0(A_23,k2_xboole_0(B_24,C_25)) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_37,plain,(
    ! [A_8,B_9,C_25] : k2_xboole_0(k1_tarski(A_8),k2_xboole_0(k1_tarski(B_9),C_25)) = k2_xboole_0(k2_tarski(A_8,B_9),C_25) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_22])).

tff(c_95,plain,(
    ! [A_8,D_39,B_36,E_37,A_38,C_40] : k2_xboole_0(k2_tarski(A_8,A_38),k2_enumset1(B_36,C_40,D_39,E_37)) = k2_xboole_0(k1_tarski(A_8),k3_enumset1(A_38,B_36,C_40,D_39,E_37)) ),
    inference(superposition,[status(thm),theory(equality)],[c_89,c_37])).

tff(c_231,plain,(
    ! [A_8,D_39,B_36,E_37,A_38,C_40] : k2_xboole_0(k2_tarski(A_8,A_38),k2_enumset1(B_36,C_40,D_39,E_37)) = k4_enumset1(A_8,A_38,B_36,C_40,D_39,E_37) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_95])).

tff(c_4,plain,(
    ! [A_4,B_5,C_6,D_7] : k2_xboole_0(k2_tarski(A_4,B_5),k2_tarski(C_6,D_7)) = k2_enumset1(A_4,B_5,C_6,D_7) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_42,plain,(
    ! [A_26,B_27,C_28,D_29] : k2_xboole_0(k2_tarski(A_26,B_27),k2_tarski(C_28,D_29)) = k2_enumset1(A_26,B_27,C_28,D_29) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_2,plain,(
    ! [A_1,B_2,C_3] : k2_xboole_0(k2_xboole_0(A_1,B_2),C_3) = k2_xboole_0(A_1,k2_xboole_0(B_2,C_3)) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_119,plain,(
    ! [C_51,C_50,A_49,D_47,B_48] : k2_xboole_0(k2_tarski(A_49,B_48),k2_xboole_0(k2_tarski(C_51,D_47),C_50)) = k2_xboole_0(k2_enumset1(A_49,B_48,C_51,D_47),C_50) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_2])).

tff(c_140,plain,(
    ! [B_5,D_7,A_4,C_6,A_49,B_48] : k2_xboole_0(k2_enumset1(A_49,B_48,A_4,B_5),k2_tarski(C_6,D_7)) = k2_xboole_0(k2_tarski(A_49,B_48),k2_enumset1(A_4,B_5,C_6,D_7)) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_119])).

tff(c_12,plain,(
    k2_xboole_0(k2_enumset1('#skF_1','#skF_2','#skF_3','#skF_4'),k2_tarski('#skF_5','#skF_6')) != k4_enumset1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_195,plain,(
    k2_xboole_0(k2_tarski('#skF_1','#skF_2'),k2_enumset1('#skF_3','#skF_4','#skF_5','#skF_6')) != k4_enumset1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_140,c_12])).

tff(c_235,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_231,c_195])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:19:24 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.06/1.26  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.06/1.27  
% 2.06/1.27  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.06/1.27  %$ k4_enumset1 > k3_enumset1 > k2_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.06/1.27  
% 2.06/1.27  %Foreground sorts:
% 2.06/1.27  
% 2.06/1.27  
% 2.06/1.27  %Background operators:
% 2.06/1.27  
% 2.06/1.27  
% 2.06/1.27  %Foreground operators:
% 2.06/1.27  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.06/1.27  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.06/1.27  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.06/1.27  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.06/1.27  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.06/1.27  tff('#skF_5', type, '#skF_5': $i).
% 2.06/1.27  tff('#skF_6', type, '#skF_6': $i).
% 2.06/1.27  tff('#skF_2', type, '#skF_2': $i).
% 2.06/1.27  tff('#skF_3', type, '#skF_3': $i).
% 2.06/1.27  tff('#skF_1', type, '#skF_1': $i).
% 2.06/1.27  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.06/1.27  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.06/1.27  tff('#skF_4', type, '#skF_4': $i).
% 2.06/1.27  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.06/1.27  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.06/1.27  
% 2.06/1.28  tff(f_35, axiom, (![A, B, C, D, E, F]: (k4_enumset1(A, B, C, D, E, F) = k2_xboole_0(k1_tarski(A), k3_enumset1(B, C, D, E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_enumset1)).
% 2.06/1.28  tff(f_33, axiom, (![A, B, C, D, E]: (k3_enumset1(A, B, C, D, E) = k2_xboole_0(k1_tarski(A), k2_enumset1(B, C, D, E)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_enumset1)).
% 2.06/1.28  tff(f_31, axiom, (![A, B]: (k2_tarski(A, B) = k2_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_enumset1)).
% 2.06/1.28  tff(f_27, axiom, (![A, B, C]: (k2_xboole_0(k2_xboole_0(A, B), C) = k2_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_1)).
% 2.06/1.28  tff(f_29, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k2_tarski(A, B), k2_tarski(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l53_enumset1)).
% 2.06/1.28  tff(f_38, negated_conjecture, ~(![A, B, C, D, E, F]: (k4_enumset1(A, B, C, D, E, F) = k2_xboole_0(k2_enumset1(A, B, C, D), k2_tarski(E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t54_enumset1)).
% 2.06/1.28  tff(c_10, plain, (![B_16, A_15, D_18, E_19, F_20, C_17]: (k2_xboole_0(k1_tarski(A_15), k3_enumset1(B_16, C_17, D_18, E_19, F_20))=k4_enumset1(A_15, B_16, C_17, D_18, E_19, F_20))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.06/1.28  tff(c_89, plain, (![D_39, B_36, E_37, A_38, C_40]: (k2_xboole_0(k1_tarski(A_38), k2_enumset1(B_36, C_40, D_39, E_37))=k3_enumset1(A_38, B_36, C_40, D_39, E_37))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.06/1.28  tff(c_6, plain, (![A_8, B_9]: (k2_xboole_0(k1_tarski(A_8), k1_tarski(B_9))=k2_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.06/1.28  tff(c_22, plain, (![A_23, B_24, C_25]: (k2_xboole_0(k2_xboole_0(A_23, B_24), C_25)=k2_xboole_0(A_23, k2_xboole_0(B_24, C_25)))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.06/1.28  tff(c_37, plain, (![A_8, B_9, C_25]: (k2_xboole_0(k1_tarski(A_8), k2_xboole_0(k1_tarski(B_9), C_25))=k2_xboole_0(k2_tarski(A_8, B_9), C_25))), inference(superposition, [status(thm), theory('equality')], [c_6, c_22])).
% 2.06/1.28  tff(c_95, plain, (![A_8, D_39, B_36, E_37, A_38, C_40]: (k2_xboole_0(k2_tarski(A_8, A_38), k2_enumset1(B_36, C_40, D_39, E_37))=k2_xboole_0(k1_tarski(A_8), k3_enumset1(A_38, B_36, C_40, D_39, E_37)))), inference(superposition, [status(thm), theory('equality')], [c_89, c_37])).
% 2.06/1.28  tff(c_231, plain, (![A_8, D_39, B_36, E_37, A_38, C_40]: (k2_xboole_0(k2_tarski(A_8, A_38), k2_enumset1(B_36, C_40, D_39, E_37))=k4_enumset1(A_8, A_38, B_36, C_40, D_39, E_37))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_95])).
% 2.06/1.28  tff(c_4, plain, (![A_4, B_5, C_6, D_7]: (k2_xboole_0(k2_tarski(A_4, B_5), k2_tarski(C_6, D_7))=k2_enumset1(A_4, B_5, C_6, D_7))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.06/1.28  tff(c_42, plain, (![A_26, B_27, C_28, D_29]: (k2_xboole_0(k2_tarski(A_26, B_27), k2_tarski(C_28, D_29))=k2_enumset1(A_26, B_27, C_28, D_29))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.06/1.28  tff(c_2, plain, (![A_1, B_2, C_3]: (k2_xboole_0(k2_xboole_0(A_1, B_2), C_3)=k2_xboole_0(A_1, k2_xboole_0(B_2, C_3)))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.06/1.28  tff(c_119, plain, (![C_51, C_50, A_49, D_47, B_48]: (k2_xboole_0(k2_tarski(A_49, B_48), k2_xboole_0(k2_tarski(C_51, D_47), C_50))=k2_xboole_0(k2_enumset1(A_49, B_48, C_51, D_47), C_50))), inference(superposition, [status(thm), theory('equality')], [c_42, c_2])).
% 2.06/1.28  tff(c_140, plain, (![B_5, D_7, A_4, C_6, A_49, B_48]: (k2_xboole_0(k2_enumset1(A_49, B_48, A_4, B_5), k2_tarski(C_6, D_7))=k2_xboole_0(k2_tarski(A_49, B_48), k2_enumset1(A_4, B_5, C_6, D_7)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_119])).
% 2.06/1.28  tff(c_12, plain, (k2_xboole_0(k2_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), k2_tarski('#skF_5', '#skF_6'))!=k4_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.06/1.28  tff(c_195, plain, (k2_xboole_0(k2_tarski('#skF_1', '#skF_2'), k2_enumset1('#skF_3', '#skF_4', '#skF_5', '#skF_6'))!=k4_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_140, c_12])).
% 2.06/1.28  tff(c_235, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_231, c_195])).
% 2.06/1.28  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.06/1.28  
% 2.06/1.28  Inference rules
% 2.06/1.28  ----------------------
% 2.06/1.28  #Ref     : 0
% 2.06/1.28  #Sup     : 56
% 2.06/1.28  #Fact    : 0
% 2.06/1.28  #Define  : 0
% 2.06/1.28  #Split   : 0
% 2.06/1.28  #Chain   : 0
% 2.06/1.28  #Close   : 0
% 2.06/1.28  
% 2.06/1.28  Ordering : KBO
% 2.06/1.28  
% 2.06/1.28  Simplification rules
% 2.06/1.28  ----------------------
% 2.06/1.28  #Subsume      : 0
% 2.06/1.28  #Demod        : 38
% 2.06/1.28  #Tautology    : 35
% 2.06/1.28  #SimpNegUnit  : 0
% 2.06/1.28  #BackRed      : 3
% 2.06/1.28  
% 2.06/1.28  #Partial instantiations: 0
% 2.06/1.28  #Strategies tried      : 1
% 2.06/1.28  
% 2.06/1.28  Timing (in seconds)
% 2.06/1.28  ----------------------
% 2.06/1.29  Preprocessing        : 0.28
% 2.06/1.29  Parsing              : 0.14
% 2.06/1.29  CNF conversion       : 0.02
% 2.06/1.29  Main loop            : 0.23
% 2.06/1.29  Inferencing          : 0.10
% 2.06/1.29  Reduction            : 0.07
% 2.06/1.29  Demodulation         : 0.06
% 2.06/1.29  BG Simplification    : 0.02
% 2.06/1.29  Subsumption          : 0.03
% 2.06/1.29  Abstraction          : 0.02
% 2.06/1.29  MUC search           : 0.00
% 2.06/1.29  Cooper               : 0.00
% 2.06/1.29  Total                : 0.54
% 2.06/1.29  Index Insertion      : 0.00
% 2.06/1.29  Index Deletion       : 0.00
% 2.06/1.29  Index Matching       : 0.00
% 2.06/1.29  BG Taut test         : 0.00
%------------------------------------------------------------------------------

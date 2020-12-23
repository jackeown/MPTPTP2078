%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:45:42 EST 2020

% Result     : Theorem 1.70s
% Output     : CNFRefutation 1.70s
% Verified   : 
% Statistics : Number of formulae       :   28 (  28 expanded)
%              Number of leaves         :   19 (  19 expanded)
%              Depth                    :    5
%              Number of atoms          :   14 (  14 expanded)
%              Number of equality atoms :   13 (  13 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(f_35,axiom,(
    ! [A,B,C,D,E] : k3_enumset1(A,B,C,D,E) = k2_xboole_0(k1_tarski(A),k2_enumset1(B,C,D,E)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_enumset1)).

tff(f_29,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k2_tarski(A,B),k2_tarski(C,D)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l53_enumset1)).

tff(f_33,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k2_xboole_0(k1_tarski(A),k2_tarski(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_enumset1)).

tff(f_27,axiom,(
    ! [A,B,C] : k2_xboole_0(k2_xboole_0(A,B),C) = k2_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).

tff(f_38,negated_conjecture,(
    ~ ! [A,B,C,D,E] : k3_enumset1(A,B,C,D,E) = k2_xboole_0(k1_enumset1(A,B,C),k2_tarski(D,E)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_enumset1)).

tff(c_10,plain,(
    ! [E_17,A_13,B_14,C_15,D_16] : k2_xboole_0(k1_tarski(A_13),k2_enumset1(B_14,C_15,D_16,E_17)) = k3_enumset1(A_13,B_14,C_15,D_16,E_17) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_4,plain,(
    ! [A_4,B_5,C_6,D_7] : k2_xboole_0(k2_tarski(A_4,B_5),k2_tarski(C_6,D_7)) = k2_enumset1(A_4,B_5,C_6,D_7) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_8,plain,(
    ! [A_10,B_11,C_12] : k2_xboole_0(k1_tarski(A_10),k2_tarski(B_11,C_12)) = k1_enumset1(A_10,B_11,C_12) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_31,plain,(
    ! [A_23,B_24,C_25] : k2_xboole_0(k2_xboole_0(A_23,B_24),C_25) = k2_xboole_0(A_23,k2_xboole_0(B_24,C_25)) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_135,plain,(
    ! [A_45,B_46,C_47,C_48] : k2_xboole_0(k1_tarski(A_45),k2_xboole_0(k2_tarski(B_46,C_47),C_48)) = k2_xboole_0(k1_enumset1(A_45,B_46,C_47),C_48) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_31])).

tff(c_153,plain,(
    ! [B_5,D_7,A_4,A_45,C_6] : k2_xboole_0(k1_enumset1(A_45,A_4,B_5),k2_tarski(C_6,D_7)) = k2_xboole_0(k1_tarski(A_45),k2_enumset1(A_4,B_5,C_6,D_7)) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_135])).

tff(c_158,plain,(
    ! [B_5,D_7,A_4,A_45,C_6] : k2_xboole_0(k1_enumset1(A_45,A_4,B_5),k2_tarski(C_6,D_7)) = k3_enumset1(A_45,A_4,B_5,C_6,D_7) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_153])).

tff(c_12,plain,(
    k2_xboole_0(k1_enumset1('#skF_1','#skF_2','#skF_3'),k2_tarski('#skF_4','#skF_5')) != k3_enumset1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_173,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_158,c_12])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:25:10 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.70/1.14  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.70/1.14  
% 1.70/1.14  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.70/1.15  %$ k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 1.70/1.15  
% 1.70/1.15  %Foreground sorts:
% 1.70/1.15  
% 1.70/1.15  
% 1.70/1.15  %Background operators:
% 1.70/1.15  
% 1.70/1.15  
% 1.70/1.15  %Foreground operators:
% 1.70/1.15  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.70/1.15  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.70/1.15  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 1.70/1.15  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.70/1.15  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.70/1.15  tff('#skF_5', type, '#skF_5': $i).
% 1.70/1.15  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.70/1.15  tff('#skF_2', type, '#skF_2': $i).
% 1.70/1.15  tff('#skF_3', type, '#skF_3': $i).
% 1.70/1.15  tff('#skF_1', type, '#skF_1': $i).
% 1.70/1.15  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.70/1.15  tff('#skF_4', type, '#skF_4': $i).
% 1.70/1.15  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.70/1.15  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.70/1.15  
% 1.70/1.15  tff(f_35, axiom, (![A, B, C, D, E]: (k3_enumset1(A, B, C, D, E) = k2_xboole_0(k1_tarski(A), k2_enumset1(B, C, D, E)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_enumset1)).
% 1.70/1.15  tff(f_29, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k2_tarski(A, B), k2_tarski(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l53_enumset1)).
% 1.70/1.15  tff(f_33, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k2_xboole_0(k1_tarski(A), k2_tarski(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t42_enumset1)).
% 1.70/1.15  tff(f_27, axiom, (![A, B, C]: (k2_xboole_0(k2_xboole_0(A, B), C) = k2_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_1)).
% 1.70/1.15  tff(f_38, negated_conjecture, ~(![A, B, C, D, E]: (k3_enumset1(A, B, C, D, E) = k2_xboole_0(k1_enumset1(A, B, C), k2_tarski(D, E)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_enumset1)).
% 1.70/1.15  tff(c_10, plain, (![E_17, A_13, B_14, C_15, D_16]: (k2_xboole_0(k1_tarski(A_13), k2_enumset1(B_14, C_15, D_16, E_17))=k3_enumset1(A_13, B_14, C_15, D_16, E_17))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.70/1.15  tff(c_4, plain, (![A_4, B_5, C_6, D_7]: (k2_xboole_0(k2_tarski(A_4, B_5), k2_tarski(C_6, D_7))=k2_enumset1(A_4, B_5, C_6, D_7))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.70/1.15  tff(c_8, plain, (![A_10, B_11, C_12]: (k2_xboole_0(k1_tarski(A_10), k2_tarski(B_11, C_12))=k1_enumset1(A_10, B_11, C_12))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.70/1.15  tff(c_31, plain, (![A_23, B_24, C_25]: (k2_xboole_0(k2_xboole_0(A_23, B_24), C_25)=k2_xboole_0(A_23, k2_xboole_0(B_24, C_25)))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.70/1.15  tff(c_135, plain, (![A_45, B_46, C_47, C_48]: (k2_xboole_0(k1_tarski(A_45), k2_xboole_0(k2_tarski(B_46, C_47), C_48))=k2_xboole_0(k1_enumset1(A_45, B_46, C_47), C_48))), inference(superposition, [status(thm), theory('equality')], [c_8, c_31])).
% 1.70/1.15  tff(c_153, plain, (![B_5, D_7, A_4, A_45, C_6]: (k2_xboole_0(k1_enumset1(A_45, A_4, B_5), k2_tarski(C_6, D_7))=k2_xboole_0(k1_tarski(A_45), k2_enumset1(A_4, B_5, C_6, D_7)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_135])).
% 1.70/1.15  tff(c_158, plain, (![B_5, D_7, A_4, A_45, C_6]: (k2_xboole_0(k1_enumset1(A_45, A_4, B_5), k2_tarski(C_6, D_7))=k3_enumset1(A_45, A_4, B_5, C_6, D_7))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_153])).
% 1.70/1.15  tff(c_12, plain, (k2_xboole_0(k1_enumset1('#skF_1', '#skF_2', '#skF_3'), k2_tarski('#skF_4', '#skF_5'))!=k3_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.70/1.15  tff(c_173, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_158, c_12])).
% 1.70/1.15  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.70/1.15  
% 1.70/1.15  Inference rules
% 1.70/1.15  ----------------------
% 1.70/1.15  #Ref     : 0
% 1.70/1.15  #Sup     : 40
% 1.70/1.15  #Fact    : 0
% 1.70/1.15  #Define  : 0
% 1.70/1.15  #Split   : 0
% 1.70/1.15  #Chain   : 0
% 1.70/1.15  #Close   : 0
% 1.70/1.15  
% 1.70/1.15  Ordering : KBO
% 1.70/1.15  
% 1.70/1.15  Simplification rules
% 1.70/1.15  ----------------------
% 1.70/1.15  #Subsume      : 0
% 1.70/1.15  #Demod        : 17
% 1.70/1.15  #Tautology    : 24
% 1.70/1.15  #SimpNegUnit  : 0
% 1.70/1.15  #BackRed      : 1
% 1.70/1.15  
% 1.70/1.15  #Partial instantiations: 0
% 1.70/1.15  #Strategies tried      : 1
% 1.70/1.15  
% 1.70/1.16  Timing (in seconds)
% 1.70/1.16  ----------------------
% 1.70/1.16  Preprocessing        : 0.25
% 1.70/1.16  Parsing              : 0.14
% 1.70/1.16  CNF conversion       : 0.01
% 1.70/1.16  Main loop            : 0.15
% 1.70/1.16  Inferencing          : 0.07
% 1.70/1.16  Reduction            : 0.05
% 1.70/1.16  Demodulation         : 0.04
% 1.70/1.16  BG Simplification    : 0.01
% 1.70/1.16  Subsumption          : 0.02
% 1.70/1.16  Abstraction          : 0.01
% 1.70/1.16  MUC search           : 0.00
% 1.70/1.16  Cooper               : 0.00
% 1.70/1.16  Total                : 0.42
% 1.70/1.16  Index Insertion      : 0.00
% 1.70/1.16  Index Deletion       : 0.00
% 1.70/1.16  Index Matching       : 0.00
% 1.70/1.16  BG Taut test         : 0.00
%------------------------------------------------------------------------------

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
% DateTime   : Thu Dec  3 09:46:14 EST 2020

% Result     : Theorem 2.09s
% Output     : CNFRefutation 2.34s
% Verified   : 
% Statistics : Number of formulae       :   29 (  29 expanded)
%              Number of leaves         :   22 (  22 expanded)
%              Depth                    :    4
%              Number of atoms          :   11 (  11 expanded)
%              Number of equality atoms :   10 (  10 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

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

tff(f_31,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k2_tarski(A,B),k2_tarski(C,D)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l53_enumset1)).

tff(f_47,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_33,axiom,(
    ! [A,B,C,D,E] : k3_enumset1(A,B,C,D,E) = k2_xboole_0(k1_enumset1(A,B,C),k2_tarski(D,E)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l57_enumset1)).

tff(f_52,negated_conjecture,(
    ~ ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

tff(c_6,plain,(
    ! [A_6,B_7,C_8,D_9] : k2_xboole_0(k2_tarski(A_6,B_7),k2_tarski(C_8,D_9)) = k2_enumset1(A_6,B_7,C_8,D_9) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_22,plain,(
    ! [A_50,B_51] : k1_enumset1(A_50,A_50,B_51) = k2_tarski(A_50,B_51) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_243,plain,(
    ! [A_87,C_89,D_88,B_85,E_86] : k2_xboole_0(k1_enumset1(A_87,B_85,C_89),k2_tarski(D_88,E_86)) = k3_enumset1(A_87,B_85,C_89,D_88,E_86) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_261,plain,(
    ! [A_50,B_51,D_88,E_86] : k3_enumset1(A_50,A_50,B_51,D_88,E_86) = k2_xboole_0(k2_tarski(A_50,B_51),k2_tarski(D_88,E_86)) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_243])).

tff(c_268,plain,(
    ! [A_50,B_51,D_88,E_86] : k3_enumset1(A_50,A_50,B_51,D_88,E_86) = k2_enumset1(A_50,B_51,D_88,E_86) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_261])).

tff(c_26,plain,(
    k3_enumset1('#skF_1','#skF_1','#skF_2','#skF_3','#skF_4') != k2_enumset1('#skF_1','#skF_2','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_390,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_268,c_26])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:32:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.09/1.31  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.09/1.32  
% 2.09/1.32  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.09/1.32  %$ k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.09/1.32  
% 2.09/1.32  %Foreground sorts:
% 2.09/1.32  
% 2.09/1.32  
% 2.09/1.32  %Background operators:
% 2.09/1.32  
% 2.09/1.32  
% 2.09/1.32  %Foreground operators:
% 2.09/1.32  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.09/1.32  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.09/1.32  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.09/1.32  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.09/1.32  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.09/1.32  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.09/1.32  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.09/1.32  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.09/1.32  tff('#skF_2', type, '#skF_2': $i).
% 2.09/1.32  tff('#skF_3', type, '#skF_3': $i).
% 2.09/1.32  tff('#skF_1', type, '#skF_1': $i).
% 2.09/1.32  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.09/1.32  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.09/1.32  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.09/1.32  tff('#skF_4', type, '#skF_4': $i).
% 2.09/1.32  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.09/1.32  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.09/1.32  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.09/1.32  
% 2.34/1.33  tff(f_31, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k2_tarski(A, B), k2_tarski(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l53_enumset1)).
% 2.34/1.33  tff(f_47, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 2.34/1.33  tff(f_33, axiom, (![A, B, C, D, E]: (k3_enumset1(A, B, C, D, E) = k2_xboole_0(k1_enumset1(A, B, C), k2_tarski(D, E)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l57_enumset1)).
% 2.34/1.33  tff(f_52, negated_conjecture, ~(![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 2.34/1.33  tff(c_6, plain, (![A_6, B_7, C_8, D_9]: (k2_xboole_0(k2_tarski(A_6, B_7), k2_tarski(C_8, D_9))=k2_enumset1(A_6, B_7, C_8, D_9))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.34/1.33  tff(c_22, plain, (![A_50, B_51]: (k1_enumset1(A_50, A_50, B_51)=k2_tarski(A_50, B_51))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.34/1.33  tff(c_243, plain, (![A_87, C_89, D_88, B_85, E_86]: (k2_xboole_0(k1_enumset1(A_87, B_85, C_89), k2_tarski(D_88, E_86))=k3_enumset1(A_87, B_85, C_89, D_88, E_86))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.34/1.33  tff(c_261, plain, (![A_50, B_51, D_88, E_86]: (k3_enumset1(A_50, A_50, B_51, D_88, E_86)=k2_xboole_0(k2_tarski(A_50, B_51), k2_tarski(D_88, E_86)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_243])).
% 2.34/1.33  tff(c_268, plain, (![A_50, B_51, D_88, E_86]: (k3_enumset1(A_50, A_50, B_51, D_88, E_86)=k2_enumset1(A_50, B_51, D_88, E_86))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_261])).
% 2.34/1.33  tff(c_26, plain, (k3_enumset1('#skF_1', '#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k2_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.34/1.33  tff(c_390, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_268, c_26])).
% 2.34/1.33  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.34/1.33  
% 2.34/1.33  Inference rules
% 2.34/1.33  ----------------------
% 2.34/1.33  #Ref     : 0
% 2.34/1.33  #Sup     : 88
% 2.34/1.33  #Fact    : 0
% 2.34/1.33  #Define  : 0
% 2.34/1.33  #Split   : 0
% 2.34/1.33  #Chain   : 0
% 2.34/1.33  #Close   : 0
% 2.34/1.33  
% 2.34/1.33  Ordering : KBO
% 2.34/1.33  
% 2.34/1.33  Simplification rules
% 2.34/1.33  ----------------------
% 2.34/1.33  #Subsume      : 4
% 2.34/1.33  #Demod        : 38
% 2.34/1.33  #Tautology    : 59
% 2.34/1.33  #SimpNegUnit  : 0
% 2.34/1.33  #BackRed      : 1
% 2.34/1.33  
% 2.34/1.33  #Partial instantiations: 0
% 2.34/1.33  #Strategies tried      : 1
% 2.34/1.33  
% 2.34/1.33  Timing (in seconds)
% 2.34/1.33  ----------------------
% 2.34/1.33  Preprocessing        : 0.32
% 2.34/1.33  Parsing              : 0.17
% 2.34/1.33  CNF conversion       : 0.02
% 2.34/1.33  Main loop            : 0.21
% 2.34/1.33  Inferencing          : 0.09
% 2.34/1.33  Reduction            : 0.07
% 2.34/1.33  Demodulation         : 0.06
% 2.34/1.33  BG Simplification    : 0.02
% 2.34/1.33  Subsumption          : 0.02
% 2.34/1.33  Abstraction          : 0.02
% 2.34/1.33  MUC search           : 0.00
% 2.34/1.33  Cooper               : 0.00
% 2.34/1.33  Total                : 0.54
% 2.34/1.33  Index Insertion      : 0.00
% 2.34/1.33  Index Deletion       : 0.00
% 2.34/1.33  Index Matching       : 0.00
% 2.34/1.33  BG Taut test         : 0.00
%------------------------------------------------------------------------------

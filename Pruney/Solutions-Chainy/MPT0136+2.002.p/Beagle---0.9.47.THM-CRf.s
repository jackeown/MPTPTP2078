%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:45:43 EST 2020

% Result     : Theorem 2.05s
% Output     : CNFRefutation 2.05s
% Verified   : 
% Statistics : Number of formulae       :   29 (  29 expanded)
%              Number of leaves         :   20 (  20 expanded)
%              Depth                    :    5
%              Number of atoms          :   14 (  14 expanded)
%              Number of equality atoms :   13 (  13 expanded)
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_enumset1)).

tff(f_33,axiom,(
    ! [A,B,C,D,E] : k3_enumset1(A,B,C,D,E) = k2_xboole_0(k1_tarski(A),k2_enumset1(B,C,D,E)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_enumset1)).

tff(f_31,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_xboole_0(k1_tarski(A),k1_tarski(B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).

tff(f_27,axiom,(
    ! [A,B,C] : k2_xboole_0(k2_xboole_0(A,B),C) = k2_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).

tff(f_38,negated_conjecture,(
    ~ ! [A,B,C,D,E,F] : k4_enumset1(A,B,C,D,E,F) = k2_xboole_0(k2_tarski(A,B),k2_enumset1(C,D,E,F)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_enumset1)).

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

tff(c_211,plain,(
    ! [A_8,D_39,B_36,E_37,A_38,C_40] : k2_xboole_0(k2_tarski(A_8,A_38),k2_enumset1(B_36,C_40,D_39,E_37)) = k4_enumset1(A_8,A_38,B_36,C_40,D_39,E_37) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_95])).

tff(c_12,plain,(
    k2_xboole_0(k2_tarski('#skF_1','#skF_2'),k2_enumset1('#skF_3','#skF_4','#skF_5','#skF_6')) != k4_enumset1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_215,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_211,c_12])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n022.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 18:57:25 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.05/1.19  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.05/1.19  
% 2.05/1.19  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.05/1.19  %$ k4_enumset1 > k3_enumset1 > k2_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.05/1.19  
% 2.05/1.19  %Foreground sorts:
% 2.05/1.19  
% 2.05/1.19  
% 2.05/1.19  %Background operators:
% 2.05/1.19  
% 2.05/1.19  
% 2.05/1.19  %Foreground operators:
% 2.05/1.19  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.05/1.19  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.05/1.19  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.05/1.19  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.05/1.19  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.05/1.19  tff('#skF_5', type, '#skF_5': $i).
% 2.05/1.19  tff('#skF_6', type, '#skF_6': $i).
% 2.05/1.19  tff('#skF_2', type, '#skF_2': $i).
% 2.05/1.19  tff('#skF_3', type, '#skF_3': $i).
% 2.05/1.19  tff('#skF_1', type, '#skF_1': $i).
% 2.05/1.19  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.05/1.19  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.05/1.19  tff('#skF_4', type, '#skF_4': $i).
% 2.05/1.19  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.05/1.19  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.05/1.19  
% 2.05/1.20  tff(f_35, axiom, (![A, B, C, D, E, F]: (k4_enumset1(A, B, C, D, E, F) = k2_xboole_0(k1_tarski(A), k3_enumset1(B, C, D, E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t51_enumset1)).
% 2.05/1.20  tff(f_33, axiom, (![A, B, C, D, E]: (k3_enumset1(A, B, C, D, E) = k2_xboole_0(k1_tarski(A), k2_enumset1(B, C, D, E)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_enumset1)).
% 2.05/1.20  tff(f_31, axiom, (![A, B]: (k2_tarski(A, B) = k2_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_enumset1)).
% 2.05/1.20  tff(f_27, axiom, (![A, B, C]: (k2_xboole_0(k2_xboole_0(A, B), C) = k2_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_1)).
% 2.05/1.20  tff(f_38, negated_conjecture, ~(![A, B, C, D, E, F]: (k4_enumset1(A, B, C, D, E, F) = k2_xboole_0(k2_tarski(A, B), k2_enumset1(C, D, E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_enumset1)).
% 2.05/1.20  tff(c_10, plain, (![B_16, A_15, D_18, E_19, F_20, C_17]: (k2_xboole_0(k1_tarski(A_15), k3_enumset1(B_16, C_17, D_18, E_19, F_20))=k4_enumset1(A_15, B_16, C_17, D_18, E_19, F_20))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.05/1.20  tff(c_89, plain, (![D_39, B_36, E_37, A_38, C_40]: (k2_xboole_0(k1_tarski(A_38), k2_enumset1(B_36, C_40, D_39, E_37))=k3_enumset1(A_38, B_36, C_40, D_39, E_37))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.05/1.20  tff(c_6, plain, (![A_8, B_9]: (k2_xboole_0(k1_tarski(A_8), k1_tarski(B_9))=k2_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.05/1.20  tff(c_22, plain, (![A_23, B_24, C_25]: (k2_xboole_0(k2_xboole_0(A_23, B_24), C_25)=k2_xboole_0(A_23, k2_xboole_0(B_24, C_25)))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.05/1.20  tff(c_37, plain, (![A_8, B_9, C_25]: (k2_xboole_0(k1_tarski(A_8), k2_xboole_0(k1_tarski(B_9), C_25))=k2_xboole_0(k2_tarski(A_8, B_9), C_25))), inference(superposition, [status(thm), theory('equality')], [c_6, c_22])).
% 2.05/1.20  tff(c_95, plain, (![A_8, D_39, B_36, E_37, A_38, C_40]: (k2_xboole_0(k2_tarski(A_8, A_38), k2_enumset1(B_36, C_40, D_39, E_37))=k2_xboole_0(k1_tarski(A_8), k3_enumset1(A_38, B_36, C_40, D_39, E_37)))), inference(superposition, [status(thm), theory('equality')], [c_89, c_37])).
% 2.05/1.20  tff(c_211, plain, (![A_8, D_39, B_36, E_37, A_38, C_40]: (k2_xboole_0(k2_tarski(A_8, A_38), k2_enumset1(B_36, C_40, D_39, E_37))=k4_enumset1(A_8, A_38, B_36, C_40, D_39, E_37))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_95])).
% 2.05/1.20  tff(c_12, plain, (k2_xboole_0(k2_tarski('#skF_1', '#skF_2'), k2_enumset1('#skF_3', '#skF_4', '#skF_5', '#skF_6'))!=k4_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.05/1.20  tff(c_215, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_211, c_12])).
% 2.05/1.20  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.05/1.20  
% 2.05/1.20  Inference rules
% 2.05/1.20  ----------------------
% 2.05/1.20  #Ref     : 0
% 2.05/1.20  #Sup     : 51
% 2.05/1.20  #Fact    : 0
% 2.05/1.20  #Define  : 0
% 2.05/1.20  #Split   : 0
% 2.05/1.20  #Chain   : 0
% 2.05/1.20  #Close   : 0
% 2.05/1.20  
% 2.05/1.20  Ordering : KBO
% 2.05/1.20  
% 2.05/1.20  Simplification rules
% 2.05/1.20  ----------------------
% 2.05/1.20  #Subsume      : 0
% 2.05/1.20  #Demod        : 34
% 2.05/1.20  #Tautology    : 32
% 2.05/1.20  #SimpNegUnit  : 0
% 2.05/1.20  #BackRed      : 2
% 2.05/1.20  
% 2.05/1.20  #Partial instantiations: 0
% 2.05/1.20  #Strategies tried      : 1
% 2.05/1.20  
% 2.05/1.20  Timing (in seconds)
% 2.05/1.20  ----------------------
% 2.05/1.20  Preprocessing        : 0.26
% 2.05/1.20  Parsing              : 0.14
% 2.05/1.20  CNF conversion       : 0.02
% 2.05/1.20  Main loop            : 0.20
% 2.05/1.21  Inferencing          : 0.09
% 2.05/1.21  Reduction            : 0.06
% 2.05/1.21  Demodulation         : 0.06
% 2.05/1.21  BG Simplification    : 0.01
% 2.05/1.21  Subsumption          : 0.02
% 2.05/1.21  Abstraction          : 0.02
% 2.05/1.21  MUC search           : 0.00
% 2.05/1.21  Cooper               : 0.00
% 2.05/1.21  Total                : 0.48
% 2.05/1.21  Index Insertion      : 0.00
% 2.05/1.21  Index Deletion       : 0.00
% 2.05/1.21  Index Matching       : 0.00
% 2.05/1.21  BG Taut test         : 0.00
%------------------------------------------------------------------------------

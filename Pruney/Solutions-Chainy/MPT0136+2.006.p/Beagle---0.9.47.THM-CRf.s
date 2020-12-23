%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:45:44 EST 2020

% Result     : Theorem 2.48s
% Output     : CNFRefutation 2.48s
% Verified   : 
% Statistics : Number of formulae       :   30 (  30 expanded)
%              Number of leaves         :   21 (  21 expanded)
%              Depth                    :    5
%              Number of atoms          :   14 (  14 expanded)
%              Number of equality atoms :   13 (  13 expanded)
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

tff(f_37,axiom,(
    ! [A,B,C,D,E,F] : k4_enumset1(A,B,C,D,E,F) = k2_xboole_0(k1_tarski(A),k3_enumset1(B,C,D,E,F)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_enumset1)).

tff(f_35,axiom,(
    ! [A,B,C,D,E] : k3_enumset1(A,B,C,D,E) = k2_xboole_0(k1_tarski(A),k2_enumset1(B,C,D,E)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_enumset1)).

tff(f_29,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_xboole_0(k1_tarski(A),k1_tarski(B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).

tff(f_27,axiom,(
    ! [A,B,C] : k2_xboole_0(k2_xboole_0(A,B),C) = k2_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).

tff(f_40,negated_conjecture,(
    ~ ! [A,B,C,D,E,F] : k4_enumset1(A,B,C,D,E,F) = k2_xboole_0(k2_tarski(A,B),k2_enumset1(C,D,E,F)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_enumset1)).

tff(c_12,plain,(
    ! [E_22,D_21,F_23,A_18,C_20,B_19] : k2_xboole_0(k1_tarski(A_18),k3_enumset1(B_19,C_20,D_21,E_22,F_23)) = k4_enumset1(A_18,B_19,C_20,D_21,E_22,F_23) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_98,plain,(
    ! [D_39,A_42,C_43,E_41,B_40] : k2_xboole_0(k1_tarski(A_42),k2_enumset1(B_40,C_43,D_39,E_41)) = k3_enumset1(A_42,B_40,C_43,D_39,E_41) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_4,plain,(
    ! [A_4,B_5] : k2_xboole_0(k1_tarski(A_4),k1_tarski(B_5)) = k2_tarski(A_4,B_5) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_24,plain,(
    ! [A_26,B_27,C_28] : k2_xboole_0(k2_xboole_0(A_26,B_27),C_28) = k2_xboole_0(A_26,k2_xboole_0(B_27,C_28)) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_39,plain,(
    ! [A_4,B_5,C_28] : k2_xboole_0(k1_tarski(A_4),k2_xboole_0(k1_tarski(B_5),C_28)) = k2_xboole_0(k2_tarski(A_4,B_5),C_28) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_24])).

tff(c_104,plain,(
    ! [D_39,A_42,C_43,A_4,E_41,B_40] : k2_xboole_0(k2_tarski(A_4,A_42),k2_enumset1(B_40,C_43,D_39,E_41)) = k2_xboole_0(k1_tarski(A_4),k3_enumset1(A_42,B_40,C_43,D_39,E_41)) ),
    inference(superposition,[status(thm),theory(equality)],[c_98,c_39])).

tff(c_466,plain,(
    ! [D_39,A_42,C_43,A_4,E_41,B_40] : k2_xboole_0(k2_tarski(A_4,A_42),k2_enumset1(B_40,C_43,D_39,E_41)) = k4_enumset1(A_4,A_42,B_40,C_43,D_39,E_41) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_104])).

tff(c_14,plain,(
    k2_xboole_0(k2_tarski('#skF_1','#skF_2'),k2_enumset1('#skF_3','#skF_4','#skF_5','#skF_6')) != k4_enumset1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_469,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_466,c_14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:33:00 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.48/1.29  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.48/1.29  
% 2.48/1.29  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.48/1.29  %$ k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.48/1.29  
% 2.48/1.29  %Foreground sorts:
% 2.48/1.29  
% 2.48/1.29  
% 2.48/1.29  %Background operators:
% 2.48/1.29  
% 2.48/1.29  
% 2.48/1.29  %Foreground operators:
% 2.48/1.29  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.48/1.29  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.48/1.29  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.48/1.29  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.48/1.29  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.48/1.29  tff('#skF_5', type, '#skF_5': $i).
% 2.48/1.29  tff('#skF_6', type, '#skF_6': $i).
% 2.48/1.29  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.48/1.29  tff('#skF_2', type, '#skF_2': $i).
% 2.48/1.29  tff('#skF_3', type, '#skF_3': $i).
% 2.48/1.29  tff('#skF_1', type, '#skF_1': $i).
% 2.48/1.29  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.48/1.29  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.48/1.29  tff('#skF_4', type, '#skF_4': $i).
% 2.48/1.29  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.48/1.29  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.48/1.29  
% 2.48/1.30  tff(f_37, axiom, (![A, B, C, D, E, F]: (k4_enumset1(A, B, C, D, E, F) = k2_xboole_0(k1_tarski(A), k3_enumset1(B, C, D, E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_enumset1)).
% 2.48/1.30  tff(f_35, axiom, (![A, B, C, D, E]: (k3_enumset1(A, B, C, D, E) = k2_xboole_0(k1_tarski(A), k2_enumset1(B, C, D, E)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_enumset1)).
% 2.48/1.30  tff(f_29, axiom, (![A, B]: (k2_tarski(A, B) = k2_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_enumset1)).
% 2.48/1.30  tff(f_27, axiom, (![A, B, C]: (k2_xboole_0(k2_xboole_0(A, B), C) = k2_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_1)).
% 2.48/1.30  tff(f_40, negated_conjecture, ~(![A, B, C, D, E, F]: (k4_enumset1(A, B, C, D, E, F) = k2_xboole_0(k2_tarski(A, B), k2_enumset1(C, D, E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_enumset1)).
% 2.48/1.30  tff(c_12, plain, (![E_22, D_21, F_23, A_18, C_20, B_19]: (k2_xboole_0(k1_tarski(A_18), k3_enumset1(B_19, C_20, D_21, E_22, F_23))=k4_enumset1(A_18, B_19, C_20, D_21, E_22, F_23))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.48/1.30  tff(c_98, plain, (![D_39, A_42, C_43, E_41, B_40]: (k2_xboole_0(k1_tarski(A_42), k2_enumset1(B_40, C_43, D_39, E_41))=k3_enumset1(A_42, B_40, C_43, D_39, E_41))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.48/1.30  tff(c_4, plain, (![A_4, B_5]: (k2_xboole_0(k1_tarski(A_4), k1_tarski(B_5))=k2_tarski(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.48/1.30  tff(c_24, plain, (![A_26, B_27, C_28]: (k2_xboole_0(k2_xboole_0(A_26, B_27), C_28)=k2_xboole_0(A_26, k2_xboole_0(B_27, C_28)))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.48/1.30  tff(c_39, plain, (![A_4, B_5, C_28]: (k2_xboole_0(k1_tarski(A_4), k2_xboole_0(k1_tarski(B_5), C_28))=k2_xboole_0(k2_tarski(A_4, B_5), C_28))), inference(superposition, [status(thm), theory('equality')], [c_4, c_24])).
% 2.48/1.30  tff(c_104, plain, (![D_39, A_42, C_43, A_4, E_41, B_40]: (k2_xboole_0(k2_tarski(A_4, A_42), k2_enumset1(B_40, C_43, D_39, E_41))=k2_xboole_0(k1_tarski(A_4), k3_enumset1(A_42, B_40, C_43, D_39, E_41)))), inference(superposition, [status(thm), theory('equality')], [c_98, c_39])).
% 2.48/1.30  tff(c_466, plain, (![D_39, A_42, C_43, A_4, E_41, B_40]: (k2_xboole_0(k2_tarski(A_4, A_42), k2_enumset1(B_40, C_43, D_39, E_41))=k4_enumset1(A_4, A_42, B_40, C_43, D_39, E_41))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_104])).
% 2.48/1.30  tff(c_14, plain, (k2_xboole_0(k2_tarski('#skF_1', '#skF_2'), k2_enumset1('#skF_3', '#skF_4', '#skF_5', '#skF_6'))!=k4_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.48/1.30  tff(c_469, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_466, c_14])).
% 2.48/1.30  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.48/1.30  
% 2.48/1.30  Inference rules
% 2.48/1.30  ----------------------
% 2.48/1.30  #Ref     : 0
% 2.48/1.30  #Sup     : 119
% 2.48/1.30  #Fact    : 0
% 2.48/1.30  #Define  : 0
% 2.48/1.30  #Split   : 0
% 2.48/1.30  #Chain   : 0
% 2.48/1.30  #Close   : 0
% 2.48/1.30  
% 2.48/1.30  Ordering : KBO
% 2.48/1.30  
% 2.48/1.30  Simplification rules
% 2.48/1.30  ----------------------
% 2.48/1.30  #Subsume      : 0
% 2.48/1.30  #Demod        : 53
% 2.48/1.30  #Tautology    : 62
% 2.48/1.30  #SimpNegUnit  : 0
% 2.48/1.30  #BackRed      : 1
% 2.48/1.30  
% 2.48/1.30  #Partial instantiations: 0
% 2.48/1.30  #Strategies tried      : 1
% 2.48/1.30  
% 2.48/1.30  Timing (in seconds)
% 2.48/1.30  ----------------------
% 2.48/1.30  Preprocessing        : 0.28
% 2.48/1.30  Parsing              : 0.16
% 2.48/1.30  CNF conversion       : 0.02
% 2.48/1.30  Main loop            : 0.29
% 2.48/1.30  Inferencing          : 0.14
% 2.48/1.30  Reduction            : 0.09
% 2.48/1.30  Demodulation         : 0.07
% 2.48/1.30  BG Simplification    : 0.02
% 2.48/1.30  Subsumption          : 0.03
% 2.48/1.30  Abstraction          : 0.02
% 2.48/1.30  MUC search           : 0.00
% 2.48/1.30  Cooper               : 0.00
% 2.48/1.30  Total                : 0.59
% 2.48/1.30  Index Insertion      : 0.00
% 2.48/1.31  Index Deletion       : 0.00
% 2.48/1.31  Index Matching       : 0.00
% 2.48/1.31  BG Taut test         : 0.00
%------------------------------------------------------------------------------

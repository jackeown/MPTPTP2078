%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:46:38 EST 2020

% Result     : Theorem 1.57s
% Output     : CNFRefutation 1.67s
% Verified   : 
% Statistics : Number of formulae       :   26 (  26 expanded)
%              Number of leaves         :   17 (  17 expanded)
%              Depth                    :    4
%              Number of atoms          :   14 (  14 expanded)
%              Number of equality atoms :   13 (  13 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k6_enumset1 > k5_enumset1 > k3_enumset1 > k2_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_1

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

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_27,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_xboole_0(k1_tarski(A),k1_tarski(B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).

tff(f_33,axiom,(
    ! [A] : k2_enumset1(A,A,A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t82_enumset1)).

tff(f_29,axiom,(
    ! [A,B,C,D,E] : k3_enumset1(A,B,C,D,E) = k2_xboole_0(k2_enumset1(A,B,C,D),k1_tarski(E)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_enumset1)).

tff(f_35,axiom,(
    ! [A,B,C,D,E] : k6_enumset1(A,A,A,A,B,C,D,E) = k3_enumset1(A,B,C,D,E) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_enumset1)).

tff(f_38,negated_conjecture,(
    ~ ! [A,B] : k6_enumset1(A,A,A,A,A,A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_enumset1)).

tff(c_2,plain,(
    ! [A_1,B_2] : k2_xboole_0(k1_tarski(A_1),k1_tarski(B_2)) = k2_tarski(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_8,plain,(
    ! [A_16] : k2_enumset1(A_16,A_16,A_16,A_16) = k1_tarski(A_16) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_32,plain,(
    ! [E_25,B_29,A_27,D_26,C_28] : k2_xboole_0(k2_enumset1(A_27,B_29,C_28,D_26),k1_tarski(E_25)) = k3_enumset1(A_27,B_29,C_28,D_26,E_25) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_41,plain,(
    ! [A_16,E_25] : k3_enumset1(A_16,A_16,A_16,A_16,E_25) = k2_xboole_0(k1_tarski(A_16),k1_tarski(E_25)) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_32])).

tff(c_44,plain,(
    ! [A_16,E_25] : k3_enumset1(A_16,A_16,A_16,A_16,E_25) = k2_tarski(A_16,E_25) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_41])).

tff(c_10,plain,(
    ! [E_21,D_20,C_19,B_18,A_17] : k6_enumset1(A_17,A_17,A_17,A_17,B_18,C_19,D_20,E_21) = k3_enumset1(A_17,B_18,C_19,D_20,E_21) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_12,plain,(
    k6_enumset1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_1','#skF_1','#skF_1','#skF_2') != k2_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_13,plain,(
    k3_enumset1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2') != k2_tarski('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_12])).

tff(c_47,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_13])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n016.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 12:09:19 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.57/1.08  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.67/1.09  
% 1.67/1.09  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.67/1.09  %$ k6_enumset1 > k5_enumset1 > k3_enumset1 > k2_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_1
% 1.67/1.09  
% 1.67/1.09  %Foreground sorts:
% 1.67/1.09  
% 1.67/1.09  
% 1.67/1.09  %Background operators:
% 1.67/1.09  
% 1.67/1.09  
% 1.67/1.09  %Foreground operators:
% 1.67/1.09  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.67/1.09  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.67/1.09  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 1.67/1.09  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.67/1.09  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.67/1.09  tff('#skF_2', type, '#skF_2': $i).
% 1.67/1.09  tff('#skF_1', type, '#skF_1': $i).
% 1.67/1.09  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 1.67/1.09  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.67/1.09  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.67/1.09  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.67/1.09  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 1.67/1.09  
% 1.67/1.10  tff(f_27, axiom, (![A, B]: (k2_tarski(A, B) = k2_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_enumset1)).
% 1.67/1.10  tff(f_33, axiom, (![A]: (k2_enumset1(A, A, A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t82_enumset1)).
% 1.67/1.10  tff(f_29, axiom, (![A, B, C, D, E]: (k3_enumset1(A, B, C, D, E) = k2_xboole_0(k2_enumset1(A, B, C, D), k1_tarski(E)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_enumset1)).
% 1.67/1.10  tff(f_35, axiom, (![A, B, C, D, E]: (k6_enumset1(A, A, A, A, B, C, D, E) = k3_enumset1(A, B, C, D, E))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t86_enumset1)).
% 1.67/1.10  tff(f_38, negated_conjecture, ~(![A, B]: (k6_enumset1(A, A, A, A, A, A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t95_enumset1)).
% 1.67/1.10  tff(c_2, plain, (![A_1, B_2]: (k2_xboole_0(k1_tarski(A_1), k1_tarski(B_2))=k2_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.67/1.10  tff(c_8, plain, (![A_16]: (k2_enumset1(A_16, A_16, A_16, A_16)=k1_tarski(A_16))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.67/1.10  tff(c_32, plain, (![E_25, B_29, A_27, D_26, C_28]: (k2_xboole_0(k2_enumset1(A_27, B_29, C_28, D_26), k1_tarski(E_25))=k3_enumset1(A_27, B_29, C_28, D_26, E_25))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.67/1.10  tff(c_41, plain, (![A_16, E_25]: (k3_enumset1(A_16, A_16, A_16, A_16, E_25)=k2_xboole_0(k1_tarski(A_16), k1_tarski(E_25)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_32])).
% 1.67/1.10  tff(c_44, plain, (![A_16, E_25]: (k3_enumset1(A_16, A_16, A_16, A_16, E_25)=k2_tarski(A_16, E_25))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_41])).
% 1.67/1.10  tff(c_10, plain, (![E_21, D_20, C_19, B_18, A_17]: (k6_enumset1(A_17, A_17, A_17, A_17, B_18, C_19, D_20, E_21)=k3_enumset1(A_17, B_18, C_19, D_20, E_21))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.67/1.10  tff(c_12, plain, (k6_enumset1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2')!=k2_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.67/1.10  tff(c_13, plain, (k3_enumset1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2')!=k2_tarski('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_10, c_12])).
% 1.67/1.10  tff(c_47, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_44, c_13])).
% 1.67/1.10  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.67/1.10  
% 1.67/1.10  Inference rules
% 1.67/1.10  ----------------------
% 1.67/1.10  #Ref     : 0
% 1.67/1.10  #Sup     : 7
% 1.67/1.10  #Fact    : 0
% 1.67/1.10  #Define  : 0
% 1.67/1.10  #Split   : 0
% 1.67/1.10  #Chain   : 0
% 1.67/1.10  #Close   : 0
% 1.67/1.10  
% 1.67/1.10  Ordering : KBO
% 1.67/1.10  
% 1.67/1.10  Simplification rules
% 1.67/1.10  ----------------------
% 1.67/1.10  #Subsume      : 0
% 1.67/1.10  #Demod        : 3
% 1.67/1.10  #Tautology    : 6
% 1.67/1.10  #SimpNegUnit  : 0
% 1.67/1.10  #BackRed      : 1
% 1.67/1.10  
% 1.67/1.10  #Partial instantiations: 0
% 1.67/1.10  #Strategies tried      : 1
% 1.67/1.10  
% 1.67/1.10  Timing (in seconds)
% 1.67/1.10  ----------------------
% 1.67/1.10  Preprocessing        : 0.28
% 1.67/1.10  Parsing              : 0.15
% 1.67/1.10  CNF conversion       : 0.02
% 1.67/1.10  Main loop            : 0.07
% 1.67/1.10  Inferencing          : 0.03
% 1.67/1.10  Reduction            : 0.02
% 1.67/1.10  Demodulation         : 0.02
% 1.67/1.10  BG Simplification    : 0.01
% 1.67/1.10  Subsumption          : 0.01
% 1.67/1.10  Abstraction          : 0.01
% 1.67/1.10  MUC search           : 0.00
% 1.67/1.10  Cooper               : 0.00
% 1.67/1.10  Total                : 0.36
% 1.67/1.10  Index Insertion      : 0.00
% 1.67/1.10  Index Deletion       : 0.00
% 1.67/1.10  Index Matching       : 0.00
% 1.67/1.10  BG Taut test         : 0.00
%------------------------------------------------------------------------------

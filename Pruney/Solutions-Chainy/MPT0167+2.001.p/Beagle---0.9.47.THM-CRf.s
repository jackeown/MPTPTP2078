%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:46:26 EST 2020

% Result     : Theorem 1.61s
% Output     : CNFRefutation 1.61s
% Verified   : 
% Statistics : Number of formulae       :   21 (  21 expanded)
%              Number of leaves         :   14 (  14 expanded)
%              Depth                    :    4
%              Number of atoms          :   11 (  11 expanded)
%              Number of equality atoms :   10 (  10 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k3_enumset1 > k2_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_1

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

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_27,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_xboole_0(k1_tarski(A),k1_tarski(B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).

tff(f_31,axiom,(
    ! [A] : k2_enumset1(A,A,A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t82_enumset1)).

tff(f_29,axiom,(
    ! [A,B,C,D,E] : k3_enumset1(A,B,C,D,E) = k2_xboole_0(k2_enumset1(A,B,C,D),k1_tarski(E)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_enumset1)).

tff(f_34,negated_conjecture,(
    ~ ! [A,B] : k3_enumset1(A,A,A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_enumset1)).

tff(c_2,plain,(
    ! [A_1,B_2] : k2_xboole_0(k1_tarski(A_1),k1_tarski(B_2)) = k2_tarski(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_6,plain,(
    ! [A_8] : k2_enumset1(A_8,A_8,A_8,A_8) = k1_tarski(A_8) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_27,plain,(
    ! [E_12,B_16,C_15,D_13,A_14] : k2_xboole_0(k2_enumset1(A_14,B_16,C_15,D_13),k1_tarski(E_12)) = k3_enumset1(A_14,B_16,C_15,D_13,E_12) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_36,plain,(
    ! [A_8,E_12] : k3_enumset1(A_8,A_8,A_8,A_8,E_12) = k2_xboole_0(k1_tarski(A_8),k1_tarski(E_12)) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_27])).

tff(c_39,plain,(
    ! [A_8,E_12] : k3_enumset1(A_8,A_8,A_8,A_8,E_12) = k2_tarski(A_8,E_12) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_36])).

tff(c_8,plain,(
    k3_enumset1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2') != k2_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_42,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_39,c_8])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n004.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 12:47:08 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.61/1.16  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.61/1.16  
% 1.61/1.16  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.61/1.16  %$ k3_enumset1 > k2_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_1
% 1.61/1.16  
% 1.61/1.16  %Foreground sorts:
% 1.61/1.16  
% 1.61/1.16  
% 1.61/1.16  %Background operators:
% 1.61/1.16  
% 1.61/1.16  
% 1.61/1.16  %Foreground operators:
% 1.61/1.16  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.61/1.16  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.61/1.16  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 1.61/1.16  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.61/1.16  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.61/1.16  tff('#skF_2', type, '#skF_2': $i).
% 1.61/1.16  tff('#skF_1', type, '#skF_1': $i).
% 1.61/1.16  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.61/1.16  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.61/1.16  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.61/1.16  
% 1.61/1.17  tff(f_27, axiom, (![A, B]: (k2_tarski(A, B) = k2_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_enumset1)).
% 1.61/1.17  tff(f_31, axiom, (![A]: (k2_enumset1(A, A, A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t82_enumset1)).
% 1.61/1.17  tff(f_29, axiom, (![A, B, C, D, E]: (k3_enumset1(A, B, C, D, E) = k2_xboole_0(k2_enumset1(A, B, C, D), k1_tarski(E)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_enumset1)).
% 1.61/1.17  tff(f_34, negated_conjecture, ~(![A, B]: (k3_enumset1(A, A, A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_enumset1)).
% 1.61/1.17  tff(c_2, plain, (![A_1, B_2]: (k2_xboole_0(k1_tarski(A_1), k1_tarski(B_2))=k2_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.61/1.17  tff(c_6, plain, (![A_8]: (k2_enumset1(A_8, A_8, A_8, A_8)=k1_tarski(A_8))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.61/1.17  tff(c_27, plain, (![E_12, B_16, C_15, D_13, A_14]: (k2_xboole_0(k2_enumset1(A_14, B_16, C_15, D_13), k1_tarski(E_12))=k3_enumset1(A_14, B_16, C_15, D_13, E_12))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.61/1.17  tff(c_36, plain, (![A_8, E_12]: (k3_enumset1(A_8, A_8, A_8, A_8, E_12)=k2_xboole_0(k1_tarski(A_8), k1_tarski(E_12)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_27])).
% 1.61/1.17  tff(c_39, plain, (![A_8, E_12]: (k3_enumset1(A_8, A_8, A_8, A_8, E_12)=k2_tarski(A_8, E_12))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_36])).
% 1.61/1.17  tff(c_8, plain, (k3_enumset1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2')!=k2_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.61/1.17  tff(c_42, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_39, c_8])).
% 1.61/1.17  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.61/1.17  
% 1.61/1.17  Inference rules
% 1.61/1.17  ----------------------
% 1.61/1.17  #Ref     : 0
% 1.61/1.17  #Sup     : 7
% 1.61/1.17  #Fact    : 0
% 1.61/1.17  #Define  : 0
% 1.61/1.17  #Split   : 0
% 1.61/1.17  #Chain   : 0
% 1.61/1.17  #Close   : 0
% 1.61/1.17  
% 1.61/1.17  Ordering : KBO
% 1.61/1.17  
% 1.61/1.17  Simplification rules
% 1.61/1.17  ----------------------
% 1.61/1.17  #Subsume      : 0
% 1.61/1.17  #Demod        : 2
% 1.61/1.17  #Tautology    : 6
% 1.61/1.17  #SimpNegUnit  : 0
% 1.61/1.17  #BackRed      : 1
% 1.61/1.17  
% 1.61/1.17  #Partial instantiations: 0
% 1.61/1.17  #Strategies tried      : 1
% 1.61/1.17  
% 1.61/1.17  Timing (in seconds)
% 1.61/1.17  ----------------------
% 1.61/1.17  Preprocessing        : 0.28
% 1.61/1.17  Parsing              : 0.14
% 1.61/1.17  CNF conversion       : 0.02
% 1.61/1.17  Main loop            : 0.07
% 1.61/1.17  Inferencing          : 0.03
% 1.61/1.17  Reduction            : 0.02
% 1.61/1.17  Demodulation         : 0.02
% 1.61/1.17  BG Simplification    : 0.01
% 1.61/1.17  Subsumption          : 0.01
% 1.61/1.17  Abstraction          : 0.01
% 1.61/1.17  MUC search           : 0.00
% 1.61/1.17  Cooper               : 0.00
% 1.61/1.17  Total                : 0.37
% 1.61/1.17  Index Insertion      : 0.00
% 1.61/1.17  Index Deletion       : 0.00
% 1.61/1.18  Index Matching       : 0.00
% 1.61/1.18  BG Taut test         : 0.00
%------------------------------------------------------------------------------

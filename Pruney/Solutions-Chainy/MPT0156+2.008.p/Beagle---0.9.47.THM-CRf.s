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
% DateTime   : Thu Dec  3 09:46:15 EST 2020

% Result     : Theorem 1.98s
% Output     : CNFRefutation 1.98s
% Verified   : 
% Statistics : Number of formulae       :   23 (  23 expanded)
%              Number of leaves         :   16 (  16 expanded)
%              Depth                    :    4
%              Number of atoms          :   11 (  11 expanded)
%              Number of equality atoms :   10 (  10 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

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

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_27,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k2_tarski(A,B),k2_tarski(C,D)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l53_enumset1)).

tff(f_31,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_29,axiom,(
    ! [A,B,C,D,E] : k3_enumset1(A,B,C,D,E) = k2_xboole_0(k1_enumset1(A,B,C),k2_tarski(D,E)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_enumset1)).

tff(f_36,negated_conjecture,(
    ~ ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

tff(c_2,plain,(
    ! [A_1,B_2,C_3,D_4] : k2_xboole_0(k2_tarski(A_1,B_2),k2_tarski(C_3,D_4)) = k2_enumset1(A_1,B_2,C_3,D_4) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_6,plain,(
    ! [A_10,B_11] : k1_enumset1(A_10,A_10,B_11) = k2_tarski(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_38,plain,(
    ! [D_24,B_25,C_26,A_27,E_28] : k2_xboole_0(k1_enumset1(A_27,B_25,C_26),k2_tarski(D_24,E_28)) = k3_enumset1(A_27,B_25,C_26,D_24,E_28) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_47,plain,(
    ! [A_10,B_11,D_24,E_28] : k3_enumset1(A_10,A_10,B_11,D_24,E_28) = k2_xboole_0(k2_tarski(A_10,B_11),k2_tarski(D_24,E_28)) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_38])).

tff(c_50,plain,(
    ! [A_10,B_11,D_24,E_28] : k3_enumset1(A_10,A_10,B_11,D_24,E_28) = k2_enumset1(A_10,B_11,D_24,E_28) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_47])).

tff(c_10,plain,(
    k3_enumset1('#skF_1','#skF_1','#skF_2','#skF_3','#skF_4') != k2_enumset1('#skF_1','#skF_2','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_53,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_10])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n013.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:31:39 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.98/1.42  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.98/1.43  
% 1.98/1.43  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.98/1.43  %$ k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 1.98/1.43  
% 1.98/1.43  %Foreground sorts:
% 1.98/1.43  
% 1.98/1.43  
% 1.98/1.43  %Background operators:
% 1.98/1.43  
% 1.98/1.43  
% 1.98/1.43  %Foreground operators:
% 1.98/1.43  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.98/1.43  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 1.98/1.43  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.98/1.43  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.98/1.43  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.98/1.43  tff('#skF_2', type, '#skF_2': $i).
% 1.98/1.43  tff('#skF_3', type, '#skF_3': $i).
% 1.98/1.43  tff('#skF_1', type, '#skF_1': $i).
% 1.98/1.43  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.98/1.43  tff('#skF_4', type, '#skF_4': $i).
% 1.98/1.43  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.98/1.43  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.98/1.43  
% 1.98/1.44  tff(f_27, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k2_tarski(A, B), k2_tarski(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l53_enumset1)).
% 1.98/1.44  tff(f_31, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 1.98/1.44  tff(f_29, axiom, (![A, B, C, D, E]: (k3_enumset1(A, B, C, D, E) = k2_xboole_0(k1_enumset1(A, B, C), k2_tarski(D, E)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_enumset1)).
% 1.98/1.44  tff(f_36, negated_conjecture, ~(![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 1.98/1.44  tff(c_2, plain, (![A_1, B_2, C_3, D_4]: (k2_xboole_0(k2_tarski(A_1, B_2), k2_tarski(C_3, D_4))=k2_enumset1(A_1, B_2, C_3, D_4))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.98/1.44  tff(c_6, plain, (![A_10, B_11]: (k1_enumset1(A_10, A_10, B_11)=k2_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.98/1.44  tff(c_38, plain, (![D_24, B_25, C_26, A_27, E_28]: (k2_xboole_0(k1_enumset1(A_27, B_25, C_26), k2_tarski(D_24, E_28))=k3_enumset1(A_27, B_25, C_26, D_24, E_28))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.98/1.44  tff(c_47, plain, (![A_10, B_11, D_24, E_28]: (k3_enumset1(A_10, A_10, B_11, D_24, E_28)=k2_xboole_0(k2_tarski(A_10, B_11), k2_tarski(D_24, E_28)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_38])).
% 1.98/1.44  tff(c_50, plain, (![A_10, B_11, D_24, E_28]: (k3_enumset1(A_10, A_10, B_11, D_24, E_28)=k2_enumset1(A_10, B_11, D_24, E_28))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_47])).
% 1.98/1.44  tff(c_10, plain, (k3_enumset1('#skF_1', '#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k2_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.98/1.44  tff(c_53, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_50, c_10])).
% 1.98/1.44  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.98/1.44  
% 1.98/1.44  Inference rules
% 1.98/1.44  ----------------------
% 1.98/1.44  #Ref     : 0
% 1.98/1.44  #Sup     : 9
% 1.98/1.44  #Fact    : 0
% 1.98/1.44  #Define  : 0
% 1.98/1.44  #Split   : 0
% 1.98/1.44  #Chain   : 0
% 1.98/1.44  #Close   : 0
% 1.98/1.44  
% 1.98/1.44  Ordering : KBO
% 1.98/1.44  
% 1.98/1.44  Simplification rules
% 1.98/1.44  ----------------------
% 1.98/1.44  #Subsume      : 0
% 1.98/1.44  #Demod        : 2
% 1.98/1.44  #Tautology    : 8
% 1.98/1.44  #SimpNegUnit  : 0
% 1.98/1.44  #BackRed      : 1
% 1.98/1.44  
% 1.98/1.44  #Partial instantiations: 0
% 1.98/1.44  #Strategies tried      : 1
% 1.98/1.44  
% 1.98/1.44  Timing (in seconds)
% 1.98/1.44  ----------------------
% 1.98/1.45  Preprocessing        : 0.41
% 1.98/1.45  Parsing              : 0.21
% 1.98/1.45  CNF conversion       : 0.03
% 1.98/1.45  Main loop            : 0.13
% 1.98/1.45  Inferencing          : 0.06
% 1.98/1.45  Reduction            : 0.04
% 1.98/1.45  Demodulation         : 0.03
% 1.98/1.45  BG Simplification    : 0.01
% 1.98/1.45  Subsumption          : 0.01
% 1.98/1.45  Abstraction          : 0.01
% 1.98/1.45  MUC search           : 0.00
% 1.98/1.45  Cooper               : 0.00
% 1.98/1.45  Total                : 0.58
% 1.98/1.45  Index Insertion      : 0.00
% 1.98/1.45  Index Deletion       : 0.00
% 1.98/1.45  Index Matching       : 0.00
% 1.98/1.45  BG Taut test         : 0.00
%------------------------------------------------------------------------------

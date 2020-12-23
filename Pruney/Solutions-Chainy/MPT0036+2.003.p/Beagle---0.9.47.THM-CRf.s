%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:42:40 EST 2020

% Result     : Theorem 1.76s
% Output     : CNFRefutation 1.97s
% Verified   : 
% Statistics : Number of formulae       :   25 (  26 expanded)
%              Number of leaves         :   14 (  15 expanded)
%              Depth                    :    6
%              Number of atoms          :   16 (  17 expanded)
%              Number of equality atoms :    7 (   8 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k3_xboole_0 > k2_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_33,axiom,(
    ! [A,B] : k3_xboole_0(A,k2_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_xboole_1)).

tff(f_29,axiom,(
    ! [A,B,C] : k3_xboole_0(k3_xboole_0(A,B),C) = k3_xboole_0(A,k3_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_36,negated_conjecture,(
    ~ ! [A,B,C] : r1_tarski(k3_xboole_0(A,B),k2_xboole_0(A,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_xboole_1)).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_8,plain,(
    ! [A_8,B_9] : k3_xboole_0(A_8,k2_xboole_0(A_8,B_9)) = A_8 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_78,plain,(
    ! [A_21,B_22,C_23] : k3_xboole_0(k3_xboole_0(A_21,B_22),C_23) = k3_xboole_0(A_21,k3_xboole_0(B_22,C_23)) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_12,plain,(
    ! [B_12,A_13] : k3_xboole_0(B_12,A_13) = k3_xboole_0(A_13,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_6,plain,(
    ! [A_6,B_7] : r1_tarski(k3_xboole_0(A_6,B_7),A_6) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_27,plain,(
    ! [B_12,A_13] : r1_tarski(k3_xboole_0(B_12,A_13),A_13) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_6])).

tff(c_132,plain,(
    ! [A_24,B_25,C_26] : r1_tarski(k3_xboole_0(A_24,k3_xboole_0(B_25,C_26)),C_26) ),
    inference(superposition,[status(thm),theory(equality)],[c_78,c_27])).

tff(c_159,plain,(
    ! [A_27,A_28,B_29] : r1_tarski(k3_xboole_0(A_27,A_28),k2_xboole_0(A_28,B_29)) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_132])).

tff(c_171,plain,(
    ! [A_1,B_2,B_29] : r1_tarski(k3_xboole_0(A_1,B_2),k2_xboole_0(A_1,B_29)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_159])).

tff(c_10,plain,(
    ~ r1_tarski(k3_xboole_0('#skF_1','#skF_2'),k2_xboole_0('#skF_1','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_251,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_171,c_10])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n005.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 09:43:32 EST 2020
% 0.19/0.33  % CPUTime    : 
% 0.19/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.76/1.19  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.97/1.20  
% 1.97/1.20  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.97/1.20  %$ r1_tarski > k3_xboole_0 > k2_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1
% 1.97/1.20  
% 1.97/1.20  %Foreground sorts:
% 1.97/1.20  
% 1.97/1.20  
% 1.97/1.20  %Background operators:
% 1.97/1.20  
% 1.97/1.20  
% 1.97/1.20  %Foreground operators:
% 1.97/1.20  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.97/1.20  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.97/1.20  tff('#skF_2', type, '#skF_2': $i).
% 1.97/1.20  tff('#skF_3', type, '#skF_3': $i).
% 1.97/1.20  tff('#skF_1', type, '#skF_1': $i).
% 1.97/1.20  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.97/1.20  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.97/1.20  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.97/1.20  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.97/1.20  
% 1.97/1.21  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 1.97/1.21  tff(f_33, axiom, (![A, B]: (k3_xboole_0(A, k2_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_xboole_1)).
% 1.97/1.21  tff(f_29, axiom, (![A, B, C]: (k3_xboole_0(k3_xboole_0(A, B), C) = k3_xboole_0(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t16_xboole_1)).
% 1.97/1.21  tff(f_31, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 1.97/1.21  tff(f_36, negated_conjecture, ~(![A, B, C]: r1_tarski(k3_xboole_0(A, B), k2_xboole_0(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_xboole_1)).
% 1.97/1.21  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.97/1.21  tff(c_8, plain, (![A_8, B_9]: (k3_xboole_0(A_8, k2_xboole_0(A_8, B_9))=A_8)), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.97/1.21  tff(c_78, plain, (![A_21, B_22, C_23]: (k3_xboole_0(k3_xboole_0(A_21, B_22), C_23)=k3_xboole_0(A_21, k3_xboole_0(B_22, C_23)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.97/1.21  tff(c_12, plain, (![B_12, A_13]: (k3_xboole_0(B_12, A_13)=k3_xboole_0(A_13, B_12))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.97/1.21  tff(c_6, plain, (![A_6, B_7]: (r1_tarski(k3_xboole_0(A_6, B_7), A_6))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.97/1.21  tff(c_27, plain, (![B_12, A_13]: (r1_tarski(k3_xboole_0(B_12, A_13), A_13))), inference(superposition, [status(thm), theory('equality')], [c_12, c_6])).
% 1.97/1.21  tff(c_132, plain, (![A_24, B_25, C_26]: (r1_tarski(k3_xboole_0(A_24, k3_xboole_0(B_25, C_26)), C_26))), inference(superposition, [status(thm), theory('equality')], [c_78, c_27])).
% 1.97/1.21  tff(c_159, plain, (![A_27, A_28, B_29]: (r1_tarski(k3_xboole_0(A_27, A_28), k2_xboole_0(A_28, B_29)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_132])).
% 1.97/1.21  tff(c_171, plain, (![A_1, B_2, B_29]: (r1_tarski(k3_xboole_0(A_1, B_2), k2_xboole_0(A_1, B_29)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_159])).
% 1.97/1.21  tff(c_10, plain, (~r1_tarski(k3_xboole_0('#skF_1', '#skF_2'), k2_xboole_0('#skF_1', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.97/1.21  tff(c_251, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_171, c_10])).
% 1.97/1.21  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.97/1.21  
% 1.97/1.21  Inference rules
% 1.97/1.21  ----------------------
% 1.97/1.21  #Ref     : 0
% 1.97/1.21  #Sup     : 60
% 1.97/1.21  #Fact    : 0
% 1.97/1.21  #Define  : 0
% 1.97/1.21  #Split   : 0
% 1.97/1.21  #Chain   : 0
% 1.97/1.21  #Close   : 0
% 1.97/1.21  
% 1.97/1.21  Ordering : KBO
% 1.97/1.21  
% 1.97/1.21  Simplification rules
% 1.97/1.21  ----------------------
% 1.97/1.21  #Subsume      : 0
% 1.97/1.21  #Demod        : 28
% 1.97/1.21  #Tautology    : 27
% 1.97/1.21  #SimpNegUnit  : 0
% 1.97/1.21  #BackRed      : 1
% 1.97/1.21  
% 1.97/1.21  #Partial instantiations: 0
% 1.97/1.21  #Strategies tried      : 1
% 1.97/1.21  
% 1.97/1.21  Timing (in seconds)
% 1.97/1.21  ----------------------
% 1.97/1.21  Preprocessing        : 0.24
% 1.97/1.21  Parsing              : 0.13
% 1.97/1.21  CNF conversion       : 0.01
% 1.97/1.21  Main loop            : 0.18
% 1.97/1.21  Inferencing          : 0.06
% 1.97/1.21  Reduction            : 0.08
% 1.97/1.21  Demodulation         : 0.07
% 1.97/1.21  BG Simplification    : 0.01
% 1.97/1.21  Subsumption          : 0.03
% 1.97/1.21  Abstraction          : 0.01
% 1.97/1.21  MUC search           : 0.00
% 1.97/1.21  Cooper               : 0.00
% 1.97/1.21  Total                : 0.45
% 1.97/1.21  Index Insertion      : 0.00
% 1.97/1.21  Index Deletion       : 0.00
% 1.97/1.21  Index Matching       : 0.00
% 1.97/1.21  BG Taut test         : 0.00
%------------------------------------------------------------------------------

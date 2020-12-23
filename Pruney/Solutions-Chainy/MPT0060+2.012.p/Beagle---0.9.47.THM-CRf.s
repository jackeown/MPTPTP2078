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
% DateTime   : Thu Dec  3 09:43:07 EST 2020

% Result     : Theorem 10.92s
% Output     : CNFRefutation 10.92s
% Verified   : 
% Statistics : Number of formulae       :   33 (  36 expanded)
%              Number of leaves         :   18 (  20 expanded)
%              Depth                    :    6
%              Number of atoms          :   24 (  27 expanded)
%              Number of equality atoms :   19 (  22 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

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

tff(f_35,axiom,(
    ! [A,B,C] : k4_xboole_0(k4_xboole_0(A,B),C) = k4_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

tff(f_33,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_27,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_xboole_1)).

tff(f_39,axiom,(
    ! [A,B,C] : k3_xboole_0(A,k4_xboole_0(B,C)) = k4_xboole_0(k3_xboole_0(A,B),C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_42,negated_conjecture,(
    ~ ! [A,B,C] : k4_xboole_0(A,k2_xboole_0(B,C)) = k3_xboole_0(k4_xboole_0(A,B),k4_xboole_0(A,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t53_xboole_1)).

tff(c_10,plain,(
    ! [A_6,B_7,C_8] : k4_xboole_0(k4_xboole_0(A_6,B_7),C_8) = k4_xboole_0(A_6,k2_xboole_0(B_7,C_8)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_8,plain,(
    ! [A_5] : k4_xboole_0(A_5,k1_xboole_0) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_360,plain,(
    ! [A_39,B_40,C_41] : k4_xboole_0(k4_xboole_0(A_39,B_40),C_41) = k4_xboole_0(A_39,k2_xboole_0(B_40,C_41)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_429,plain,(
    ! [A_5,C_41] : k4_xboole_0(A_5,k2_xboole_0(k1_xboole_0,C_41)) = k4_xboole_0(A_5,C_41) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_360])).

tff(c_2,plain,(
    ! [A_1,B_2] : r1_tarski(k4_xboole_0(A_1,B_2),A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_31,plain,(
    ! [A_18,B_19] :
      ( k4_xboole_0(A_18,B_19) = k1_xboole_0
      | ~ r1_tarski(A_18,B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_39,plain,(
    ! [A_1,B_2] : k4_xboole_0(k4_xboole_0(A_1,B_2),A_1) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2,c_31])).

tff(c_14,plain,(
    ! [A_11,B_12,C_13] : k4_xboole_0(k3_xboole_0(A_11,B_12),C_13) = k3_xboole_0(A_11,k4_xboole_0(B_12,C_13)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_12,plain,(
    ! [A_9,B_10] : k4_xboole_0(A_9,k4_xboole_0(A_9,B_10)) = k3_xboole_0(A_9,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_406,plain,(
    ! [A_9,B_10,C_41] : k4_xboole_0(A_9,k2_xboole_0(k4_xboole_0(A_9,B_10),C_41)) = k4_xboole_0(k3_xboole_0(A_9,B_10),C_41) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_360])).

tff(c_5309,plain,(
    ! [A_123,B_124,C_125] : k4_xboole_0(A_123,k2_xboole_0(k4_xboole_0(A_123,B_124),C_125)) = k3_xboole_0(A_123,k4_xboole_0(B_124,C_125)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_406])).

tff(c_5524,plain,(
    ! [A_1,B_2,C_125] : k4_xboole_0(k4_xboole_0(A_1,B_2),k2_xboole_0(k1_xboole_0,C_125)) = k3_xboole_0(k4_xboole_0(A_1,B_2),k4_xboole_0(A_1,C_125)) ),
    inference(superposition,[status(thm),theory(equality)],[c_39,c_5309])).

tff(c_5585,plain,(
    ! [A_1,B_2,C_125] : k3_xboole_0(k4_xboole_0(A_1,B_2),k4_xboole_0(A_1,C_125)) = k4_xboole_0(A_1,k2_xboole_0(B_2,C_125)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_429,c_5524])).

tff(c_16,plain,(
    k3_xboole_0(k4_xboole_0('#skF_1','#skF_2'),k4_xboole_0('#skF_1','#skF_3')) != k4_xboole_0('#skF_1',k2_xboole_0('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_47021,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5585,c_16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n004.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 12:38:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 10.92/5.08  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.92/5.08  
% 10.92/5.08  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.92/5.09  %$ r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 10.92/5.09  
% 10.92/5.09  %Foreground sorts:
% 10.92/5.09  
% 10.92/5.09  
% 10.92/5.09  %Background operators:
% 10.92/5.09  
% 10.92/5.09  
% 10.92/5.09  %Foreground operators:
% 10.92/5.09  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 10.92/5.09  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 10.92/5.09  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 10.92/5.09  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 10.92/5.09  tff('#skF_2', type, '#skF_2': $i).
% 10.92/5.09  tff('#skF_3', type, '#skF_3': $i).
% 10.92/5.09  tff('#skF_1', type, '#skF_1': $i).
% 10.92/5.09  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 10.92/5.09  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 10.92/5.09  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 10.92/5.09  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 10.92/5.09  
% 10.92/5.10  tff(f_35, axiom, (![A, B, C]: (k4_xboole_0(k4_xboole_0(A, B), C) = k4_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_xboole_1)).
% 10.92/5.10  tff(f_33, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 10.92/5.10  tff(f_27, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 10.92/5.10  tff(f_31, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t37_xboole_1)).
% 10.92/5.10  tff(f_39, axiom, (![A, B, C]: (k3_xboole_0(A, k4_xboole_0(B, C)) = k4_xboole_0(k3_xboole_0(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_xboole_1)).
% 10.92/5.10  tff(f_37, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 10.92/5.10  tff(f_42, negated_conjecture, ~(![A, B, C]: (k4_xboole_0(A, k2_xboole_0(B, C)) = k3_xboole_0(k4_xboole_0(A, B), k4_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t53_xboole_1)).
% 10.92/5.10  tff(c_10, plain, (![A_6, B_7, C_8]: (k4_xboole_0(k4_xboole_0(A_6, B_7), C_8)=k4_xboole_0(A_6, k2_xboole_0(B_7, C_8)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 10.92/5.10  tff(c_8, plain, (![A_5]: (k4_xboole_0(A_5, k1_xboole_0)=A_5)), inference(cnfTransformation, [status(thm)], [f_33])).
% 10.92/5.10  tff(c_360, plain, (![A_39, B_40, C_41]: (k4_xboole_0(k4_xboole_0(A_39, B_40), C_41)=k4_xboole_0(A_39, k2_xboole_0(B_40, C_41)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 10.92/5.10  tff(c_429, plain, (![A_5, C_41]: (k4_xboole_0(A_5, k2_xboole_0(k1_xboole_0, C_41))=k4_xboole_0(A_5, C_41))), inference(superposition, [status(thm), theory('equality')], [c_8, c_360])).
% 10.92/5.10  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(k4_xboole_0(A_1, B_2), A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 10.92/5.10  tff(c_31, plain, (![A_18, B_19]: (k4_xboole_0(A_18, B_19)=k1_xboole_0 | ~r1_tarski(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_31])).
% 10.92/5.10  tff(c_39, plain, (![A_1, B_2]: (k4_xboole_0(k4_xboole_0(A_1, B_2), A_1)=k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_31])).
% 10.92/5.10  tff(c_14, plain, (![A_11, B_12, C_13]: (k4_xboole_0(k3_xboole_0(A_11, B_12), C_13)=k3_xboole_0(A_11, k4_xboole_0(B_12, C_13)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 10.92/5.10  tff(c_12, plain, (![A_9, B_10]: (k4_xboole_0(A_9, k4_xboole_0(A_9, B_10))=k3_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_37])).
% 10.92/5.10  tff(c_406, plain, (![A_9, B_10, C_41]: (k4_xboole_0(A_9, k2_xboole_0(k4_xboole_0(A_9, B_10), C_41))=k4_xboole_0(k3_xboole_0(A_9, B_10), C_41))), inference(superposition, [status(thm), theory('equality')], [c_12, c_360])).
% 10.92/5.10  tff(c_5309, plain, (![A_123, B_124, C_125]: (k4_xboole_0(A_123, k2_xboole_0(k4_xboole_0(A_123, B_124), C_125))=k3_xboole_0(A_123, k4_xboole_0(B_124, C_125)))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_406])).
% 10.92/5.10  tff(c_5524, plain, (![A_1, B_2, C_125]: (k4_xboole_0(k4_xboole_0(A_1, B_2), k2_xboole_0(k1_xboole_0, C_125))=k3_xboole_0(k4_xboole_0(A_1, B_2), k4_xboole_0(A_1, C_125)))), inference(superposition, [status(thm), theory('equality')], [c_39, c_5309])).
% 10.92/5.10  tff(c_5585, plain, (![A_1, B_2, C_125]: (k3_xboole_0(k4_xboole_0(A_1, B_2), k4_xboole_0(A_1, C_125))=k4_xboole_0(A_1, k2_xboole_0(B_2, C_125)))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_429, c_5524])).
% 10.92/5.10  tff(c_16, plain, (k3_xboole_0(k4_xboole_0('#skF_1', '#skF_2'), k4_xboole_0('#skF_1', '#skF_3'))!=k4_xboole_0('#skF_1', k2_xboole_0('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_42])).
% 10.92/5.10  tff(c_47021, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_5585, c_16])).
% 10.92/5.10  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.92/5.10  
% 10.92/5.10  Inference rules
% 10.92/5.10  ----------------------
% 10.92/5.10  #Ref     : 0
% 10.92/5.10  #Sup     : 11675
% 10.92/5.10  #Fact    : 0
% 10.92/5.10  #Define  : 0
% 10.92/5.10  #Split   : 0
% 10.92/5.10  #Chain   : 0
% 10.92/5.10  #Close   : 0
% 10.92/5.10  
% 10.92/5.10  Ordering : KBO
% 10.92/5.10  
% 10.92/5.10  Simplification rules
% 10.92/5.10  ----------------------
% 10.92/5.10  #Subsume      : 0
% 10.92/5.10  #Demod        : 13718
% 10.92/5.10  #Tautology    : 8916
% 10.92/5.10  #SimpNegUnit  : 0
% 10.92/5.10  #BackRed      : 3
% 10.92/5.10  
% 10.92/5.10  #Partial instantiations: 0
% 10.92/5.10  #Strategies tried      : 1
% 10.92/5.10  
% 10.92/5.10  Timing (in seconds)
% 10.92/5.10  ----------------------
% 10.92/5.10  Preprocessing        : 0.31
% 10.92/5.10  Parsing              : 0.16
% 10.92/5.10  CNF conversion       : 0.02
% 10.92/5.10  Main loop            : 3.96
% 10.92/5.10  Inferencing          : 0.81
% 10.92/5.10  Reduction            : 2.17
% 10.92/5.10  Demodulation         : 1.93
% 10.92/5.10  BG Simplification    : 0.09
% 10.92/5.10  Subsumption          : 0.70
% 10.92/5.10  Abstraction          : 0.18
% 10.92/5.10  MUC search           : 0.00
% 10.92/5.10  Cooper               : 0.00
% 10.92/5.10  Total                : 4.29
% 10.92/5.10  Index Insertion      : 0.00
% 10.92/5.10  Index Deletion       : 0.00
% 10.92/5.10  Index Matching       : 0.00
% 10.92/5.10  BG Taut test         : 0.00
%------------------------------------------------------------------------------

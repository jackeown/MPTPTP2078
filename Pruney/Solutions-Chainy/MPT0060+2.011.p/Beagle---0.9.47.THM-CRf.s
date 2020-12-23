%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:43:06 EST 2020

% Result     : Theorem 11.51s
% Output     : CNFRefutation 11.61s
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

tff(f_33,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_31,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_39,axiom,(
    ! [A,B,C] : k3_xboole_0(A,k4_xboole_0(B,C)) = k4_xboole_0(k3_xboole_0(A,B),C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_42,negated_conjecture,(
    ~ ! [A,B,C] : k4_xboole_0(A,k2_xboole_0(B,C)) = k3_xboole_0(k4_xboole_0(A,B),k4_xboole_0(A,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t53_xboole_1)).

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

tff(c_6,plain,(
    ! [A_3,B_4] : r1_tarski(k4_xboole_0(A_3,B_4),A_3) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_31,plain,(
    ! [A_18,B_19] :
      ( k4_xboole_0(A_18,B_19) = k1_xboole_0
      | ~ r1_tarski(A_18,B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_39,plain,(
    ! [A_3,B_4] : k4_xboole_0(k4_xboole_0(A_3,B_4),A_3) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_31])).

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
    ! [A_3,B_4,C_125] : k4_xboole_0(k4_xboole_0(A_3,B_4),k2_xboole_0(k1_xboole_0,C_125)) = k3_xboole_0(k4_xboole_0(A_3,B_4),k4_xboole_0(A_3,C_125)) ),
    inference(superposition,[status(thm),theory(equality)],[c_39,c_5309])).

tff(c_5585,plain,(
    ! [A_3,B_4,C_125] : k3_xboole_0(k4_xboole_0(A_3,B_4),k4_xboole_0(A_3,C_125)) = k4_xboole_0(A_3,k2_xboole_0(B_4,C_125)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_429,c_5524])).

tff(c_16,plain,(
    k3_xboole_0(k4_xboole_0('#skF_1','#skF_2'),k4_xboole_0('#skF_1','#skF_3')) != k4_xboole_0('#skF_1',k2_xboole_0('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_47021,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5585,c_16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n016.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:46:34 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 11.51/5.06  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.51/5.06  
% 11.51/5.06  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.61/5.06  %$ r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 11.61/5.06  
% 11.61/5.06  %Foreground sorts:
% 11.61/5.06  
% 11.61/5.06  
% 11.61/5.06  %Background operators:
% 11.61/5.06  
% 11.61/5.06  
% 11.61/5.06  %Foreground operators:
% 11.61/5.06  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 11.61/5.06  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 11.61/5.06  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 11.61/5.06  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 11.61/5.06  tff('#skF_2', type, '#skF_2': $i).
% 11.61/5.06  tff('#skF_3', type, '#skF_3': $i).
% 11.61/5.06  tff('#skF_1', type, '#skF_1': $i).
% 11.61/5.06  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 11.61/5.06  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 11.61/5.06  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 11.61/5.06  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 11.61/5.06  
% 11.61/5.07  tff(f_35, axiom, (![A, B, C]: (k4_xboole_0(k4_xboole_0(A, B), C) = k4_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_xboole_1)).
% 11.61/5.07  tff(f_33, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 11.61/5.07  tff(f_31, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 11.61/5.07  tff(f_29, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 11.61/5.07  tff(f_39, axiom, (![A, B, C]: (k3_xboole_0(A, k4_xboole_0(B, C)) = k4_xboole_0(k3_xboole_0(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_xboole_1)).
% 11.61/5.07  tff(f_37, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 11.61/5.07  tff(f_42, negated_conjecture, ~(![A, B, C]: (k4_xboole_0(A, k2_xboole_0(B, C)) = k3_xboole_0(k4_xboole_0(A, B), k4_xboole_0(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t53_xboole_1)).
% 11.61/5.07  tff(c_10, plain, (![A_6, B_7, C_8]: (k4_xboole_0(k4_xboole_0(A_6, B_7), C_8)=k4_xboole_0(A_6, k2_xboole_0(B_7, C_8)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 11.61/5.07  tff(c_8, plain, (![A_5]: (k4_xboole_0(A_5, k1_xboole_0)=A_5)), inference(cnfTransformation, [status(thm)], [f_33])).
% 11.61/5.07  tff(c_360, plain, (![A_39, B_40, C_41]: (k4_xboole_0(k4_xboole_0(A_39, B_40), C_41)=k4_xboole_0(A_39, k2_xboole_0(B_40, C_41)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 11.61/5.07  tff(c_429, plain, (![A_5, C_41]: (k4_xboole_0(A_5, k2_xboole_0(k1_xboole_0, C_41))=k4_xboole_0(A_5, C_41))), inference(superposition, [status(thm), theory('equality')], [c_8, c_360])).
% 11.61/5.07  tff(c_6, plain, (![A_3, B_4]: (r1_tarski(k4_xboole_0(A_3, B_4), A_3))), inference(cnfTransformation, [status(thm)], [f_31])).
% 11.61/5.07  tff(c_31, plain, (![A_18, B_19]: (k4_xboole_0(A_18, B_19)=k1_xboole_0 | ~r1_tarski(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_29])).
% 11.61/5.07  tff(c_39, plain, (![A_3, B_4]: (k4_xboole_0(k4_xboole_0(A_3, B_4), A_3)=k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_31])).
% 11.61/5.07  tff(c_14, plain, (![A_11, B_12, C_13]: (k4_xboole_0(k3_xboole_0(A_11, B_12), C_13)=k3_xboole_0(A_11, k4_xboole_0(B_12, C_13)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 11.61/5.07  tff(c_12, plain, (![A_9, B_10]: (k4_xboole_0(A_9, k4_xboole_0(A_9, B_10))=k3_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_37])).
% 11.61/5.07  tff(c_406, plain, (![A_9, B_10, C_41]: (k4_xboole_0(A_9, k2_xboole_0(k4_xboole_0(A_9, B_10), C_41))=k4_xboole_0(k3_xboole_0(A_9, B_10), C_41))), inference(superposition, [status(thm), theory('equality')], [c_12, c_360])).
% 11.61/5.07  tff(c_5309, plain, (![A_123, B_124, C_125]: (k4_xboole_0(A_123, k2_xboole_0(k4_xboole_0(A_123, B_124), C_125))=k3_xboole_0(A_123, k4_xboole_0(B_124, C_125)))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_406])).
% 11.61/5.07  tff(c_5524, plain, (![A_3, B_4, C_125]: (k4_xboole_0(k4_xboole_0(A_3, B_4), k2_xboole_0(k1_xboole_0, C_125))=k3_xboole_0(k4_xboole_0(A_3, B_4), k4_xboole_0(A_3, C_125)))), inference(superposition, [status(thm), theory('equality')], [c_39, c_5309])).
% 11.61/5.07  tff(c_5585, plain, (![A_3, B_4, C_125]: (k3_xboole_0(k4_xboole_0(A_3, B_4), k4_xboole_0(A_3, C_125))=k4_xboole_0(A_3, k2_xboole_0(B_4, C_125)))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_429, c_5524])).
% 11.61/5.07  tff(c_16, plain, (k3_xboole_0(k4_xboole_0('#skF_1', '#skF_2'), k4_xboole_0('#skF_1', '#skF_3'))!=k4_xboole_0('#skF_1', k2_xboole_0('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_42])).
% 11.61/5.07  tff(c_47021, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_5585, c_16])).
% 11.61/5.07  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.61/5.07  
% 11.61/5.07  Inference rules
% 11.61/5.07  ----------------------
% 11.61/5.07  #Ref     : 0
% 11.61/5.07  #Sup     : 11675
% 11.61/5.07  #Fact    : 0
% 11.61/5.07  #Define  : 0
% 11.61/5.07  #Split   : 0
% 11.61/5.07  #Chain   : 0
% 11.61/5.07  #Close   : 0
% 11.61/5.07  
% 11.61/5.07  Ordering : KBO
% 11.61/5.07  
% 11.61/5.07  Simplification rules
% 11.61/5.07  ----------------------
% 11.61/5.07  #Subsume      : 0
% 11.61/5.07  #Demod        : 13718
% 11.61/5.07  #Tautology    : 8916
% 11.61/5.07  #SimpNegUnit  : 0
% 11.61/5.07  #BackRed      : 3
% 11.61/5.07  
% 11.61/5.07  #Partial instantiations: 0
% 11.61/5.07  #Strategies tried      : 1
% 11.61/5.07  
% 11.61/5.07  Timing (in seconds)
% 11.61/5.07  ----------------------
% 11.61/5.08  Preprocessing        : 0.28
% 11.61/5.08  Parsing              : 0.15
% 11.61/5.08  CNF conversion       : 0.02
% 11.61/5.08  Main loop            : 4.03
% 11.61/5.08  Inferencing          : 0.79
% 11.61/5.08  Reduction            : 2.21
% 11.61/5.08  Demodulation         : 1.97
% 11.61/5.08  BG Simplification    : 0.09
% 11.61/5.08  Subsumption          : 0.73
% 11.61/5.08  Abstraction          : 0.17
% 11.61/5.08  MUC search           : 0.00
% 11.61/5.08  Cooper               : 0.00
% 11.61/5.08  Total                : 4.34
% 11.61/5.08  Index Insertion      : 0.00
% 11.61/5.08  Index Deletion       : 0.00
% 11.61/5.08  Index Matching       : 0.00
% 11.61/5.08  BG Taut test         : 0.00
%------------------------------------------------------------------------------

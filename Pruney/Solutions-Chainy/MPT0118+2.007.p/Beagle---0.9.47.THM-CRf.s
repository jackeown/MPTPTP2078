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
% DateTime   : Thu Dec  3 09:45:33 EST 2020

% Result     : Theorem 3.06s
% Output     : CNFRefutation 3.12s
% Verified   : 
% Statistics : Number of formulae       :   24 (  31 expanded)
%              Number of leaves         :   12 (  16 expanded)
%              Depth                    :    5
%              Number of atoms          :   16 (  23 expanded)
%              Number of equality atoms :   15 (  22 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k4_xboole_0 > k3_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

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

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_33,axiom,(
    ! [A,B,C] : k3_xboole_0(A,k4_xboole_0(B,C)) = k4_xboole_0(k3_xboole_0(A,B),C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k4_xboole_0(A,k3_xboole_0(A,B)) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

tff(f_36,negated_conjecture,(
    ~ ! [A,B,C] : k4_xboole_0(k3_xboole_0(A,B),k3_xboole_0(C,B)) = k3_xboole_0(k4_xboole_0(A,C),B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t111_xboole_1)).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_141,plain,(
    ! [A_20,B_21,C_22] : k4_xboole_0(k3_xboole_0(A_20,B_21),C_22) = k3_xboole_0(A_20,k4_xboole_0(B_21,C_22)) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_250,plain,(
    ! [A_25,B_26,C_27] : k4_xboole_0(k3_xboole_0(A_25,B_26),C_27) = k3_xboole_0(B_26,k4_xboole_0(A_25,C_27)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_141])).

tff(c_8,plain,(
    ! [A_7,B_8,C_9] : k4_xboole_0(k3_xboole_0(A_7,B_8),C_9) = k3_xboole_0(A_7,k4_xboole_0(B_8,C_9)) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_256,plain,(
    ! [B_26,A_25,C_27] : k3_xboole_0(B_26,k4_xboole_0(A_25,C_27)) = k3_xboole_0(A_25,k4_xboole_0(B_26,C_27)) ),
    inference(superposition,[status(thm),theory(equality)],[c_250,c_8])).

tff(c_61,plain,(
    ! [A_14,B_15] : k4_xboole_0(A_14,k3_xboole_0(A_14,B_15)) = k4_xboole_0(A_14,B_15) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_76,plain,(
    ! [B_2,A_1] : k4_xboole_0(B_2,k3_xboole_0(A_1,B_2)) = k4_xboole_0(B_2,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_61])).

tff(c_10,plain,(
    k4_xboole_0(k3_xboole_0('#skF_1','#skF_2'),k3_xboole_0('#skF_3','#skF_2')) != k3_xboole_0(k4_xboole_0('#skF_1','#skF_3'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_11,plain,(
    k3_xboole_0('#skF_1',k4_xboole_0('#skF_2',k3_xboole_0('#skF_3','#skF_2'))) != k3_xboole_0(k4_xboole_0('#skF_1','#skF_3'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_10])).

tff(c_12,plain,(
    k3_xboole_0('#skF_1',k4_xboole_0('#skF_2',k3_xboole_0('#skF_3','#skF_2'))) != k3_xboole_0('#skF_2',k4_xboole_0('#skF_1','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_11])).

tff(c_248,plain,(
    k3_xboole_0('#skF_2',k4_xboole_0('#skF_1','#skF_3')) != k3_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_12])).

tff(c_1168,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_256,c_248])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n013.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 15:23:54 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.06/1.48  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.06/1.49  
% 3.06/1.49  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.12/1.49  %$ k4_xboole_0 > k3_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1
% 3.12/1.49  
% 3.12/1.49  %Foreground sorts:
% 3.12/1.49  
% 3.12/1.49  
% 3.12/1.49  %Background operators:
% 3.12/1.49  
% 3.12/1.49  
% 3.12/1.49  %Foreground operators:
% 3.12/1.49  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.12/1.49  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.12/1.49  tff('#skF_2', type, '#skF_2': $i).
% 3.12/1.49  tff('#skF_3', type, '#skF_3': $i).
% 3.12/1.49  tff('#skF_1', type, '#skF_1': $i).
% 3.12/1.49  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.12/1.49  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.12/1.49  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.12/1.49  
% 3.12/1.50  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 3.12/1.50  tff(f_33, axiom, (![A, B, C]: (k3_xboole_0(A, k4_xboole_0(B, C)) = k4_xboole_0(k3_xboole_0(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_xboole_1)).
% 3.12/1.50  tff(f_29, axiom, (![A, B]: (k4_xboole_0(A, k3_xboole_0(A, B)) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_xboole_1)).
% 3.12/1.50  tff(f_36, negated_conjecture, ~(![A, B, C]: (k4_xboole_0(k3_xboole_0(A, B), k3_xboole_0(C, B)) = k3_xboole_0(k4_xboole_0(A, C), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t111_xboole_1)).
% 3.12/1.50  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.12/1.50  tff(c_141, plain, (![A_20, B_21, C_22]: (k4_xboole_0(k3_xboole_0(A_20, B_21), C_22)=k3_xboole_0(A_20, k4_xboole_0(B_21, C_22)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.12/1.50  tff(c_250, plain, (![A_25, B_26, C_27]: (k4_xboole_0(k3_xboole_0(A_25, B_26), C_27)=k3_xboole_0(B_26, k4_xboole_0(A_25, C_27)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_141])).
% 3.12/1.50  tff(c_8, plain, (![A_7, B_8, C_9]: (k4_xboole_0(k3_xboole_0(A_7, B_8), C_9)=k3_xboole_0(A_7, k4_xboole_0(B_8, C_9)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.12/1.50  tff(c_256, plain, (![B_26, A_25, C_27]: (k3_xboole_0(B_26, k4_xboole_0(A_25, C_27))=k3_xboole_0(A_25, k4_xboole_0(B_26, C_27)))), inference(superposition, [status(thm), theory('equality')], [c_250, c_8])).
% 3.12/1.50  tff(c_61, plain, (![A_14, B_15]: (k4_xboole_0(A_14, k3_xboole_0(A_14, B_15))=k4_xboole_0(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.12/1.50  tff(c_76, plain, (![B_2, A_1]: (k4_xboole_0(B_2, k3_xboole_0(A_1, B_2))=k4_xboole_0(B_2, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_61])).
% 3.12/1.50  tff(c_10, plain, (k4_xboole_0(k3_xboole_0('#skF_1', '#skF_2'), k3_xboole_0('#skF_3', '#skF_2'))!=k3_xboole_0(k4_xboole_0('#skF_1', '#skF_3'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.12/1.50  tff(c_11, plain, (k3_xboole_0('#skF_1', k4_xboole_0('#skF_2', k3_xboole_0('#skF_3', '#skF_2')))!=k3_xboole_0(k4_xboole_0('#skF_1', '#skF_3'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_8, c_10])).
% 3.12/1.50  tff(c_12, plain, (k3_xboole_0('#skF_1', k4_xboole_0('#skF_2', k3_xboole_0('#skF_3', '#skF_2')))!=k3_xboole_0('#skF_2', k4_xboole_0('#skF_1', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_11])).
% 3.12/1.50  tff(c_248, plain, (k3_xboole_0('#skF_2', k4_xboole_0('#skF_1', '#skF_3'))!=k3_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_12])).
% 3.12/1.50  tff(c_1168, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_256, c_248])).
% 3.12/1.50  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.12/1.50  
% 3.12/1.50  Inference rules
% 3.12/1.50  ----------------------
% 3.12/1.50  #Ref     : 0
% 3.12/1.50  #Sup     : 267
% 3.12/1.50  #Fact    : 0
% 3.12/1.50  #Define  : 0
% 3.12/1.50  #Split   : 0
% 3.12/1.50  #Chain   : 0
% 3.12/1.50  #Close   : 0
% 3.12/1.50  
% 3.12/1.50  Ordering : KBO
% 3.12/1.50  
% 3.12/1.50  Simplification rules
% 3.12/1.50  ----------------------
% 3.12/1.50  #Subsume      : 28
% 3.12/1.50  #Demod        : 368
% 3.12/1.50  #Tautology    : 141
% 3.12/1.50  #SimpNegUnit  : 0
% 3.12/1.50  #BackRed      : 1
% 3.12/1.50  
% 3.12/1.50  #Partial instantiations: 0
% 3.12/1.50  #Strategies tried      : 1
% 3.12/1.50  
% 3.12/1.50  Timing (in seconds)
% 3.12/1.50  ----------------------
% 3.12/1.50  Preprocessing        : 0.29
% 3.12/1.50  Parsing              : 0.15
% 3.12/1.50  CNF conversion       : 0.02
% 3.12/1.50  Main loop            : 0.41
% 3.12/1.50  Inferencing          : 0.12
% 3.12/1.50  Reduction            : 0.21
% 3.12/1.50  Demodulation         : 0.19
% 3.12/1.50  BG Simplification    : 0.02
% 3.12/1.50  Subsumption          : 0.05
% 3.12/1.50  Abstraction          : 0.03
% 3.12/1.50  MUC search           : 0.00
% 3.12/1.50  Cooper               : 0.00
% 3.12/1.50  Total                : 0.73
% 3.12/1.50  Index Insertion      : 0.00
% 3.12/1.50  Index Deletion       : 0.00
% 3.12/1.50  Index Matching       : 0.00
% 3.12/1.50  BG Taut test         : 0.00
%------------------------------------------------------------------------------

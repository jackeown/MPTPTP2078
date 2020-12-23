%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:45:26 EST 2020

% Result     : Theorem 2.63s
% Output     : CNFRefutation 2.63s
% Verified   : 
% Statistics : Number of formulae       :   34 (  40 expanded)
%              Number of leaves         :   17 (  21 expanded)
%              Depth                    :    7
%              Number of atoms          :   27 (  37 expanded)
%              Number of equality atoms :   17 (  22 expanded)
%              Maximal formula depth    :    6 (   3 average)
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

tff(f_37,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_35,axiom,(
    ! [A,B,C] : k4_xboole_0(k4_xboole_0(A,B),C) = k4_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_33,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_42,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_tarski(A,B)
       => r1_tarski(k3_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t108_xboole_1)).

tff(c_12,plain,(
    ! [A_9,B_10] : k4_xboole_0(A_9,k4_xboole_0(A_9,B_10)) = k3_xboole_0(A_9,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_133,plain,(
    ! [A_22,B_23,C_24] : k4_xboole_0(k4_xboole_0(A_22,B_23),C_24) = k4_xboole_0(A_22,k2_xboole_0(B_23,C_24)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_828,plain,(
    ! [A_48,B_49,C_50] : k4_xboole_0(A_48,k2_xboole_0(k4_xboole_0(A_48,B_49),C_50)) = k4_xboole_0(k3_xboole_0(A_48,B_49),C_50) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_133])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_8,plain,(
    ! [A_5] : r1_tarski(k1_xboole_0,A_5) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_56,plain,(
    ! [A_16,B_17] :
      ( k4_xboole_0(A_16,B_17) = k1_xboole_0
      | ~ r1_tarski(A_16,B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_67,plain,(
    ! [A_5] : k4_xboole_0(k1_xboole_0,A_5) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_8,c_56])).

tff(c_16,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_68,plain,(
    k4_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_16,c_56])).

tff(c_168,plain,(
    ! [C_24] : k4_xboole_0('#skF_1',k2_xboole_0('#skF_2',C_24)) = k4_xboole_0(k1_xboole_0,C_24) ),
    inference(superposition,[status(thm),theory(equality)],[c_68,c_133])).

tff(c_180,plain,(
    ! [C_25] : k4_xboole_0('#skF_1',k2_xboole_0('#skF_2',C_25)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_67,c_168])).

tff(c_194,plain,(
    ! [B_2] : k4_xboole_0('#skF_1',k2_xboole_0(B_2,'#skF_2')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_180])).

tff(c_854,plain,(
    ! [B_49] : k4_xboole_0(k3_xboole_0('#skF_1',B_49),'#skF_2') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_828,c_194])).

tff(c_51,plain,(
    ! [A_14,B_15] :
      ( r1_tarski(A_14,B_15)
      | k4_xboole_0(A_14,B_15) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_14,plain,(
    ~ r1_tarski(k3_xboole_0('#skF_1','#skF_3'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_55,plain,(
    k4_xboole_0(k3_xboole_0('#skF_1','#skF_3'),'#skF_2') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_51,c_14])).

tff(c_989,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_854,c_55])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:23:05 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.63/1.39  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.63/1.39  
% 2.63/1.39  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.63/1.40  %$ r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.63/1.40  
% 2.63/1.40  %Foreground sorts:
% 2.63/1.40  
% 2.63/1.40  
% 2.63/1.40  %Background operators:
% 2.63/1.40  
% 2.63/1.40  
% 2.63/1.40  %Foreground operators:
% 2.63/1.40  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.63/1.40  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.63/1.40  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.63/1.40  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.63/1.40  tff('#skF_2', type, '#skF_2': $i).
% 2.63/1.40  tff('#skF_3', type, '#skF_3': $i).
% 2.63/1.40  tff('#skF_1', type, '#skF_1': $i).
% 2.63/1.40  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.63/1.40  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.63/1.40  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.63/1.40  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.63/1.40  
% 2.63/1.41  tff(f_37, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 2.63/1.41  tff(f_35, axiom, (![A, B, C]: (k4_xboole_0(k4_xboole_0(A, B), C) = k4_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_xboole_1)).
% 2.63/1.41  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 2.63/1.41  tff(f_33, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.63/1.41  tff(f_31, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 2.63/1.41  tff(f_42, negated_conjecture, ~(![A, B, C]: (r1_tarski(A, B) => r1_tarski(k3_xboole_0(A, C), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t108_xboole_1)).
% 2.63/1.41  tff(c_12, plain, (![A_9, B_10]: (k4_xboole_0(A_9, k4_xboole_0(A_9, B_10))=k3_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.63/1.41  tff(c_133, plain, (![A_22, B_23, C_24]: (k4_xboole_0(k4_xboole_0(A_22, B_23), C_24)=k4_xboole_0(A_22, k2_xboole_0(B_23, C_24)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.63/1.41  tff(c_828, plain, (![A_48, B_49, C_50]: (k4_xboole_0(A_48, k2_xboole_0(k4_xboole_0(A_48, B_49), C_50))=k4_xboole_0(k3_xboole_0(A_48, B_49), C_50))), inference(superposition, [status(thm), theory('equality')], [c_12, c_133])).
% 2.63/1.41  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.63/1.41  tff(c_8, plain, (![A_5]: (r1_tarski(k1_xboole_0, A_5))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.63/1.41  tff(c_56, plain, (![A_16, B_17]: (k4_xboole_0(A_16, B_17)=k1_xboole_0 | ~r1_tarski(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.63/1.41  tff(c_67, plain, (![A_5]: (k4_xboole_0(k1_xboole_0, A_5)=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_56])).
% 2.63/1.41  tff(c_16, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.63/1.41  tff(c_68, plain, (k4_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_16, c_56])).
% 2.63/1.41  tff(c_168, plain, (![C_24]: (k4_xboole_0('#skF_1', k2_xboole_0('#skF_2', C_24))=k4_xboole_0(k1_xboole_0, C_24))), inference(superposition, [status(thm), theory('equality')], [c_68, c_133])).
% 2.63/1.41  tff(c_180, plain, (![C_25]: (k4_xboole_0('#skF_1', k2_xboole_0('#skF_2', C_25))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_67, c_168])).
% 2.63/1.41  tff(c_194, plain, (![B_2]: (k4_xboole_0('#skF_1', k2_xboole_0(B_2, '#skF_2'))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2, c_180])).
% 2.63/1.41  tff(c_854, plain, (![B_49]: (k4_xboole_0(k3_xboole_0('#skF_1', B_49), '#skF_2')=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_828, c_194])).
% 2.63/1.41  tff(c_51, plain, (![A_14, B_15]: (r1_tarski(A_14, B_15) | k4_xboole_0(A_14, B_15)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.63/1.41  tff(c_14, plain, (~r1_tarski(k3_xboole_0('#skF_1', '#skF_3'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.63/1.41  tff(c_55, plain, (k4_xboole_0(k3_xboole_0('#skF_1', '#skF_3'), '#skF_2')!=k1_xboole_0), inference(resolution, [status(thm)], [c_51, c_14])).
% 2.63/1.41  tff(c_989, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_854, c_55])).
% 2.63/1.41  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.63/1.41  
% 2.63/1.41  Inference rules
% 2.63/1.41  ----------------------
% 2.63/1.41  #Ref     : 0
% 2.63/1.41  #Sup     : 246
% 2.63/1.41  #Fact    : 0
% 2.63/1.41  #Define  : 0
% 2.63/1.41  #Split   : 0
% 2.63/1.41  #Chain   : 0
% 2.63/1.41  #Close   : 0
% 2.63/1.41  
% 2.63/1.41  Ordering : KBO
% 2.63/1.41  
% 2.63/1.41  Simplification rules
% 2.63/1.41  ----------------------
% 2.63/1.41  #Subsume      : 0
% 2.63/1.41  #Demod        : 103
% 2.63/1.41  #Tautology    : 143
% 2.63/1.41  #SimpNegUnit  : 0
% 2.63/1.41  #BackRed      : 1
% 2.63/1.41  
% 2.63/1.41  #Partial instantiations: 0
% 2.63/1.41  #Strategies tried      : 1
% 2.63/1.41  
% 2.63/1.41  Timing (in seconds)
% 2.63/1.41  ----------------------
% 2.63/1.41  Preprocessing        : 0.25
% 2.63/1.41  Parsing              : 0.14
% 2.63/1.41  CNF conversion       : 0.01
% 2.63/1.41  Main loop            : 0.38
% 2.63/1.41  Inferencing          : 0.13
% 2.63/1.41  Reduction            : 0.15
% 2.63/1.41  Demodulation         : 0.12
% 2.63/1.41  BG Simplification    : 0.02
% 2.63/1.41  Subsumption          : 0.06
% 2.63/1.41  Abstraction          : 0.02
% 2.63/1.41  MUC search           : 0.00
% 2.63/1.41  Cooper               : 0.00
% 2.63/1.41  Total                : 0.65
% 2.63/1.41  Index Insertion      : 0.00
% 2.63/1.41  Index Deletion       : 0.00
% 2.63/1.41  Index Matching       : 0.00
% 2.63/1.41  BG Taut test         : 0.00
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:45:32 EST 2020

% Result     : Theorem 1.88s
% Output     : CNFRefutation 1.88s
% Verified   : 
% Statistics : Number of formulae       :   25 (  32 expanded)
%              Number of leaves         :   13 (  17 expanded)
%              Depth                    :    5
%              Number of atoms          :   16 (  23 expanded)
%              Number of equality atoms :   15 (  22 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

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

tff(f_31,axiom,(
    ! [A,B] : k4_xboole_0(A,k3_xboole_0(A,B)) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

tff(f_36,negated_conjecture,(
    ~ ! [A,B,C] : k4_xboole_0(k3_xboole_0(A,B),k3_xboole_0(C,B)) = k3_xboole_0(k4_xboole_0(A,C),B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t111_xboole_1)).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_104,plain,(
    ! [A_18,B_19,C_20] : k4_xboole_0(k3_xboole_0(A_18,B_19),C_20) = k3_xboole_0(A_18,k4_xboole_0(B_19,C_20)) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_167,plain,(
    ! [B_23,A_24,C_25] : k4_xboole_0(k3_xboole_0(B_23,A_24),C_25) = k3_xboole_0(A_24,k4_xboole_0(B_23,C_25)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_104])).

tff(c_8,plain,(
    ! [A_7,B_8,C_9] : k4_xboole_0(k3_xboole_0(A_7,B_8),C_9) = k3_xboole_0(A_7,k4_xboole_0(B_8,C_9)) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_173,plain,(
    ! [B_23,A_24,C_25] : k3_xboole_0(B_23,k4_xboole_0(A_24,C_25)) = k3_xboole_0(A_24,k4_xboole_0(B_23,C_25)) ),
    inference(superposition,[status(thm),theory(equality)],[c_167,c_8])).

tff(c_46,plain,(
    ! [A_12,B_13] : k4_xboole_0(A_12,k3_xboole_0(A_12,B_13)) = k4_xboole_0(A_12,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_58,plain,(
    ! [B_2,A_1] : k4_xboole_0(B_2,k3_xboole_0(A_1,B_2)) = k4_xboole_0(B_2,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_46])).

tff(c_10,plain,(
    k4_xboole_0(k3_xboole_0('#skF_1','#skF_2'),k3_xboole_0('#skF_3','#skF_2')) != k3_xboole_0(k4_xboole_0('#skF_1','#skF_3'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_11,plain,(
    k3_xboole_0('#skF_1',k4_xboole_0('#skF_2',k3_xboole_0('#skF_3','#skF_2'))) != k3_xboole_0(k4_xboole_0('#skF_1','#skF_3'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_10])).

tff(c_12,plain,(
    k3_xboole_0('#skF_1',k4_xboole_0('#skF_2',k3_xboole_0('#skF_3','#skF_2'))) != k3_xboole_0('#skF_2',k4_xboole_0('#skF_1','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_11])).

tff(c_210,plain,(
    k3_xboole_0('#skF_2',k4_xboole_0('#skF_1','#skF_3')) != k3_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_12])).

tff(c_214,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_173,c_210])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:59:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.88/1.18  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.88/1.19  
% 1.88/1.19  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.88/1.19  %$ k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1
% 1.88/1.19  
% 1.88/1.19  %Foreground sorts:
% 1.88/1.19  
% 1.88/1.19  
% 1.88/1.19  %Background operators:
% 1.88/1.19  
% 1.88/1.19  
% 1.88/1.19  %Foreground operators:
% 1.88/1.19  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.88/1.19  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.88/1.19  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 1.88/1.19  tff('#skF_2', type, '#skF_2': $i).
% 1.88/1.19  tff('#skF_3', type, '#skF_3': $i).
% 1.88/1.19  tff('#skF_1', type, '#skF_1': $i).
% 1.88/1.19  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.88/1.19  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.88/1.19  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.88/1.19  
% 1.88/1.20  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 1.88/1.20  tff(f_33, axiom, (![A, B, C]: (k3_xboole_0(A, k4_xboole_0(B, C)) = k4_xboole_0(k3_xboole_0(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_xboole_1)).
% 1.88/1.20  tff(f_31, axiom, (![A, B]: (k4_xboole_0(A, k3_xboole_0(A, B)) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_xboole_1)).
% 1.88/1.20  tff(f_36, negated_conjecture, ~(![A, B, C]: (k4_xboole_0(k3_xboole_0(A, B), k3_xboole_0(C, B)) = k3_xboole_0(k4_xboole_0(A, C), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t111_xboole_1)).
% 1.88/1.20  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.88/1.20  tff(c_104, plain, (![A_18, B_19, C_20]: (k4_xboole_0(k3_xboole_0(A_18, B_19), C_20)=k3_xboole_0(A_18, k4_xboole_0(B_19, C_20)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.88/1.20  tff(c_167, plain, (![B_23, A_24, C_25]: (k4_xboole_0(k3_xboole_0(B_23, A_24), C_25)=k3_xboole_0(A_24, k4_xboole_0(B_23, C_25)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_104])).
% 1.88/1.20  tff(c_8, plain, (![A_7, B_8, C_9]: (k4_xboole_0(k3_xboole_0(A_7, B_8), C_9)=k3_xboole_0(A_7, k4_xboole_0(B_8, C_9)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.88/1.20  tff(c_173, plain, (![B_23, A_24, C_25]: (k3_xboole_0(B_23, k4_xboole_0(A_24, C_25))=k3_xboole_0(A_24, k4_xboole_0(B_23, C_25)))), inference(superposition, [status(thm), theory('equality')], [c_167, c_8])).
% 1.88/1.20  tff(c_46, plain, (![A_12, B_13]: (k4_xboole_0(A_12, k3_xboole_0(A_12, B_13))=k4_xboole_0(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.88/1.20  tff(c_58, plain, (![B_2, A_1]: (k4_xboole_0(B_2, k3_xboole_0(A_1, B_2))=k4_xboole_0(B_2, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_46])).
% 1.88/1.20  tff(c_10, plain, (k4_xboole_0(k3_xboole_0('#skF_1', '#skF_2'), k3_xboole_0('#skF_3', '#skF_2'))!=k3_xboole_0(k4_xboole_0('#skF_1', '#skF_3'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.88/1.20  tff(c_11, plain, (k3_xboole_0('#skF_1', k4_xboole_0('#skF_2', k3_xboole_0('#skF_3', '#skF_2')))!=k3_xboole_0(k4_xboole_0('#skF_1', '#skF_3'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_8, c_10])).
% 1.88/1.20  tff(c_12, plain, (k3_xboole_0('#skF_1', k4_xboole_0('#skF_2', k3_xboole_0('#skF_3', '#skF_2')))!=k3_xboole_0('#skF_2', k4_xboole_0('#skF_1', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_11])).
% 1.88/1.20  tff(c_210, plain, (k3_xboole_0('#skF_2', k4_xboole_0('#skF_1', '#skF_3'))!=k3_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_12])).
% 1.88/1.20  tff(c_214, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_173, c_210])).
% 1.88/1.20  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.88/1.20  
% 1.88/1.20  Inference rules
% 1.88/1.20  ----------------------
% 1.88/1.20  #Ref     : 0
% 1.88/1.20  #Sup     : 46
% 1.88/1.20  #Fact    : 0
% 1.88/1.20  #Define  : 0
% 1.88/1.20  #Split   : 0
% 1.88/1.20  #Chain   : 0
% 1.88/1.20  #Close   : 0
% 1.88/1.20  
% 1.88/1.20  Ordering : KBO
% 1.88/1.20  
% 1.88/1.20  Simplification rules
% 1.88/1.20  ----------------------
% 1.88/1.20  #Subsume      : 0
% 1.88/1.20  #Demod        : 21
% 1.88/1.20  #Tautology    : 33
% 1.88/1.20  #SimpNegUnit  : 0
% 1.88/1.20  #BackRed      : 1
% 1.88/1.20  
% 1.88/1.20  #Partial instantiations: 0
% 1.88/1.20  #Strategies tried      : 1
% 1.88/1.20  
% 1.88/1.20  Timing (in seconds)
% 1.88/1.20  ----------------------
% 1.88/1.20  Preprocessing        : 0.27
% 1.88/1.20  Parsing              : 0.14
% 1.88/1.20  CNF conversion       : 0.01
% 1.88/1.20  Main loop            : 0.15
% 1.88/1.20  Inferencing          : 0.05
% 1.88/1.20  Reduction            : 0.06
% 1.88/1.20  Demodulation         : 0.05
% 1.88/1.20  BG Simplification    : 0.01
% 1.88/1.20  Subsumption          : 0.02
% 1.88/1.20  Abstraction          : 0.01
% 1.88/1.20  MUC search           : 0.00
% 1.88/1.20  Cooper               : 0.00
% 1.88/1.20  Total                : 0.44
% 1.88/1.20  Index Insertion      : 0.00
% 1.88/1.20  Index Deletion       : 0.00
% 1.88/1.20  Index Matching       : 0.00
% 1.88/1.20  BG Taut test         : 0.00
%------------------------------------------------------------------------------

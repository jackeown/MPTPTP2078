%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:45:35 EST 2020

% Result     : Theorem 1.64s
% Output     : CNFRefutation 1.98s
% Verified   : 
% Statistics : Number of formulae       :   22 (  27 expanded)
%              Number of leaves         :   11 (  14 expanded)
%              Depth                    :    5
%              Number of atoms          :   15 (  20 expanded)
%              Number of equality atoms :   14 (  19 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k3_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

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

tff(f_29,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_31,axiom,(
    ! [A,B,C] : k3_xboole_0(k3_xboole_0(A,B),C) = k3_xboole_0(A,k3_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_34,negated_conjecture,(
    ~ ! [A,B,C] : k3_xboole_0(A,k3_xboole_0(B,C)) = k3_xboole_0(k3_xboole_0(A,B),k3_xboole_0(A,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t116_xboole_1)).

tff(c_4,plain,(
    ! [A_3] : k3_xboole_0(A_3,A_3) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_53,plain,(
    ! [A_11,B_12,C_13] : k3_xboole_0(k3_xboole_0(A_11,B_12),C_13) = k3_xboole_0(A_11,k3_xboole_0(B_12,C_13)) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_92,plain,(
    ! [A_3,C_13] : k3_xboole_0(A_3,k3_xboole_0(A_3,C_13)) = k3_xboole_0(A_3,C_13) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_53])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_62,plain,(
    ! [C_13,A_11,B_12] : k3_xboole_0(C_13,k3_xboole_0(A_11,B_12)) = k3_xboole_0(A_11,k3_xboole_0(B_12,C_13)) ),
    inference(superposition,[status(thm),theory(equality)],[c_53,c_2])).

tff(c_6,plain,(
    ! [A_5,B_6,C_7] : k3_xboole_0(k3_xboole_0(A_5,B_6),C_7) = k3_xboole_0(A_5,k3_xboole_0(B_6,C_7)) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_8,plain,(
    k3_xboole_0(k3_xboole_0('#skF_1','#skF_2'),k3_xboole_0('#skF_1','#skF_3')) != k3_xboole_0('#skF_1',k3_xboole_0('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_9,plain,(
    k3_xboole_0('#skF_1',k3_xboole_0('#skF_2',k3_xboole_0('#skF_1','#skF_3'))) != k3_xboole_0('#skF_1',k3_xboole_0('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_8])).

tff(c_10,plain,(
    k3_xboole_0('#skF_1',k3_xboole_0('#skF_2',k3_xboole_0('#skF_1','#skF_3'))) != k3_xboole_0('#skF_1',k3_xboole_0('#skF_3','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_9])).

tff(c_211,plain,(
    k3_xboole_0('#skF_1',k3_xboole_0('#skF_1',k3_xboole_0('#skF_3','#skF_2'))) != k3_xboole_0('#skF_1',k3_xboole_0('#skF_3','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_10])).

tff(c_214,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_211])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n021.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 10:57:19 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.64/1.17  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.64/1.17  
% 1.64/1.17  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.64/1.18  %$ k3_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1
% 1.64/1.18  
% 1.64/1.18  %Foreground sorts:
% 1.64/1.18  
% 1.64/1.18  
% 1.64/1.18  %Background operators:
% 1.64/1.18  
% 1.64/1.18  
% 1.64/1.18  %Foreground operators:
% 1.64/1.18  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.64/1.18  tff('#skF_2', type, '#skF_2': $i).
% 1.64/1.18  tff('#skF_3', type, '#skF_3': $i).
% 1.64/1.18  tff('#skF_1', type, '#skF_1': $i).
% 1.64/1.18  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.64/1.18  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.64/1.18  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.64/1.18  
% 1.98/1.19  tff(f_29, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 1.98/1.19  tff(f_31, axiom, (![A, B, C]: (k3_xboole_0(k3_xboole_0(A, B), C) = k3_xboole_0(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t16_xboole_1)).
% 1.98/1.19  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 1.98/1.19  tff(f_34, negated_conjecture, ~(![A, B, C]: (k3_xboole_0(A, k3_xboole_0(B, C)) = k3_xboole_0(k3_xboole_0(A, B), k3_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t116_xboole_1)).
% 1.98/1.19  tff(c_4, plain, (![A_3]: (k3_xboole_0(A_3, A_3)=A_3)), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.98/1.19  tff(c_53, plain, (![A_11, B_12, C_13]: (k3_xboole_0(k3_xboole_0(A_11, B_12), C_13)=k3_xboole_0(A_11, k3_xboole_0(B_12, C_13)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.98/1.19  tff(c_92, plain, (![A_3, C_13]: (k3_xboole_0(A_3, k3_xboole_0(A_3, C_13))=k3_xboole_0(A_3, C_13))), inference(superposition, [status(thm), theory('equality')], [c_4, c_53])).
% 1.98/1.19  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.98/1.19  tff(c_62, plain, (![C_13, A_11, B_12]: (k3_xboole_0(C_13, k3_xboole_0(A_11, B_12))=k3_xboole_0(A_11, k3_xboole_0(B_12, C_13)))), inference(superposition, [status(thm), theory('equality')], [c_53, c_2])).
% 1.98/1.19  tff(c_6, plain, (![A_5, B_6, C_7]: (k3_xboole_0(k3_xboole_0(A_5, B_6), C_7)=k3_xboole_0(A_5, k3_xboole_0(B_6, C_7)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.98/1.19  tff(c_8, plain, (k3_xboole_0(k3_xboole_0('#skF_1', '#skF_2'), k3_xboole_0('#skF_1', '#skF_3'))!=k3_xboole_0('#skF_1', k3_xboole_0('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.98/1.19  tff(c_9, plain, (k3_xboole_0('#skF_1', k3_xboole_0('#skF_2', k3_xboole_0('#skF_1', '#skF_3')))!=k3_xboole_0('#skF_1', k3_xboole_0('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_8])).
% 1.98/1.19  tff(c_10, plain, (k3_xboole_0('#skF_1', k3_xboole_0('#skF_2', k3_xboole_0('#skF_1', '#skF_3')))!=k3_xboole_0('#skF_1', k3_xboole_0('#skF_3', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_9])).
% 1.98/1.19  tff(c_211, plain, (k3_xboole_0('#skF_1', k3_xboole_0('#skF_1', k3_xboole_0('#skF_3', '#skF_2')))!=k3_xboole_0('#skF_1', k3_xboole_0('#skF_3', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_10])).
% 1.98/1.19  tff(c_214, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_92, c_211])).
% 1.98/1.19  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.98/1.19  
% 1.98/1.19  Inference rules
% 1.98/1.19  ----------------------
% 1.98/1.19  #Ref     : 0
% 1.98/1.19  #Sup     : 49
% 1.98/1.19  #Fact    : 0
% 1.98/1.19  #Define  : 0
% 1.98/1.19  #Split   : 0
% 1.98/1.19  #Chain   : 0
% 1.98/1.19  #Close   : 0
% 1.98/1.19  
% 1.98/1.19  Ordering : KBO
% 1.98/1.19  
% 1.98/1.19  Simplification rules
% 1.98/1.19  ----------------------
% 1.98/1.19  #Subsume      : 0
% 1.98/1.19  #Demod        : 46
% 1.98/1.19  #Tautology    : 30
% 1.98/1.19  #SimpNegUnit  : 0
% 1.98/1.19  #BackRed      : 1
% 1.98/1.19  
% 1.98/1.19  #Partial instantiations: 0
% 1.98/1.19  #Strategies tried      : 1
% 1.98/1.19  
% 1.98/1.19  Timing (in seconds)
% 1.98/1.19  ----------------------
% 1.98/1.19  Preprocessing        : 0.25
% 1.98/1.19  Parsing              : 0.14
% 1.98/1.19  CNF conversion       : 0.01
% 1.98/1.19  Main loop            : 0.18
% 1.98/1.19  Inferencing          : 0.06
% 1.98/1.19  Reduction            : 0.09
% 1.98/1.19  Demodulation         : 0.08
% 1.98/1.19  BG Simplification    : 0.01
% 1.98/1.19  Subsumption          : 0.02
% 1.98/1.19  Abstraction          : 0.01
% 1.98/1.19  MUC search           : 0.00
% 1.98/1.19  Cooper               : 0.00
% 1.98/1.19  Total                : 0.45
% 1.98/1.19  Index Insertion      : 0.00
% 1.98/1.19  Index Deletion       : 0.00
% 1.98/1.19  Index Matching       : 0.00
% 1.98/1.19  BG Taut test         : 0.00
%------------------------------------------------------------------------------

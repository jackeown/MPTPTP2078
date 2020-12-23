%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:42:29 EST 2020

% Result     : Theorem 1.88s
% Output     : CNFRefutation 1.88s
% Verified   : 
% Statistics : Number of formulae       :   20 (  25 expanded)
%              Number of leaves         :   11 (  14 expanded)
%              Depth                    :    4
%              Number of atoms          :   13 (  18 expanded)
%              Number of equality atoms :   12 (  17 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k2_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_29,axiom,(
    ! [A,B] : k2_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

tff(f_31,axiom,(
    ! [A,B,C] : k2_xboole_0(k2_xboole_0(A,B),C) = k2_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_34,negated_conjecture,(
    ~ ! [A,B,C] : k2_xboole_0(k2_xboole_0(A,B),C) = k2_xboole_0(k2_xboole_0(A,C),k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_xboole_1)).

tff(c_4,plain,(
    ! [A_3] : k2_xboole_0(A_3,A_3) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_53,plain,(
    ! [A_11,B_12,C_13] : k2_xboole_0(k2_xboole_0(A_11,B_12),C_13) = k2_xboole_0(A_11,k2_xboole_0(B_12,C_13)) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_92,plain,(
    ! [A_3,C_13] : k2_xboole_0(A_3,k2_xboole_0(A_3,C_13)) = k2_xboole_0(A_3,C_13) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_53])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_6,plain,(
    ! [A_5,B_6,C_7] : k2_xboole_0(k2_xboole_0(A_5,B_6),C_7) = k2_xboole_0(A_5,k2_xboole_0(B_6,C_7)) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_8,plain,(
    k2_xboole_0(k2_xboole_0('#skF_1','#skF_3'),k2_xboole_0('#skF_2','#skF_3')) != k2_xboole_0(k2_xboole_0('#skF_1','#skF_2'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_9,plain,(
    k2_xboole_0('#skF_1',k2_xboole_0('#skF_3',k2_xboole_0('#skF_2','#skF_3'))) != k2_xboole_0('#skF_1',k2_xboole_0('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_6,c_8])).

tff(c_10,plain,(
    k2_xboole_0('#skF_1',k2_xboole_0('#skF_3',k2_xboole_0('#skF_3','#skF_2'))) != k2_xboole_0('#skF_1',k2_xboole_0('#skF_3','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_2,c_9])).

tff(c_211,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_10])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 10:42:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.88/1.25  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.88/1.26  
% 1.88/1.26  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.88/1.26  %$ k2_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1
% 1.88/1.26  
% 1.88/1.26  %Foreground sorts:
% 1.88/1.26  
% 1.88/1.26  
% 1.88/1.26  %Background operators:
% 1.88/1.26  
% 1.88/1.26  
% 1.88/1.26  %Foreground operators:
% 1.88/1.26  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.88/1.26  tff('#skF_2', type, '#skF_2': $i).
% 1.88/1.26  tff('#skF_3', type, '#skF_3': $i).
% 1.88/1.26  tff('#skF_1', type, '#skF_1': $i).
% 1.88/1.26  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.88/1.26  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.88/1.26  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.88/1.26  
% 1.88/1.27  tff(f_29, axiom, (![A, B]: (k2_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 1.88/1.27  tff(f_31, axiom, (![A, B, C]: (k2_xboole_0(k2_xboole_0(A, B), C) = k2_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_1)).
% 1.88/1.27  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 1.88/1.27  tff(f_34, negated_conjecture, ~(![A, B, C]: (k2_xboole_0(k2_xboole_0(A, B), C) = k2_xboole_0(k2_xboole_0(A, C), k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_xboole_1)).
% 1.88/1.27  tff(c_4, plain, (![A_3]: (k2_xboole_0(A_3, A_3)=A_3)), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.88/1.27  tff(c_53, plain, (![A_11, B_12, C_13]: (k2_xboole_0(k2_xboole_0(A_11, B_12), C_13)=k2_xboole_0(A_11, k2_xboole_0(B_12, C_13)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.88/1.27  tff(c_92, plain, (![A_3, C_13]: (k2_xboole_0(A_3, k2_xboole_0(A_3, C_13))=k2_xboole_0(A_3, C_13))), inference(superposition, [status(thm), theory('equality')], [c_4, c_53])).
% 1.88/1.27  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.88/1.27  tff(c_6, plain, (![A_5, B_6, C_7]: (k2_xboole_0(k2_xboole_0(A_5, B_6), C_7)=k2_xboole_0(A_5, k2_xboole_0(B_6, C_7)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.88/1.27  tff(c_8, plain, (k2_xboole_0(k2_xboole_0('#skF_1', '#skF_3'), k2_xboole_0('#skF_2', '#skF_3'))!=k2_xboole_0(k2_xboole_0('#skF_1', '#skF_2'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.88/1.27  tff(c_9, plain, (k2_xboole_0('#skF_1', k2_xboole_0('#skF_3', k2_xboole_0('#skF_2', '#skF_3')))!=k2_xboole_0('#skF_1', k2_xboole_0('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_6, c_8])).
% 1.88/1.27  tff(c_10, plain, (k2_xboole_0('#skF_1', k2_xboole_0('#skF_3', k2_xboole_0('#skF_3', '#skF_2')))!=k2_xboole_0('#skF_1', k2_xboole_0('#skF_3', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_2, c_9])).
% 1.88/1.27  tff(c_211, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_92, c_10])).
% 1.88/1.27  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.88/1.27  
% 1.88/1.27  Inference rules
% 1.88/1.27  ----------------------
% 1.88/1.27  #Ref     : 0
% 1.88/1.27  #Sup     : 49
% 1.88/1.27  #Fact    : 0
% 1.88/1.27  #Define  : 0
% 1.88/1.27  #Split   : 0
% 1.88/1.27  #Chain   : 0
% 1.88/1.27  #Close   : 0
% 1.88/1.27  
% 1.88/1.27  Ordering : KBO
% 1.88/1.27  
% 1.88/1.27  Simplification rules
% 1.88/1.27  ----------------------
% 1.88/1.27  #Subsume      : 0
% 1.88/1.27  #Demod        : 46
% 1.88/1.27  #Tautology    : 29
% 1.88/1.27  #SimpNegUnit  : 0
% 1.88/1.27  #BackRed      : 0
% 1.88/1.27  
% 1.88/1.27  #Partial instantiations: 0
% 1.88/1.27  #Strategies tried      : 1
% 1.88/1.27  
% 1.88/1.27  Timing (in seconds)
% 1.88/1.27  ----------------------
% 1.88/1.27  Preprocessing        : 0.26
% 1.88/1.27  Parsing              : 0.14
% 1.88/1.27  CNF conversion       : 0.02
% 1.88/1.27  Main loop            : 0.18
% 1.88/1.27  Inferencing          : 0.05
% 1.88/1.27  Reduction            : 0.09
% 1.88/1.27  Demodulation         : 0.08
% 1.88/1.27  BG Simplification    : 0.01
% 1.88/1.27  Subsumption          : 0.02
% 1.88/1.27  Abstraction          : 0.01
% 1.88/1.27  MUC search           : 0.00
% 1.88/1.27  Cooper               : 0.00
% 1.88/1.27  Total                : 0.46
% 1.88/1.27  Index Insertion      : 0.00
% 1.88/1.27  Index Deletion       : 0.00
% 1.88/1.27  Index Matching       : 0.00
% 1.88/1.27  BG Taut test         : 0.00
%------------------------------------------------------------------------------

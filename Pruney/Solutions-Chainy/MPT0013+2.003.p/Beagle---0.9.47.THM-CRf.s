%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:42:29 EST 2020

% Result     : Theorem 1.76s
% Output     : CNFRefutation 1.76s
% Verified   : 
% Statistics : Number of formulae       :   14 (  14 expanded)
%              Number of leaves         :    9 (   9 expanded)
%              Depth                    :    3
%              Number of atoms          :    8 (   8 expanded)
%              Number of equality atoms :    7 (   7 expanded)
%              Maximal formula depth    :    4 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k2_xboole_0 > #nlpp > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

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
    ! [A,B] : k2_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

tff(f_29,axiom,(
    ! [A,B,C] : k2_xboole_0(k2_xboole_0(A,B),C) = k2_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).

tff(f_32,negated_conjecture,(
    ~ ! [A,B] : k2_xboole_0(A,k2_xboole_0(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_xboole_1)).

tff(c_2,plain,(
    ! [A_1] : k2_xboole_0(A_1,A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_16,plain,(
    ! [A_7,B_8,C_9] : k2_xboole_0(k2_xboole_0(A_7,B_8),C_9) = k2_xboole_0(A_7,k2_xboole_0(B_8,C_9)) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_35,plain,(
    ! [A_1,C_9] : k2_xboole_0(A_1,k2_xboole_0(A_1,C_9)) = k2_xboole_0(A_1,C_9) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_16])).

tff(c_6,plain,(
    k2_xboole_0('#skF_1',k2_xboole_0('#skF_1','#skF_2')) != k2_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_46,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_35,c_6])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.33  % Computer   : n022.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.33  % CPULimit   : 60
% 0.14/0.33  % DateTime   : Tue Dec  1 15:23:56 EST 2020
% 0.14/0.33  % CPUTime    : 
% 0.14/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.76/1.36  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.76/1.36  
% 1.76/1.36  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.76/1.38  %$ k2_xboole_0 > #nlpp > #skF_2 > #skF_1
% 1.76/1.38  
% 1.76/1.38  %Foreground sorts:
% 1.76/1.38  
% 1.76/1.38  
% 1.76/1.38  %Background operators:
% 1.76/1.38  
% 1.76/1.38  
% 1.76/1.38  %Foreground operators:
% 1.76/1.38  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.76/1.38  tff('#skF_2', type, '#skF_2': $i).
% 1.76/1.38  tff('#skF_1', type, '#skF_1': $i).
% 1.76/1.38  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.76/1.38  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.76/1.38  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.76/1.38  
% 1.76/1.39  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 1.76/1.39  tff(f_29, axiom, (![A, B, C]: (k2_xboole_0(k2_xboole_0(A, B), C) = k2_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_1)).
% 1.76/1.39  tff(f_32, negated_conjecture, ~(![A, B]: (k2_xboole_0(A, k2_xboole_0(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_xboole_1)).
% 1.76/1.39  tff(c_2, plain, (![A_1]: (k2_xboole_0(A_1, A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.76/1.39  tff(c_16, plain, (![A_7, B_8, C_9]: (k2_xboole_0(k2_xboole_0(A_7, B_8), C_9)=k2_xboole_0(A_7, k2_xboole_0(B_8, C_9)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.76/1.39  tff(c_35, plain, (![A_1, C_9]: (k2_xboole_0(A_1, k2_xboole_0(A_1, C_9))=k2_xboole_0(A_1, C_9))), inference(superposition, [status(thm), theory('equality')], [c_2, c_16])).
% 1.76/1.39  tff(c_6, plain, (k2_xboole_0('#skF_1', k2_xboole_0('#skF_1', '#skF_2'))!=k2_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.76/1.39  tff(c_46, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_35, c_6])).
% 1.76/1.39  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.76/1.39  
% 1.76/1.39  Inference rules
% 1.76/1.39  ----------------------
% 1.76/1.39  #Ref     : 0
% 1.76/1.39  #Sup     : 9
% 1.76/1.39  #Fact    : 0
% 1.76/1.39  #Define  : 0
% 1.76/1.39  #Split   : 0
% 1.76/1.39  #Chain   : 0
% 1.76/1.39  #Close   : 0
% 1.76/1.39  
% 1.76/1.39  Ordering : KBO
% 1.76/1.39  
% 1.76/1.39  Simplification rules
% 1.76/1.39  ----------------------
% 1.76/1.39  #Subsume      : 0
% 1.76/1.39  #Demod        : 7
% 1.76/1.39  #Tautology    : 6
% 1.76/1.39  #SimpNegUnit  : 0
% 1.76/1.39  #BackRed      : 1
% 1.76/1.39  
% 1.76/1.39  #Partial instantiations: 0
% 1.76/1.39  #Strategies tried      : 1
% 1.76/1.39  
% 1.76/1.39  Timing (in seconds)
% 1.76/1.39  ----------------------
% 1.76/1.39  Preprocessing        : 0.36
% 1.76/1.39  Parsing              : 0.19
% 1.87/1.39  CNF conversion       : 0.02
% 1.87/1.39  Main loop            : 0.12
% 1.87/1.39  Inferencing          : 0.05
% 1.87/1.39  Reduction            : 0.04
% 1.87/1.39  Demodulation         : 0.04
% 1.87/1.39  BG Simplification    : 0.01
% 1.87/1.39  Subsumption          : 0.02
% 1.87/1.40  Abstraction          : 0.01
% 1.87/1.40  MUC search           : 0.00
% 1.87/1.40  Cooper               : 0.00
% 1.87/1.40  Total                : 0.53
% 1.87/1.40  Index Insertion      : 0.00
% 1.87/1.40  Index Deletion       : 0.00
% 1.87/1.40  Index Matching       : 0.00
% 1.87/1.40  BG Taut test         : 0.00
%------------------------------------------------------------------------------

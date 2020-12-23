%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:44:48 EST 2020

% Result     : Theorem 3.81s
% Output     : CNFRefutation 3.81s
% Verified   : 
% Statistics : Number of formulae       :   25 (  29 expanded)
%              Number of leaves         :   14 (  16 expanded)
%              Depth                    :    6
%              Number of atoms          :   17 (  21 expanded)
%              Number of equality atoms :   16 (  20 expanded)
%              Maximal formula depth    :    4 (   3 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > #nlpp > #skF_2 > #skF_1

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

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_33,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_31,axiom,(
    ! [A,B] : k2_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

tff(f_35,axiom,(
    ! [A,B,C] : k4_xboole_0(k4_xboole_0(A,B),C) = k4_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k2_xboole_0(k4_xboole_0(A,B),k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_xboole_0)).

tff(f_38,negated_conjecture,(
    ~ ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

tff(c_8,plain,(
    ! [A_7,B_8] : k2_xboole_0(A_7,k4_xboole_0(B_8,A_7)) = k2_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_6,plain,(
    ! [A_5] : k2_xboole_0(A_5,A_5) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_10,plain,(
    ! [A_9,B_10,C_11] : k4_xboole_0(k4_xboole_0(A_9,B_10),C_11) = k4_xboole_0(A_9,k2_xboole_0(B_10,C_11)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_84,plain,(
    ! [A_20,B_21] : k2_xboole_0(k4_xboole_0(A_20,B_21),k4_xboole_0(B_21,A_20)) = k5_xboole_0(A_20,B_21) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_1467,plain,(
    ! [C_64,A_65,B_66] : k2_xboole_0(k4_xboole_0(C_64,k4_xboole_0(A_65,B_66)),k4_xboole_0(A_65,k2_xboole_0(B_66,C_64))) = k5_xboole_0(C_64,k4_xboole_0(A_65,B_66)) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_84])).

tff(c_1640,plain,(
    ! [A_67,A_68] : k2_xboole_0(k4_xboole_0(A_67,k4_xboole_0(A_68,A_67)),k4_xboole_0(A_68,A_67)) = k5_xboole_0(A_67,k4_xboole_0(A_68,A_67)) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_1467])).

tff(c_1682,plain,(
    ! [A_68,A_67] : k2_xboole_0(k4_xboole_0(A_68,A_67),k4_xboole_0(A_67,k4_xboole_0(A_68,A_67))) = k5_xboole_0(A_67,k4_xboole_0(A_68,A_67)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1640,c_2])).

tff(c_1759,plain,(
    ! [A_67,A_68] : k5_xboole_0(A_67,k4_xboole_0(A_68,A_67)) = k2_xboole_0(A_67,A_68) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_2,c_8,c_1682])).

tff(c_12,plain,(
    k5_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_1')) != k2_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_1776,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1759,c_12])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.33  % Computer   : n001.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.33  % CPULimit   : 60
% 0.14/0.33  % DateTime   : Tue Dec  1 17:46:45 EST 2020
% 0.14/0.33  % CPUTime    : 
% 0.14/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.81/1.66  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.81/1.66  
% 3.81/1.66  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.81/1.66  %$ k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > #nlpp > #skF_2 > #skF_1
% 3.81/1.66  
% 3.81/1.66  %Foreground sorts:
% 3.81/1.66  
% 3.81/1.66  
% 3.81/1.66  %Background operators:
% 3.81/1.66  
% 3.81/1.66  
% 3.81/1.66  %Foreground operators:
% 3.81/1.66  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.81/1.66  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.81/1.66  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.81/1.66  tff('#skF_2', type, '#skF_2': $i).
% 3.81/1.66  tff('#skF_1', type, '#skF_1': $i).
% 3.81/1.66  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.81/1.66  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.81/1.66  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.81/1.66  
% 3.81/1.67  tff(f_33, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 3.81/1.67  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 3.81/1.67  tff(f_31, axiom, (![A, B]: (k2_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 3.81/1.67  tff(f_35, axiom, (![A, B, C]: (k4_xboole_0(k4_xboole_0(A, B), C) = k4_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_xboole_1)).
% 3.81/1.67  tff(f_29, axiom, (![A, B]: (k5_xboole_0(A, B) = k2_xboole_0(k4_xboole_0(A, B), k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d6_xboole_0)).
% 3.81/1.67  tff(f_38, negated_conjecture, ~(![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 3.81/1.67  tff(c_8, plain, (![A_7, B_8]: (k2_xboole_0(A_7, k4_xboole_0(B_8, A_7))=k2_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.81/1.67  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.81/1.67  tff(c_6, plain, (![A_5]: (k2_xboole_0(A_5, A_5)=A_5)), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.81/1.67  tff(c_10, plain, (![A_9, B_10, C_11]: (k4_xboole_0(k4_xboole_0(A_9, B_10), C_11)=k4_xboole_0(A_9, k2_xboole_0(B_10, C_11)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.81/1.67  tff(c_84, plain, (![A_20, B_21]: (k2_xboole_0(k4_xboole_0(A_20, B_21), k4_xboole_0(B_21, A_20))=k5_xboole_0(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.81/1.67  tff(c_1467, plain, (![C_64, A_65, B_66]: (k2_xboole_0(k4_xboole_0(C_64, k4_xboole_0(A_65, B_66)), k4_xboole_0(A_65, k2_xboole_0(B_66, C_64)))=k5_xboole_0(C_64, k4_xboole_0(A_65, B_66)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_84])).
% 3.81/1.67  tff(c_1640, plain, (![A_67, A_68]: (k2_xboole_0(k4_xboole_0(A_67, k4_xboole_0(A_68, A_67)), k4_xboole_0(A_68, A_67))=k5_xboole_0(A_67, k4_xboole_0(A_68, A_67)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_1467])).
% 3.81/1.67  tff(c_1682, plain, (![A_68, A_67]: (k2_xboole_0(k4_xboole_0(A_68, A_67), k4_xboole_0(A_67, k4_xboole_0(A_68, A_67)))=k5_xboole_0(A_67, k4_xboole_0(A_68, A_67)))), inference(superposition, [status(thm), theory('equality')], [c_1640, c_2])).
% 3.81/1.67  tff(c_1759, plain, (![A_67, A_68]: (k5_xboole_0(A_67, k4_xboole_0(A_68, A_67))=k2_xboole_0(A_67, A_68))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_2, c_8, c_1682])).
% 3.81/1.67  tff(c_12, plain, (k5_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_1'))!=k2_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.81/1.67  tff(c_1776, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1759, c_12])).
% 3.81/1.67  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.81/1.67  
% 3.81/1.67  Inference rules
% 3.81/1.67  ----------------------
% 3.81/1.67  #Ref     : 0
% 3.81/1.67  #Sup     : 462
% 3.81/1.67  #Fact    : 0
% 3.81/1.67  #Define  : 0
% 3.81/1.67  #Split   : 0
% 3.81/1.67  #Chain   : 0
% 3.81/1.67  #Close   : 0
% 3.81/1.67  
% 3.81/1.67  Ordering : KBO
% 3.81/1.67  
% 3.81/1.67  Simplification rules
% 3.81/1.67  ----------------------
% 3.81/1.67  #Subsume      : 3
% 3.81/1.67  #Demod        : 427
% 3.81/1.67  #Tautology    : 161
% 3.81/1.67  #SimpNegUnit  : 0
% 3.81/1.67  #BackRed      : 2
% 3.81/1.67  
% 3.81/1.67  #Partial instantiations: 0
% 3.81/1.67  #Strategies tried      : 1
% 3.81/1.67  
% 3.81/1.67  Timing (in seconds)
% 3.81/1.67  ----------------------
% 3.81/1.67  Preprocessing        : 0.25
% 3.81/1.67  Parsing              : 0.14
% 3.81/1.67  CNF conversion       : 0.01
% 3.81/1.67  Main loop            : 0.65
% 3.81/1.67  Inferencing          : 0.18
% 3.81/1.67  Reduction            : 0.33
% 3.81/1.67  Demodulation         : 0.30
% 3.81/1.67  BG Simplification    : 0.03
% 3.81/1.67  Subsumption          : 0.07
% 3.81/1.67  Abstraction          : 0.04
% 3.81/1.67  MUC search           : 0.00
% 3.81/1.67  Cooper               : 0.00
% 3.81/1.67  Total                : 0.92
% 3.81/1.67  Index Insertion      : 0.00
% 3.81/1.67  Index Deletion       : 0.00
% 3.81/1.68  Index Matching       : 0.00
% 3.81/1.68  BG Taut test         : 0.00
%------------------------------------------------------------------------------

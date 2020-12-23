%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:44:52 EST 2020

% Result     : Theorem 4.80s
% Output     : CNFRefutation 4.80s
% Verified   : 
% Statistics : Number of formulae       :   21 (  23 expanded)
%              Number of leaves         :   13 (  14 expanded)
%              Depth                    :    5
%              Number of atoms          :   12 (  14 expanded)
%              Number of equality atoms :   11 (  13 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_27,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k2_xboole_0(k4_xboole_0(A,B),k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_xboole_0)).

tff(f_29,axiom,(
    ! [A,B,C] : k4_xboole_0(k4_xboole_0(A,B),C) = k4_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

tff(f_31,axiom,(
    ! [A,B,C] : k4_xboole_0(k2_xboole_0(A,B),C) = k2_xboole_0(k4_xboole_0(A,C),k4_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_xboole_1)).

tff(f_34,negated_conjecture,(
    ~ ! [A,B,C] : k4_xboole_0(k5_xboole_0(A,B),C) = k2_xboole_0(k4_xboole_0(A,k2_xboole_0(B,C)),k4_xboole_0(B,k2_xboole_0(A,C))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t99_xboole_1)).

tff(c_2,plain,(
    ! [A_1,B_2] : k2_xboole_0(k4_xboole_0(A_1,B_2),k4_xboole_0(B_2,A_1)) = k5_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4,plain,(
    ! [A_3,B_4,C_5] : k4_xboole_0(k4_xboole_0(A_3,B_4),C_5) = k4_xboole_0(A_3,k2_xboole_0(B_4,C_5)) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_41,plain,(
    ! [A_14,C_15,B_16] : k2_xboole_0(k4_xboole_0(A_14,C_15),k4_xboole_0(B_16,C_15)) = k4_xboole_0(k2_xboole_0(A_14,B_16),C_15) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_518,plain,(
    ! [A_34,B_35,C_36,B_37] : k2_xboole_0(k4_xboole_0(A_34,k2_xboole_0(B_35,C_36)),k4_xboole_0(B_37,C_36)) = k4_xboole_0(k2_xboole_0(k4_xboole_0(A_34,B_35),B_37),C_36) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_41])).

tff(c_610,plain,(
    ! [A_3,A_34,B_35,C_5,B_4] : k2_xboole_0(k4_xboole_0(A_34,k2_xboole_0(B_35,C_5)),k4_xboole_0(A_3,k2_xboole_0(B_4,C_5))) = k4_xboole_0(k2_xboole_0(k4_xboole_0(A_34,B_35),k4_xboole_0(A_3,B_4)),C_5) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_518])).

tff(c_8,plain,(
    k2_xboole_0(k4_xboole_0('#skF_1',k2_xboole_0('#skF_2','#skF_3')),k4_xboole_0('#skF_2',k2_xboole_0('#skF_1','#skF_3'))) != k4_xboole_0(k5_xboole_0('#skF_1','#skF_2'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_2653,plain,(
    k4_xboole_0(k2_xboole_0(k4_xboole_0('#skF_1','#skF_2'),k4_xboole_0('#skF_2','#skF_1')),'#skF_3') != k4_xboole_0(k5_xboole_0('#skF_1','#skF_2'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_610,c_8])).

tff(c_2656,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_2653])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:30:53 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.80/1.90  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.80/1.90  
% 4.80/1.90  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.80/1.91  %$ k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1
% 4.80/1.91  
% 4.80/1.91  %Foreground sorts:
% 4.80/1.91  
% 4.80/1.91  
% 4.80/1.91  %Background operators:
% 4.80/1.91  
% 4.80/1.91  
% 4.80/1.91  %Foreground operators:
% 4.80/1.91  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.80/1.91  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.80/1.91  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 4.80/1.91  tff('#skF_2', type, '#skF_2': $i).
% 4.80/1.91  tff('#skF_3', type, '#skF_3': $i).
% 4.80/1.91  tff('#skF_1', type, '#skF_1': $i).
% 4.80/1.91  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.80/1.91  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.80/1.91  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.80/1.91  
% 4.80/1.91  tff(f_27, axiom, (![A, B]: (k5_xboole_0(A, B) = k2_xboole_0(k4_xboole_0(A, B), k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d6_xboole_0)).
% 4.80/1.91  tff(f_29, axiom, (![A, B, C]: (k4_xboole_0(k4_xboole_0(A, B), C) = k4_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_xboole_1)).
% 4.80/1.91  tff(f_31, axiom, (![A, B, C]: (k4_xboole_0(k2_xboole_0(A, B), C) = k2_xboole_0(k4_xboole_0(A, C), k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t42_xboole_1)).
% 4.80/1.91  tff(f_34, negated_conjecture, ~(![A, B, C]: (k4_xboole_0(k5_xboole_0(A, B), C) = k2_xboole_0(k4_xboole_0(A, k2_xboole_0(B, C)), k4_xboole_0(B, k2_xboole_0(A, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t99_xboole_1)).
% 4.80/1.91  tff(c_2, plain, (![A_1, B_2]: (k2_xboole_0(k4_xboole_0(A_1, B_2), k4_xboole_0(B_2, A_1))=k5_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.80/1.91  tff(c_4, plain, (![A_3, B_4, C_5]: (k4_xboole_0(k4_xboole_0(A_3, B_4), C_5)=k4_xboole_0(A_3, k2_xboole_0(B_4, C_5)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.80/1.91  tff(c_41, plain, (![A_14, C_15, B_16]: (k2_xboole_0(k4_xboole_0(A_14, C_15), k4_xboole_0(B_16, C_15))=k4_xboole_0(k2_xboole_0(A_14, B_16), C_15))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.80/1.91  tff(c_518, plain, (![A_34, B_35, C_36, B_37]: (k2_xboole_0(k4_xboole_0(A_34, k2_xboole_0(B_35, C_36)), k4_xboole_0(B_37, C_36))=k4_xboole_0(k2_xboole_0(k4_xboole_0(A_34, B_35), B_37), C_36))), inference(superposition, [status(thm), theory('equality')], [c_4, c_41])).
% 4.80/1.91  tff(c_610, plain, (![A_3, A_34, B_35, C_5, B_4]: (k2_xboole_0(k4_xboole_0(A_34, k2_xboole_0(B_35, C_5)), k4_xboole_0(A_3, k2_xboole_0(B_4, C_5)))=k4_xboole_0(k2_xboole_0(k4_xboole_0(A_34, B_35), k4_xboole_0(A_3, B_4)), C_5))), inference(superposition, [status(thm), theory('equality')], [c_4, c_518])).
% 4.80/1.91  tff(c_8, plain, (k2_xboole_0(k4_xboole_0('#skF_1', k2_xboole_0('#skF_2', '#skF_3')), k4_xboole_0('#skF_2', k2_xboole_0('#skF_1', '#skF_3')))!=k4_xboole_0(k5_xboole_0('#skF_1', '#skF_2'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_34])).
% 4.80/1.91  tff(c_2653, plain, (k4_xboole_0(k2_xboole_0(k4_xboole_0('#skF_1', '#skF_2'), k4_xboole_0('#skF_2', '#skF_1')), '#skF_3')!=k4_xboole_0(k5_xboole_0('#skF_1', '#skF_2'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_610, c_8])).
% 4.80/1.91  tff(c_2656, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2, c_2653])).
% 4.80/1.91  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.80/1.91  
% 4.80/1.91  Inference rules
% 4.80/1.91  ----------------------
% 4.80/1.91  #Ref     : 0
% 4.80/1.91  #Sup     : 682
% 4.80/1.91  #Fact    : 0
% 4.80/1.91  #Define  : 0
% 4.80/1.91  #Split   : 0
% 4.80/1.91  #Chain   : 0
% 4.80/1.91  #Close   : 0
% 4.80/1.91  
% 4.80/1.91  Ordering : KBO
% 4.80/1.91  
% 4.80/1.91  Simplification rules
% 4.80/1.91  ----------------------
% 4.80/1.91  #Subsume      : 0
% 4.80/1.91  #Demod        : 754
% 4.80/1.91  #Tautology    : 134
% 4.80/1.91  #SimpNegUnit  : 0
% 4.80/1.91  #BackRed      : 1
% 4.80/1.91  
% 4.80/1.91  #Partial instantiations: 0
% 4.80/1.91  #Strategies tried      : 1
% 4.80/1.91  
% 4.80/1.91  Timing (in seconds)
% 4.80/1.91  ----------------------
% 4.80/1.92  Preprocessing        : 0.26
% 4.80/1.92  Parsing              : 0.15
% 4.80/1.92  CNF conversion       : 0.01
% 4.80/1.92  Main loop            : 0.88
% 4.80/1.92  Inferencing          : 0.29
% 4.80/1.92  Reduction            : 0.39
% 4.80/1.92  Demodulation         : 0.33
% 4.80/1.92  BG Simplification    : 0.06
% 4.80/1.92  Subsumption          : 0.09
% 4.80/1.92  Abstraction          : 0.09
% 4.80/1.92  MUC search           : 0.00
% 4.80/1.92  Cooper               : 0.00
% 4.80/1.92  Total                : 1.16
% 4.80/1.92  Index Insertion      : 0.00
% 4.80/1.92  Index Deletion       : 0.00
% 4.80/1.92  Index Matching       : 0.00
% 4.80/1.92  BG Taut test         : 0.00
%------------------------------------------------------------------------------

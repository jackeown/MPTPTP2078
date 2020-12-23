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
% DateTime   : Thu Dec  3 09:44:39 EST 2020

% Result     : Theorem 3.63s
% Output     : CNFRefutation 3.63s
% Verified   : 
% Statistics : Number of formulae       :   26 (  26 expanded)
%              Number of leaves         :   15 (  15 expanded)
%              Depth                    :    5
%              Number of atoms          :   17 (  17 expanded)
%              Number of equality atoms :   16 (  16 expanded)
%              Maximal formula depth    :    4 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > #skF_2 > #skF_1

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_31,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k2_xboole_0(k4_xboole_0(A,B),k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_xboole_0)).

tff(f_37,axiom,(
    ! [A,B] : k2_xboole_0(k3_xboole_0(A,B),k4_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).

tff(f_35,axiom,(
    ! [A,B,C] : k2_xboole_0(k2_xboole_0(A,B),C) = k2_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_40,negated_conjecture,(
    ~ ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(k5_xboole_0(A,B),k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t93_xboole_1)).

tff(c_6,plain,(
    ! [A_5,B_6] : k2_xboole_0(A_5,k4_xboole_0(B_6,A_5)) = k2_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_4,plain,(
    ! [A_3,B_4] : k2_xboole_0(k4_xboole_0(A_3,B_4),k4_xboole_0(B_4,A_3)) = k5_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_12,plain,(
    ! [A_12,B_13] : k2_xboole_0(k3_xboole_0(A_12,B_13),k4_xboole_0(A_12,B_13)) = A_12 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_89,plain,(
    ! [A_22,B_23,C_24] : k2_xboole_0(k2_xboole_0(A_22,B_23),C_24) = k2_xboole_0(A_22,k2_xboole_0(B_23,C_24)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_994,plain,(
    ! [A_47,B_48,C_49] : k2_xboole_0(k3_xboole_0(A_47,B_48),k2_xboole_0(k4_xboole_0(A_47,B_48),C_49)) = k2_xboole_0(A_47,C_49) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_89])).

tff(c_1067,plain,(
    ! [A_3,B_4] : k2_xboole_0(k3_xboole_0(A_3,B_4),k5_xboole_0(A_3,B_4)) = k2_xboole_0(A_3,k4_xboole_0(B_4,A_3)) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_994])).

tff(c_1096,plain,(
    ! [A_3,B_4] : k2_xboole_0(k3_xboole_0(A_3,B_4),k5_xboole_0(A_3,B_4)) = k2_xboole_0(A_3,B_4) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_1067])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_14,plain,(
    k2_xboole_0(k5_xboole_0('#skF_1','#skF_2'),k3_xboole_0('#skF_1','#skF_2')) != k2_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_15,plain,(
    k2_xboole_0(k3_xboole_0('#skF_1','#skF_2'),k5_xboole_0('#skF_1','#skF_2')) != k2_xboole_0('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_14])).

tff(c_1597,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1096,c_15])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:59:10 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.63/1.65  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.63/1.65  
% 3.63/1.65  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.63/1.65  %$ k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > #skF_2 > #skF_1
% 3.63/1.65  
% 3.63/1.65  %Foreground sorts:
% 3.63/1.65  
% 3.63/1.65  
% 3.63/1.65  %Background operators:
% 3.63/1.65  
% 3.63/1.65  
% 3.63/1.65  %Foreground operators:
% 3.63/1.65  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.63/1.65  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.63/1.65  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.63/1.65  tff('#skF_2', type, '#skF_2': $i).
% 3.63/1.65  tff('#skF_1', type, '#skF_1': $i).
% 3.63/1.65  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.63/1.65  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.63/1.65  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.63/1.65  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.63/1.65  
% 3.63/1.66  tff(f_31, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 3.63/1.66  tff(f_29, axiom, (![A, B]: (k5_xboole_0(A, B) = k2_xboole_0(k4_xboole_0(A, B), k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d6_xboole_0)).
% 3.63/1.66  tff(f_37, axiom, (![A, B]: (k2_xboole_0(k3_xboole_0(A, B), k4_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_xboole_1)).
% 3.63/1.66  tff(f_35, axiom, (![A, B, C]: (k2_xboole_0(k2_xboole_0(A, B), C) = k2_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_1)).
% 3.63/1.66  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 3.63/1.66  tff(f_40, negated_conjecture, ~(![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(k5_xboole_0(A, B), k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t93_xboole_1)).
% 3.63/1.66  tff(c_6, plain, (![A_5, B_6]: (k2_xboole_0(A_5, k4_xboole_0(B_6, A_5))=k2_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.63/1.66  tff(c_4, plain, (![A_3, B_4]: (k2_xboole_0(k4_xboole_0(A_3, B_4), k4_xboole_0(B_4, A_3))=k5_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.63/1.66  tff(c_12, plain, (![A_12, B_13]: (k2_xboole_0(k3_xboole_0(A_12, B_13), k4_xboole_0(A_12, B_13))=A_12)), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.63/1.66  tff(c_89, plain, (![A_22, B_23, C_24]: (k2_xboole_0(k2_xboole_0(A_22, B_23), C_24)=k2_xboole_0(A_22, k2_xboole_0(B_23, C_24)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.63/1.66  tff(c_994, plain, (![A_47, B_48, C_49]: (k2_xboole_0(k3_xboole_0(A_47, B_48), k2_xboole_0(k4_xboole_0(A_47, B_48), C_49))=k2_xboole_0(A_47, C_49))), inference(superposition, [status(thm), theory('equality')], [c_12, c_89])).
% 3.63/1.66  tff(c_1067, plain, (![A_3, B_4]: (k2_xboole_0(k3_xboole_0(A_3, B_4), k5_xboole_0(A_3, B_4))=k2_xboole_0(A_3, k4_xboole_0(B_4, A_3)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_994])).
% 3.63/1.66  tff(c_1096, plain, (![A_3, B_4]: (k2_xboole_0(k3_xboole_0(A_3, B_4), k5_xboole_0(A_3, B_4))=k2_xboole_0(A_3, B_4))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_1067])).
% 3.63/1.66  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.63/1.66  tff(c_14, plain, (k2_xboole_0(k5_xboole_0('#skF_1', '#skF_2'), k3_xboole_0('#skF_1', '#skF_2'))!=k2_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.63/1.66  tff(c_15, plain, (k2_xboole_0(k3_xboole_0('#skF_1', '#skF_2'), k5_xboole_0('#skF_1', '#skF_2'))!=k2_xboole_0('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_14])).
% 3.63/1.66  tff(c_1597, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1096, c_15])).
% 3.63/1.66  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.63/1.66  
% 3.63/1.66  Inference rules
% 3.63/1.66  ----------------------
% 3.63/1.66  #Ref     : 0
% 3.63/1.66  #Sup     : 427
% 3.63/1.66  #Fact    : 0
% 3.63/1.66  #Define  : 0
% 3.63/1.66  #Split   : 0
% 3.63/1.66  #Chain   : 0
% 3.63/1.66  #Close   : 0
% 3.63/1.66  
% 3.63/1.66  Ordering : KBO
% 3.63/1.66  
% 3.63/1.66  Simplification rules
% 3.63/1.66  ----------------------
% 3.63/1.66  #Subsume      : 46
% 3.63/1.66  #Demod        : 187
% 3.63/1.66  #Tautology    : 88
% 3.63/1.66  #SimpNegUnit  : 0
% 3.63/1.66  #BackRed      : 1
% 3.63/1.66  
% 3.63/1.66  #Partial instantiations: 0
% 3.63/1.66  #Strategies tried      : 1
% 3.63/1.66  
% 3.63/1.66  Timing (in seconds)
% 3.63/1.66  ----------------------
% 3.63/1.66  Preprocessing        : 0.26
% 3.63/1.66  Parsing              : 0.15
% 3.63/1.66  CNF conversion       : 0.01
% 3.63/1.66  Main loop            : 0.60
% 3.63/1.66  Inferencing          : 0.16
% 3.63/1.66  Reduction            : 0.32
% 3.63/1.66  Demodulation         : 0.30
% 3.63/1.66  BG Simplification    : 0.03
% 3.63/1.66  Subsumption          : 0.06
% 3.63/1.66  Abstraction          : 0.03
% 3.63/1.66  MUC search           : 0.00
% 3.63/1.66  Cooper               : 0.00
% 3.63/1.66  Total                : 0.88
% 3.63/1.66  Index Insertion      : 0.00
% 3.63/1.66  Index Deletion       : 0.00
% 3.63/1.66  Index Matching       : 0.00
% 3.63/1.66  BG Taut test         : 0.00
%------------------------------------------------------------------------------

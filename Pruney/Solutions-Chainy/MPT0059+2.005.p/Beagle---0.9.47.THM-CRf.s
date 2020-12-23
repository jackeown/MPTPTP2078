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
% DateTime   : Thu Dec  3 09:43:05 EST 2020

% Result     : Theorem 47.73s
% Output     : CNFRefutation 47.73s
% Verified   : 
% Statistics : Number of formulae       :   28 (  29 expanded)
%              Number of leaves         :   15 (  16 expanded)
%              Depth                    :    6
%              Number of atoms          :   19 (  20 expanded)
%              Number of equality atoms :   18 (  19 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_31,axiom,(
    ! [A,B] : k4_xboole_0(A,k3_xboole_0(A,B)) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_35,axiom,(
    ! [A,B,C] : k3_xboole_0(A,k4_xboole_0(B,C)) = k4_xboole_0(k3_xboole_0(A,B),C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_29,axiom,(
    ! [A,B,C] : k4_xboole_0(A,k3_xboole_0(B,C)) = k2_xboole_0(k4_xboole_0(A,B),k4_xboole_0(A,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l36_xboole_1)).

tff(f_38,negated_conjecture,(
    ~ ! [A,B,C] : k4_xboole_0(A,k4_xboole_0(B,C)) = k2_xboole_0(k4_xboole_0(A,B),k3_xboole_0(A,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_xboole_1)).

tff(c_6,plain,(
    ! [A_6,B_7] : k4_xboole_0(A_6,k3_xboole_0(A_6,B_7)) = k4_xboole_0(A_6,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_143,plain,(
    ! [A_23,B_24,C_25] : k4_xboole_0(k3_xboole_0(A_23,B_24),C_25) = k3_xboole_0(A_23,k4_xboole_0(B_24,C_25)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_295,plain,(
    ! [A_30,B_31,C_32] : k4_xboole_0(k3_xboole_0(A_30,B_31),C_32) = k3_xboole_0(B_31,k4_xboole_0(A_30,C_32)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_143])).

tff(c_10,plain,(
    ! [A_10,B_11,C_12] : k4_xboole_0(k3_xboole_0(A_10,B_11),C_12) = k3_xboole_0(A_10,k4_xboole_0(B_11,C_12)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_304,plain,(
    ! [B_31,A_30,C_32] : k3_xboole_0(B_31,k4_xboole_0(A_30,C_32)) = k3_xboole_0(A_30,k4_xboole_0(B_31,C_32)) ),
    inference(superposition,[status(thm),theory(equality)],[c_295,c_10])).

tff(c_8,plain,(
    ! [A_8,B_9] : k4_xboole_0(A_8,k4_xboole_0(A_8,B_9)) = k3_xboole_0(A_8,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_367,plain,(
    ! [A_33,B_34,C_35] : k2_xboole_0(k4_xboole_0(A_33,B_34),k4_xboole_0(A_33,C_35)) = k4_xboole_0(A_33,k3_xboole_0(B_34,C_35)) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_5650,plain,(
    ! [A_93,B_94,B_95] : k4_xboole_0(A_93,k3_xboole_0(B_94,k4_xboole_0(A_93,B_95))) = k2_xboole_0(k4_xboole_0(A_93,B_94),k3_xboole_0(A_93,B_95)) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_367])).

tff(c_5818,plain,(
    ! [A_30,B_31,C_32] : k4_xboole_0(A_30,k3_xboole_0(A_30,k4_xboole_0(B_31,C_32))) = k2_xboole_0(k4_xboole_0(A_30,B_31),k3_xboole_0(A_30,C_32)) ),
    inference(superposition,[status(thm),theory(equality)],[c_304,c_5650])).

tff(c_5893,plain,(
    ! [A_30,B_31,C_32] : k2_xboole_0(k4_xboole_0(A_30,B_31),k3_xboole_0(A_30,C_32)) = k4_xboole_0(A_30,k4_xboole_0(B_31,C_32)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_5818])).

tff(c_12,plain,(
    k2_xboole_0(k4_xboole_0('#skF_1','#skF_2'),k3_xboole_0('#skF_1','#skF_3')) != k4_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_101544,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5893,c_12])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n014.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 18:45:52 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 47.73/37.65  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 47.73/37.65  
% 47.73/37.65  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 47.73/37.66  %$ k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1
% 47.73/37.66  
% 47.73/37.66  %Foreground sorts:
% 47.73/37.66  
% 47.73/37.66  
% 47.73/37.66  %Background operators:
% 47.73/37.66  
% 47.73/37.66  
% 47.73/37.66  %Foreground operators:
% 47.73/37.66  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 47.73/37.66  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 47.73/37.66  tff('#skF_2', type, '#skF_2': $i).
% 47.73/37.66  tff('#skF_3', type, '#skF_3': $i).
% 47.73/37.66  tff('#skF_1', type, '#skF_1': $i).
% 47.73/37.66  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 47.73/37.66  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 47.73/37.66  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 47.73/37.66  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 47.73/37.66  
% 47.73/37.67  tff(f_31, axiom, (![A, B]: (k4_xboole_0(A, k3_xboole_0(A, B)) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_xboole_1)).
% 47.73/37.67  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 47.73/37.67  tff(f_35, axiom, (![A, B, C]: (k3_xboole_0(A, k4_xboole_0(B, C)) = k4_xboole_0(k3_xboole_0(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_xboole_1)).
% 47.73/37.67  tff(f_33, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 47.73/37.67  tff(f_29, axiom, (![A, B, C]: (k4_xboole_0(A, k3_xboole_0(B, C)) = k2_xboole_0(k4_xboole_0(A, B), k4_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l36_xboole_1)).
% 47.73/37.67  tff(f_38, negated_conjecture, ~(![A, B, C]: (k4_xboole_0(A, k4_xboole_0(B, C)) = k2_xboole_0(k4_xboole_0(A, B), k3_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_xboole_1)).
% 47.73/37.67  tff(c_6, plain, (![A_6, B_7]: (k4_xboole_0(A_6, k3_xboole_0(A_6, B_7))=k4_xboole_0(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_31])).
% 47.73/37.67  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 47.73/37.67  tff(c_143, plain, (![A_23, B_24, C_25]: (k4_xboole_0(k3_xboole_0(A_23, B_24), C_25)=k3_xboole_0(A_23, k4_xboole_0(B_24, C_25)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 47.73/37.67  tff(c_295, plain, (![A_30, B_31, C_32]: (k4_xboole_0(k3_xboole_0(A_30, B_31), C_32)=k3_xboole_0(B_31, k4_xboole_0(A_30, C_32)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_143])).
% 47.73/37.67  tff(c_10, plain, (![A_10, B_11, C_12]: (k4_xboole_0(k3_xboole_0(A_10, B_11), C_12)=k3_xboole_0(A_10, k4_xboole_0(B_11, C_12)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 47.73/37.67  tff(c_304, plain, (![B_31, A_30, C_32]: (k3_xboole_0(B_31, k4_xboole_0(A_30, C_32))=k3_xboole_0(A_30, k4_xboole_0(B_31, C_32)))), inference(superposition, [status(thm), theory('equality')], [c_295, c_10])).
% 47.73/37.67  tff(c_8, plain, (![A_8, B_9]: (k4_xboole_0(A_8, k4_xboole_0(A_8, B_9))=k3_xboole_0(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_33])).
% 47.73/37.67  tff(c_367, plain, (![A_33, B_34, C_35]: (k2_xboole_0(k4_xboole_0(A_33, B_34), k4_xboole_0(A_33, C_35))=k4_xboole_0(A_33, k3_xboole_0(B_34, C_35)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 47.73/37.67  tff(c_5650, plain, (![A_93, B_94, B_95]: (k4_xboole_0(A_93, k3_xboole_0(B_94, k4_xboole_0(A_93, B_95)))=k2_xboole_0(k4_xboole_0(A_93, B_94), k3_xboole_0(A_93, B_95)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_367])).
% 47.73/37.67  tff(c_5818, plain, (![A_30, B_31, C_32]: (k4_xboole_0(A_30, k3_xboole_0(A_30, k4_xboole_0(B_31, C_32)))=k2_xboole_0(k4_xboole_0(A_30, B_31), k3_xboole_0(A_30, C_32)))), inference(superposition, [status(thm), theory('equality')], [c_304, c_5650])).
% 47.73/37.67  tff(c_5893, plain, (![A_30, B_31, C_32]: (k2_xboole_0(k4_xboole_0(A_30, B_31), k3_xboole_0(A_30, C_32))=k4_xboole_0(A_30, k4_xboole_0(B_31, C_32)))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_5818])).
% 47.73/37.67  tff(c_12, plain, (k2_xboole_0(k4_xboole_0('#skF_1', '#skF_2'), k3_xboole_0('#skF_1', '#skF_3'))!=k4_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_38])).
% 47.73/37.67  tff(c_101544, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_5893, c_12])).
% 47.73/37.67  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 47.73/37.67  
% 47.73/37.67  Inference rules
% 47.73/37.67  ----------------------
% 47.73/37.67  #Ref     : 0
% 47.73/37.67  #Sup     : 24920
% 47.73/37.67  #Fact    : 0
% 47.73/37.67  #Define  : 0
% 47.73/37.67  #Split   : 0
% 47.73/37.67  #Chain   : 0
% 47.73/37.67  #Close   : 0
% 47.73/37.67  
% 47.73/37.67  Ordering : KBO
% 47.73/37.67  
% 47.73/37.67  Simplification rules
% 47.73/37.67  ----------------------
% 47.73/37.67  #Subsume      : 3357
% 47.73/37.67  #Demod        : 69663
% 47.73/37.67  #Tautology    : 6977
% 47.73/37.67  #SimpNegUnit  : 0
% 47.73/37.67  #BackRed      : 20
% 47.73/37.67  
% 47.73/37.67  #Partial instantiations: 0
% 47.73/37.67  #Strategies tried      : 1
% 47.73/37.67  
% 47.73/37.67  Timing (in seconds)
% 47.73/37.67  ----------------------
% 47.73/37.67  Preprocessing        : 0.27
% 47.73/37.67  Parsing              : 0.14
% 47.73/37.67  CNF conversion       : 0.01
% 47.73/37.67  Main loop            : 36.60
% 47.73/37.67  Inferencing          : 2.51
% 47.73/37.67  Reduction            : 29.96
% 47.73/37.67  Demodulation         : 29.17
% 47.73/37.67  BG Simplification    : 0.48
% 47.73/37.67  Subsumption          : 2.98
% 47.73/37.67  Abstraction          : 0.99
% 47.73/37.67  MUC search           : 0.00
% 47.73/37.67  Cooper               : 0.00
% 47.73/37.67  Total                : 36.89
% 47.73/37.67  Index Insertion      : 0.00
% 47.73/37.67  Index Deletion       : 0.00
% 47.73/37.67  Index Matching       : 0.00
% 47.73/37.67  BG Taut test         : 0.00
%------------------------------------------------------------------------------

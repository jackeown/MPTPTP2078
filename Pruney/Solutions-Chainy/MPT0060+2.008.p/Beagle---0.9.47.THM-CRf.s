%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:43:06 EST 2020

% Result     : Theorem 2.60s
% Output     : CNFRefutation 2.60s
% Verified   : 
% Statistics : Number of formulae       :   33 (  66 expanded)
%              Number of leaves         :   14 (  29 expanded)
%              Depth                    :    7
%              Number of atoms          :   24 (  57 expanded)
%              Number of equality atoms :   23 (  56 expanded)
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

tff(f_29,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_33,axiom,(
    ! [A,B,C] : k3_xboole_0(A,k4_xboole_0(B,C)) = k4_xboole_0(k3_xboole_0(A,B),C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).

tff(f_31,axiom,(
    ! [A,B,C] : k4_xboole_0(k4_xboole_0(A,B),C) = k4_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_36,negated_conjecture,(
    ~ ! [A,B,C] : k4_xboole_0(A,k2_xboole_0(B,C)) = k3_xboole_0(k4_xboole_0(A,B),k4_xboole_0(A,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t53_xboole_1)).

tff(c_4,plain,(
    ! [A_3] : k3_xboole_0(A_3,A_3) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_54,plain,(
    ! [A_14,B_15,C_16] : k4_xboole_0(k3_xboole_0(A_14,B_15),C_16) = k3_xboole_0(A_14,k4_xboole_0(B_15,C_16)) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_69,plain,(
    ! [A_3,C_16] : k3_xboole_0(A_3,k4_xboole_0(A_3,C_16)) = k4_xboole_0(A_3,C_16) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_54])).

tff(c_6,plain,(
    ! [A_5,B_6,C_7] : k4_xboole_0(k4_xboole_0(A_5,B_6),C_7) = k4_xboole_0(A_5,k2_xboole_0(B_6,C_7)) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_113,plain,(
    ! [A_22,B_23,C_24] : k4_xboole_0(k3_xboole_0(A_22,B_23),C_24) = k3_xboole_0(B_23,k4_xboole_0(A_22,C_24)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_54])).

tff(c_131,plain,(
    ! [A_3,C_16,C_24] : k3_xboole_0(k4_xboole_0(A_3,C_16),k4_xboole_0(A_3,C_24)) = k4_xboole_0(k4_xboole_0(A_3,C_16),C_24) ),
    inference(superposition,[status(thm),theory(equality)],[c_69,c_113])).

tff(c_487,plain,(
    ! [A_37,C_38,C_39] : k3_xboole_0(k4_xboole_0(A_37,C_38),k4_xboole_0(A_37,C_39)) = k4_xboole_0(A_37,k2_xboole_0(C_38,C_39)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_131])).

tff(c_8,plain,(
    ! [A_8,B_9,C_10] : k4_xboole_0(k3_xboole_0(A_8,B_9),C_10) = k3_xboole_0(A_8,k4_xboole_0(B_9,C_10)) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_155,plain,(
    ! [B_25,A_26,C_27] : k3_xboole_0(B_25,k4_xboole_0(A_26,C_27)) = k3_xboole_0(A_26,k4_xboole_0(B_25,C_27)) ),
    inference(superposition,[status(thm),theory(equality)],[c_113,c_8])).

tff(c_241,plain,(
    ! [A_26,C_27,B_2] : k3_xboole_0(k4_xboole_0(A_26,C_27),B_2) = k3_xboole_0(A_26,k4_xboole_0(B_2,C_27)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_155])).

tff(c_493,plain,(
    ! [A_37,C_39,C_38] : k3_xboole_0(A_37,k4_xboole_0(k4_xboole_0(A_37,C_39),C_38)) = k4_xboole_0(A_37,k2_xboole_0(C_38,C_39)) ),
    inference(superposition,[status(thm),theory(equality)],[c_487,c_241])).

tff(c_572,plain,(
    ! [A_37,C_39,C_38] : k4_xboole_0(A_37,k2_xboole_0(C_39,C_38)) = k4_xboole_0(A_37,k2_xboole_0(C_38,C_39)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_69,c_6,c_493])).

tff(c_125,plain,(
    ! [B_23,A_22,C_24] : k3_xboole_0(B_23,k4_xboole_0(A_22,C_24)) = k3_xboole_0(A_22,k4_xboole_0(B_23,C_24)) ),
    inference(superposition,[status(thm),theory(equality)],[c_113,c_8])).

tff(c_10,plain,(
    k3_xboole_0(k4_xboole_0('#skF_1','#skF_2'),k4_xboole_0('#skF_1','#skF_3')) != k4_xboole_0('#skF_1',k2_xboole_0('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_11,plain,(
    k3_xboole_0(k4_xboole_0('#skF_1','#skF_3'),k4_xboole_0('#skF_1','#skF_2')) != k4_xboole_0('#skF_1',k2_xboole_0('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_10])).

tff(c_153,plain,(
    k3_xboole_0('#skF_1',k4_xboole_0(k4_xboole_0('#skF_1','#skF_3'),'#skF_2')) != k4_xboole_0('#skF_1',k2_xboole_0('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_125,c_11])).

tff(c_154,plain,(
    k4_xboole_0('#skF_1',k2_xboole_0('#skF_2','#skF_3')) != k4_xboole_0('#skF_1',k2_xboole_0('#skF_3','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_69,c_6,c_153])).

tff(c_596,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_572,c_154])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:53:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.60/1.40  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.60/1.40  
% 2.60/1.40  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.60/1.40  %$ k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1
% 2.60/1.40  
% 2.60/1.40  %Foreground sorts:
% 2.60/1.40  
% 2.60/1.40  
% 2.60/1.40  %Background operators:
% 2.60/1.40  
% 2.60/1.40  
% 2.60/1.40  %Foreground operators:
% 2.60/1.40  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.60/1.40  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.60/1.40  tff('#skF_2', type, '#skF_2': $i).
% 2.60/1.40  tff('#skF_3', type, '#skF_3': $i).
% 2.60/1.40  tff('#skF_1', type, '#skF_1': $i).
% 2.60/1.40  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.60/1.40  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.60/1.40  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.60/1.40  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.60/1.40  
% 2.60/1.41  tff(f_29, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 2.60/1.41  tff(f_33, axiom, (![A, B, C]: (k3_xboole_0(A, k4_xboole_0(B, C)) = k4_xboole_0(k3_xboole_0(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_xboole_1)).
% 2.60/1.41  tff(f_31, axiom, (![A, B, C]: (k4_xboole_0(k4_xboole_0(A, B), C) = k4_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_xboole_1)).
% 2.60/1.41  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 2.60/1.41  tff(f_36, negated_conjecture, ~(![A, B, C]: (k4_xboole_0(A, k2_xboole_0(B, C)) = k3_xboole_0(k4_xboole_0(A, B), k4_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t53_xboole_1)).
% 2.60/1.41  tff(c_4, plain, (![A_3]: (k3_xboole_0(A_3, A_3)=A_3)), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.60/1.41  tff(c_54, plain, (![A_14, B_15, C_16]: (k4_xboole_0(k3_xboole_0(A_14, B_15), C_16)=k3_xboole_0(A_14, k4_xboole_0(B_15, C_16)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.60/1.41  tff(c_69, plain, (![A_3, C_16]: (k3_xboole_0(A_3, k4_xboole_0(A_3, C_16))=k4_xboole_0(A_3, C_16))), inference(superposition, [status(thm), theory('equality')], [c_4, c_54])).
% 2.60/1.41  tff(c_6, plain, (![A_5, B_6, C_7]: (k4_xboole_0(k4_xboole_0(A_5, B_6), C_7)=k4_xboole_0(A_5, k2_xboole_0(B_6, C_7)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.60/1.41  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.60/1.41  tff(c_113, plain, (![A_22, B_23, C_24]: (k4_xboole_0(k3_xboole_0(A_22, B_23), C_24)=k3_xboole_0(B_23, k4_xboole_0(A_22, C_24)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_54])).
% 2.60/1.41  tff(c_131, plain, (![A_3, C_16, C_24]: (k3_xboole_0(k4_xboole_0(A_3, C_16), k4_xboole_0(A_3, C_24))=k4_xboole_0(k4_xboole_0(A_3, C_16), C_24))), inference(superposition, [status(thm), theory('equality')], [c_69, c_113])).
% 2.60/1.41  tff(c_487, plain, (![A_37, C_38, C_39]: (k3_xboole_0(k4_xboole_0(A_37, C_38), k4_xboole_0(A_37, C_39))=k4_xboole_0(A_37, k2_xboole_0(C_38, C_39)))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_131])).
% 2.60/1.41  tff(c_8, plain, (![A_8, B_9, C_10]: (k4_xboole_0(k3_xboole_0(A_8, B_9), C_10)=k3_xboole_0(A_8, k4_xboole_0(B_9, C_10)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.60/1.41  tff(c_155, plain, (![B_25, A_26, C_27]: (k3_xboole_0(B_25, k4_xboole_0(A_26, C_27))=k3_xboole_0(A_26, k4_xboole_0(B_25, C_27)))), inference(superposition, [status(thm), theory('equality')], [c_113, c_8])).
% 2.60/1.41  tff(c_241, plain, (![A_26, C_27, B_2]: (k3_xboole_0(k4_xboole_0(A_26, C_27), B_2)=k3_xboole_0(A_26, k4_xboole_0(B_2, C_27)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_155])).
% 2.60/1.41  tff(c_493, plain, (![A_37, C_39, C_38]: (k3_xboole_0(A_37, k4_xboole_0(k4_xboole_0(A_37, C_39), C_38))=k4_xboole_0(A_37, k2_xboole_0(C_38, C_39)))), inference(superposition, [status(thm), theory('equality')], [c_487, c_241])).
% 2.60/1.41  tff(c_572, plain, (![A_37, C_39, C_38]: (k4_xboole_0(A_37, k2_xboole_0(C_39, C_38))=k4_xboole_0(A_37, k2_xboole_0(C_38, C_39)))), inference(demodulation, [status(thm), theory('equality')], [c_69, c_6, c_493])).
% 2.60/1.41  tff(c_125, plain, (![B_23, A_22, C_24]: (k3_xboole_0(B_23, k4_xboole_0(A_22, C_24))=k3_xboole_0(A_22, k4_xboole_0(B_23, C_24)))), inference(superposition, [status(thm), theory('equality')], [c_113, c_8])).
% 2.60/1.41  tff(c_10, plain, (k3_xboole_0(k4_xboole_0('#skF_1', '#skF_2'), k4_xboole_0('#skF_1', '#skF_3'))!=k4_xboole_0('#skF_1', k2_xboole_0('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.60/1.41  tff(c_11, plain, (k3_xboole_0(k4_xboole_0('#skF_1', '#skF_3'), k4_xboole_0('#skF_1', '#skF_2'))!=k4_xboole_0('#skF_1', k2_xboole_0('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_10])).
% 2.60/1.41  tff(c_153, plain, (k3_xboole_0('#skF_1', k4_xboole_0(k4_xboole_0('#skF_1', '#skF_3'), '#skF_2'))!=k4_xboole_0('#skF_1', k2_xboole_0('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_125, c_11])).
% 2.60/1.41  tff(c_154, plain, (k4_xboole_0('#skF_1', k2_xboole_0('#skF_2', '#skF_3'))!=k4_xboole_0('#skF_1', k2_xboole_0('#skF_3', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_69, c_6, c_153])).
% 2.60/1.41  tff(c_596, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_572, c_154])).
% 2.60/1.41  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.60/1.41  
% 2.60/1.41  Inference rules
% 2.60/1.41  ----------------------
% 2.60/1.41  #Ref     : 0
% 2.60/1.41  #Sup     : 138
% 2.60/1.41  #Fact    : 0
% 2.60/1.41  #Define  : 0
% 2.60/1.41  #Split   : 0
% 2.60/1.41  #Chain   : 0
% 2.60/1.41  #Close   : 0
% 2.60/1.41  
% 2.60/1.41  Ordering : KBO
% 2.60/1.41  
% 2.60/1.41  Simplification rules
% 2.60/1.41  ----------------------
% 2.60/1.41  #Subsume      : 11
% 2.60/1.41  #Demod        : 170
% 2.60/1.41  #Tautology    : 69
% 2.60/1.41  #SimpNegUnit  : 0
% 2.60/1.41  #BackRed      : 2
% 2.60/1.41  
% 2.60/1.41  #Partial instantiations: 0
% 2.60/1.41  #Strategies tried      : 1
% 2.60/1.41  
% 2.60/1.41  Timing (in seconds)
% 2.60/1.41  ----------------------
% 2.60/1.42  Preprocessing        : 0.28
% 2.60/1.42  Parsing              : 0.15
% 2.60/1.42  CNF conversion       : 0.01
% 2.60/1.42  Main loop            : 0.33
% 2.60/1.42  Inferencing          : 0.10
% 2.60/1.42  Reduction            : 0.16
% 2.60/1.42  Demodulation         : 0.14
% 2.60/1.42  BG Simplification    : 0.02
% 2.60/1.42  Subsumption          : 0.04
% 2.60/1.42  Abstraction          : 0.03
% 2.60/1.42  MUC search           : 0.00
% 2.60/1.42  Cooper               : 0.00
% 2.60/1.42  Total                : 0.64
% 2.60/1.42  Index Insertion      : 0.00
% 2.60/1.42  Index Deletion       : 0.00
% 2.60/1.42  Index Matching       : 0.00
% 2.60/1.42  BG Taut test         : 0.00
%------------------------------------------------------------------------------

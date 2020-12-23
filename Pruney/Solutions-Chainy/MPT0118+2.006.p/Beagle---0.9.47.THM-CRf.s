%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:45:32 EST 2020

% Result     : Theorem 4.38s
% Output     : CNFRefutation 4.38s
% Verified   : 
% Statistics : Number of formulae       :   26 (  32 expanded)
%              Number of leaves         :   14 (  17 expanded)
%              Depth                    :    6
%              Number of atoms          :   17 (  23 expanded)
%              Number of equality atoms :   16 (  22 expanded)
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

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_31,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_33,axiom,(
    ! [A,B,C] : k4_xboole_0(A,k4_xboole_0(B,C)) = k2_xboole_0(k4_xboole_0(A,B),k3_xboole_0(A,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_xboole_1)).

tff(f_29,axiom,(
    ! [A,B,C] : k4_xboole_0(k4_xboole_0(A,B),C) = k4_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

tff(f_36,negated_conjecture,(
    ~ ! [A,B,C] : k4_xboole_0(k3_xboole_0(A,B),k3_xboole_0(C,B)) = k3_xboole_0(k4_xboole_0(A,C),B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t111_xboole_1)).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_6,plain,(
    ! [A_6,B_7] : k4_xboole_0(A_6,k4_xboole_0(A_6,B_7)) = k3_xboole_0(A_6,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_169,plain,(
    ! [A_22,B_23,C_24] : k2_xboole_0(k4_xboole_0(A_22,B_23),k3_xboole_0(A_22,C_24)) = k4_xboole_0(A_22,k4_xboole_0(B_23,C_24)) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_249,plain,(
    ! [B_28,B_29,A_30] : k2_xboole_0(k4_xboole_0(B_28,B_29),k3_xboole_0(A_30,B_28)) = k4_xboole_0(B_28,k4_xboole_0(B_29,A_30)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_169])).

tff(c_60,plain,(
    ! [A_15,B_16,C_17] : k4_xboole_0(k4_xboole_0(A_15,B_16),C_17) = k4_xboole_0(A_15,k2_xboole_0(B_16,C_17)) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_82,plain,(
    ! [A_6,B_7,C_17] : k4_xboole_0(A_6,k2_xboole_0(k4_xboole_0(A_6,B_7),C_17)) = k4_xboole_0(k3_xboole_0(A_6,B_7),C_17) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_60])).

tff(c_255,plain,(
    ! [B_28,B_29,A_30] : k4_xboole_0(k3_xboole_0(B_28,B_29),k3_xboole_0(A_30,B_28)) = k4_xboole_0(B_28,k4_xboole_0(B_28,k4_xboole_0(B_29,A_30))) ),
    inference(superposition,[status(thm),theory(equality)],[c_249,c_82])).

tff(c_1161,plain,(
    ! [B_54,B_55,A_56] : k4_xboole_0(k3_xboole_0(B_54,B_55),k3_xboole_0(A_56,B_54)) = k3_xboole_0(B_54,k4_xboole_0(B_55,A_56)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_255])).

tff(c_1235,plain,(
    ! [B_2,A_1,A_56] : k4_xboole_0(k3_xboole_0(B_2,A_1),k3_xboole_0(A_56,A_1)) = k3_xboole_0(A_1,k4_xboole_0(B_2,A_56)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_1161])).

tff(c_10,plain,(
    k4_xboole_0(k3_xboole_0('#skF_1','#skF_2'),k3_xboole_0('#skF_3','#skF_2')) != k3_xboole_0(k4_xboole_0('#skF_1','#skF_3'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_11,plain,(
    k4_xboole_0(k3_xboole_0('#skF_1','#skF_2'),k3_xboole_0('#skF_3','#skF_2')) != k3_xboole_0('#skF_2',k4_xboole_0('#skF_1','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_10])).

tff(c_1460,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1235,c_11])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:20:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.38/2.09  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.38/2.09  
% 4.38/2.09  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.38/2.09  %$ k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1
% 4.38/2.09  
% 4.38/2.09  %Foreground sorts:
% 4.38/2.09  
% 4.38/2.09  
% 4.38/2.09  %Background operators:
% 4.38/2.09  
% 4.38/2.09  
% 4.38/2.09  %Foreground operators:
% 4.38/2.09  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.38/2.09  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.38/2.09  tff('#skF_2', type, '#skF_2': $i).
% 4.38/2.09  tff('#skF_3', type, '#skF_3': $i).
% 4.38/2.09  tff('#skF_1', type, '#skF_1': $i).
% 4.38/2.09  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.38/2.09  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.38/2.09  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.38/2.09  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.38/2.09  
% 4.38/2.11  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 4.38/2.11  tff(f_31, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 4.38/2.11  tff(f_33, axiom, (![A, B, C]: (k4_xboole_0(A, k4_xboole_0(B, C)) = k2_xboole_0(k4_xboole_0(A, B), k3_xboole_0(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_xboole_1)).
% 4.38/2.11  tff(f_29, axiom, (![A, B, C]: (k4_xboole_0(k4_xboole_0(A, B), C) = k4_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_xboole_1)).
% 4.38/2.11  tff(f_36, negated_conjecture, ~(![A, B, C]: (k4_xboole_0(k3_xboole_0(A, B), k3_xboole_0(C, B)) = k3_xboole_0(k4_xboole_0(A, C), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t111_xboole_1)).
% 4.38/2.11  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.38/2.11  tff(c_6, plain, (![A_6, B_7]: (k4_xboole_0(A_6, k4_xboole_0(A_6, B_7))=k3_xboole_0(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.38/2.11  tff(c_169, plain, (![A_22, B_23, C_24]: (k2_xboole_0(k4_xboole_0(A_22, B_23), k3_xboole_0(A_22, C_24))=k4_xboole_0(A_22, k4_xboole_0(B_23, C_24)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.38/2.11  tff(c_249, plain, (![B_28, B_29, A_30]: (k2_xboole_0(k4_xboole_0(B_28, B_29), k3_xboole_0(A_30, B_28))=k4_xboole_0(B_28, k4_xboole_0(B_29, A_30)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_169])).
% 4.38/2.11  tff(c_60, plain, (![A_15, B_16, C_17]: (k4_xboole_0(k4_xboole_0(A_15, B_16), C_17)=k4_xboole_0(A_15, k2_xboole_0(B_16, C_17)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.38/2.11  tff(c_82, plain, (![A_6, B_7, C_17]: (k4_xboole_0(A_6, k2_xboole_0(k4_xboole_0(A_6, B_7), C_17))=k4_xboole_0(k3_xboole_0(A_6, B_7), C_17))), inference(superposition, [status(thm), theory('equality')], [c_6, c_60])).
% 4.38/2.11  tff(c_255, plain, (![B_28, B_29, A_30]: (k4_xboole_0(k3_xboole_0(B_28, B_29), k3_xboole_0(A_30, B_28))=k4_xboole_0(B_28, k4_xboole_0(B_28, k4_xboole_0(B_29, A_30))))), inference(superposition, [status(thm), theory('equality')], [c_249, c_82])).
% 4.38/2.11  tff(c_1161, plain, (![B_54, B_55, A_56]: (k4_xboole_0(k3_xboole_0(B_54, B_55), k3_xboole_0(A_56, B_54))=k3_xboole_0(B_54, k4_xboole_0(B_55, A_56)))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_255])).
% 4.38/2.11  tff(c_1235, plain, (![B_2, A_1, A_56]: (k4_xboole_0(k3_xboole_0(B_2, A_1), k3_xboole_0(A_56, A_1))=k3_xboole_0(A_1, k4_xboole_0(B_2, A_56)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_1161])).
% 4.38/2.11  tff(c_10, plain, (k4_xboole_0(k3_xboole_0('#skF_1', '#skF_2'), k3_xboole_0('#skF_3', '#skF_2'))!=k3_xboole_0(k4_xboole_0('#skF_1', '#skF_3'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_36])).
% 4.38/2.11  tff(c_11, plain, (k4_xboole_0(k3_xboole_0('#skF_1', '#skF_2'), k3_xboole_0('#skF_3', '#skF_2'))!=k3_xboole_0('#skF_2', k4_xboole_0('#skF_1', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_10])).
% 4.38/2.11  tff(c_1460, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1235, c_11])).
% 4.38/2.11  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.38/2.11  
% 4.38/2.11  Inference rules
% 4.38/2.11  ----------------------
% 4.38/2.11  #Ref     : 0
% 4.38/2.11  #Sup     : 395
% 4.38/2.11  #Fact    : 0
% 4.38/2.11  #Define  : 0
% 4.38/2.11  #Split   : 0
% 4.38/2.11  #Chain   : 0
% 4.38/2.11  #Close   : 0
% 4.38/2.11  
% 4.38/2.11  Ordering : KBO
% 4.38/2.11  
% 4.38/2.11  Simplification rules
% 4.38/2.11  ----------------------
% 4.38/2.11  #Subsume      : 31
% 4.38/2.11  #Demod        : 115
% 4.38/2.11  #Tautology    : 95
% 4.38/2.11  #SimpNegUnit  : 0
% 4.38/2.11  #BackRed      : 1
% 4.38/2.11  
% 4.38/2.11  #Partial instantiations: 0
% 4.38/2.11  #Strategies tried      : 1
% 4.38/2.11  
% 4.38/2.11  Timing (in seconds)
% 4.38/2.11  ----------------------
% 4.38/2.11  Preprocessing        : 0.41
% 4.38/2.11  Parsing              : 0.22
% 4.38/2.11  CNF conversion       : 0.02
% 4.38/2.11  Main loop            : 0.84
% 4.38/2.11  Inferencing          : 0.27
% 4.38/2.11  Reduction            : 0.35
% 4.38/2.11  Demodulation         : 0.30
% 4.38/2.11  BG Simplification    : 0.05
% 4.38/2.11  Subsumption          : 0.12
% 4.38/2.11  Abstraction          : 0.06
% 4.38/2.11  MUC search           : 0.00
% 4.38/2.12  Cooper               : 0.00
% 4.38/2.12  Total                : 1.29
% 4.38/2.12  Index Insertion      : 0.00
% 4.38/2.12  Index Deletion       : 0.00
% 4.38/2.12  Index Matching       : 0.00
% 4.38/2.12  BG Taut test         : 0.00
%------------------------------------------------------------------------------

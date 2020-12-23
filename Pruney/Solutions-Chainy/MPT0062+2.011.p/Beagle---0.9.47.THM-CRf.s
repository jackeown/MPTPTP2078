%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:43:08 EST 2020

% Result     : Theorem 52.11s
% Output     : CNFRefutation 52.11s
% Verified   : 
% Statistics : Number of formulae       :   25 (  25 expanded)
%              Number of leaves         :   14 (  14 expanded)
%              Depth                    :    5
%              Number of atoms          :   17 (  17 expanded)
%              Number of equality atoms :   16 (  16 expanded)
%              Maximal formula depth    :    4 (   3 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

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

tff(f_37,axiom,(
    ! [A,B] : k2_xboole_0(k3_xboole_0(A,B),k4_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).

tff(f_29,axiom,(
    ! [A,B,C] : k4_xboole_0(k4_xboole_0(A,B),C) = k4_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] : k4_xboole_0(A,k3_xboole_0(A,B)) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

tff(f_31,axiom,(
    ! [A,B,C] : k4_xboole_0(k2_xboole_0(A,B),C) = k2_xboole_0(k4_xboole_0(A,C),k4_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_xboole_1)).

tff(f_40,negated_conjecture,(
    ~ ! [A,B] : k4_xboole_0(k2_xboole_0(A,B),k3_xboole_0(A,B)) = k2_xboole_0(k4_xboole_0(A,B),k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_xboole_1)).

tff(c_12,plain,(
    ! [A_13,B_14] : k2_xboole_0(k3_xboole_0(A_13,B_14),k4_xboole_0(A_13,B_14)) = A_13 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_85,plain,(
    ! [A_25,B_26,C_27] : k4_xboole_0(k4_xboole_0(A_25,B_26),C_27) = k4_xboole_0(A_25,k2_xboole_0(B_26,C_27)) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_2,plain,(
    ! [A_1,B_2] : k2_xboole_0(A_1,k4_xboole_0(B_2,A_1)) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_1463,plain,(
    ! [C_74,A_75,B_76] : k2_xboole_0(C_74,k4_xboole_0(A_75,k2_xboole_0(B_76,C_74))) = k2_xboole_0(C_74,k4_xboole_0(A_75,B_76)) ),
    inference(superposition,[status(thm),theory(equality)],[c_85,c_2])).

tff(c_1557,plain,(
    ! [A_13,B_14,A_75] : k2_xboole_0(k4_xboole_0(A_13,B_14),k4_xboole_0(A_75,k3_xboole_0(A_13,B_14))) = k2_xboole_0(k4_xboole_0(A_13,B_14),k4_xboole_0(A_75,A_13)) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_1463])).

tff(c_8,plain,(
    ! [A_9,B_10] : k4_xboole_0(A_9,k3_xboole_0(A_9,B_10)) = k4_xboole_0(A_9,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_255,plain,(
    ! [A_36,C_37,B_38] : k2_xboole_0(k4_xboole_0(A_36,C_37),k4_xboole_0(B_38,C_37)) = k4_xboole_0(k2_xboole_0(A_36,B_38),C_37) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_284,plain,(
    ! [A_9,B_10,B_38] : k2_xboole_0(k4_xboole_0(A_9,B_10),k4_xboole_0(B_38,k3_xboole_0(A_9,B_10))) = k4_xboole_0(k2_xboole_0(A_9,B_38),k3_xboole_0(A_9,B_10)) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_255])).

tff(c_170126,plain,(
    ! [A_9,B_38,B_10] : k4_xboole_0(k2_xboole_0(A_9,B_38),k3_xboole_0(A_9,B_10)) = k2_xboole_0(k4_xboole_0(A_9,B_10),k4_xboole_0(B_38,A_9)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1557,c_284])).

tff(c_14,plain,(
    k4_xboole_0(k2_xboole_0('#skF_1','#skF_2'),k3_xboole_0('#skF_1','#skF_2')) != k2_xboole_0(k4_xboole_0('#skF_1','#skF_2'),k4_xboole_0('#skF_2','#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_171607,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_170126,c_14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:28:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 52.11/41.99  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 52.11/41.99  
% 52.11/41.99  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 52.11/41.99  %$ k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > #skF_2 > #skF_1
% 52.11/41.99  
% 52.11/41.99  %Foreground sorts:
% 52.11/41.99  
% 52.11/41.99  
% 52.11/41.99  %Background operators:
% 52.11/41.99  
% 52.11/41.99  
% 52.11/41.99  %Foreground operators:
% 52.11/41.99  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 52.11/41.99  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 52.11/41.99  tff('#skF_2', type, '#skF_2': $i).
% 52.11/41.99  tff('#skF_1', type, '#skF_1': $i).
% 52.11/41.99  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 52.11/41.99  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 52.11/41.99  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 52.11/41.99  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 52.11/41.99  
% 52.11/42.00  tff(f_37, axiom, (![A, B]: (k2_xboole_0(k3_xboole_0(A, B), k4_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_xboole_1)).
% 52.11/42.00  tff(f_29, axiom, (![A, B, C]: (k4_xboole_0(k4_xboole_0(A, B), C) = k4_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_xboole_1)).
% 52.11/42.00  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 52.11/42.00  tff(f_33, axiom, (![A, B]: (k4_xboole_0(A, k3_xboole_0(A, B)) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_xboole_1)).
% 52.11/42.00  tff(f_31, axiom, (![A, B, C]: (k4_xboole_0(k2_xboole_0(A, B), C) = k2_xboole_0(k4_xboole_0(A, C), k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t42_xboole_1)).
% 52.11/42.00  tff(f_40, negated_conjecture, ~(![A, B]: (k4_xboole_0(k2_xboole_0(A, B), k3_xboole_0(A, B)) = k2_xboole_0(k4_xboole_0(A, B), k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_xboole_1)).
% 52.11/42.00  tff(c_12, plain, (![A_13, B_14]: (k2_xboole_0(k3_xboole_0(A_13, B_14), k4_xboole_0(A_13, B_14))=A_13)), inference(cnfTransformation, [status(thm)], [f_37])).
% 52.11/42.00  tff(c_85, plain, (![A_25, B_26, C_27]: (k4_xboole_0(k4_xboole_0(A_25, B_26), C_27)=k4_xboole_0(A_25, k2_xboole_0(B_26, C_27)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 52.11/42.00  tff(c_2, plain, (![A_1, B_2]: (k2_xboole_0(A_1, k4_xboole_0(B_2, A_1))=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 52.11/42.00  tff(c_1463, plain, (![C_74, A_75, B_76]: (k2_xboole_0(C_74, k4_xboole_0(A_75, k2_xboole_0(B_76, C_74)))=k2_xboole_0(C_74, k4_xboole_0(A_75, B_76)))), inference(superposition, [status(thm), theory('equality')], [c_85, c_2])).
% 52.11/42.00  tff(c_1557, plain, (![A_13, B_14, A_75]: (k2_xboole_0(k4_xboole_0(A_13, B_14), k4_xboole_0(A_75, k3_xboole_0(A_13, B_14)))=k2_xboole_0(k4_xboole_0(A_13, B_14), k4_xboole_0(A_75, A_13)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_1463])).
% 52.11/42.00  tff(c_8, plain, (![A_9, B_10]: (k4_xboole_0(A_9, k3_xboole_0(A_9, B_10))=k4_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_33])).
% 52.11/42.00  tff(c_255, plain, (![A_36, C_37, B_38]: (k2_xboole_0(k4_xboole_0(A_36, C_37), k4_xboole_0(B_38, C_37))=k4_xboole_0(k2_xboole_0(A_36, B_38), C_37))), inference(cnfTransformation, [status(thm)], [f_31])).
% 52.11/42.00  tff(c_284, plain, (![A_9, B_10, B_38]: (k2_xboole_0(k4_xboole_0(A_9, B_10), k4_xboole_0(B_38, k3_xboole_0(A_9, B_10)))=k4_xboole_0(k2_xboole_0(A_9, B_38), k3_xboole_0(A_9, B_10)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_255])).
% 52.11/42.00  tff(c_170126, plain, (![A_9, B_38, B_10]: (k4_xboole_0(k2_xboole_0(A_9, B_38), k3_xboole_0(A_9, B_10))=k2_xboole_0(k4_xboole_0(A_9, B_10), k4_xboole_0(B_38, A_9)))), inference(demodulation, [status(thm), theory('equality')], [c_1557, c_284])).
% 52.11/42.00  tff(c_14, plain, (k4_xboole_0(k2_xboole_0('#skF_1', '#skF_2'), k3_xboole_0('#skF_1', '#skF_2'))!=k2_xboole_0(k4_xboole_0('#skF_1', '#skF_2'), k4_xboole_0('#skF_2', '#skF_1'))), inference(cnfTransformation, [status(thm)], [f_40])).
% 52.11/42.00  tff(c_171607, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_170126, c_14])).
% 52.11/42.00  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 52.11/42.00  
% 52.11/42.00  Inference rules
% 52.11/42.00  ----------------------
% 52.11/42.00  #Ref     : 0
% 52.11/42.00  #Sup     : 43500
% 52.11/42.00  #Fact    : 0
% 52.11/42.00  #Define  : 0
% 52.11/42.00  #Split   : 0
% 52.11/42.00  #Chain   : 0
% 52.11/42.00  #Close   : 0
% 52.11/42.00  
% 52.11/42.00  Ordering : KBO
% 52.11/42.00  
% 52.11/42.00  Simplification rules
% 52.11/42.00  ----------------------
% 52.11/42.00  #Subsume      : 3021
% 52.11/42.00  #Demod        : 60345
% 52.11/42.00  #Tautology    : 18305
% 52.11/42.00  #SimpNegUnit  : 0
% 52.11/42.00  #BackRed      : 7
% 52.11/42.00  
% 52.11/42.00  #Partial instantiations: 0
% 52.11/42.00  #Strategies tried      : 1
% 52.11/42.00  
% 52.11/42.00  Timing (in seconds)
% 52.11/42.00  ----------------------
% 52.11/42.00  Preprocessing        : 0.25
% 52.11/42.00  Parsing              : 0.13
% 52.11/42.00  CNF conversion       : 0.01
% 52.11/42.00  Main loop            : 40.94
% 52.11/42.00  Inferencing          : 4.40
% 52.11/42.00  Reduction            : 28.05
% 52.11/42.00  Demodulation         : 26.93
% 52.11/42.00  BG Simplification    : 0.71
% 52.11/42.00  Subsumption          : 6.75
% 52.11/42.00  Abstraction          : 1.49
% 52.11/42.00  MUC search           : 0.00
% 52.11/42.00  Cooper               : 0.00
% 52.11/42.00  Total                : 41.21
% 52.11/42.00  Index Insertion      : 0.00
% 52.11/42.00  Index Deletion       : 0.00
% 52.11/42.00  Index Matching       : 0.00
% 52.11/42.00  BG Taut test         : 0.00
%------------------------------------------------------------------------------

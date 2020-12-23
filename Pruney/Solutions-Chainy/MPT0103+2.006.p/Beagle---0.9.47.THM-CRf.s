%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:44:46 EST 2020

% Result     : Theorem 1.71s
% Output     : CNFRefutation 1.71s
% Verified   : 
% Statistics : Number of formulae       :   26 (  28 expanded)
%              Number of leaves         :   16 (  17 expanded)
%              Depth                    :    4
%              Number of atoms          :   17 (  19 expanded)
%              Number of equality atoms :   12 (  14 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(f_27,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k2_xboole_0(k4_xboole_0(A,B),k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_xboole_0)).

tff(f_37,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

tff(f_35,axiom,(
    ! [A,B,C] : k4_xboole_0(k4_xboole_0(A,B),C) = k4_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_40,negated_conjecture,(
    ~ ! [A,B] : r1_tarski(k4_xboole_0(A,B),k5_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t96_xboole_1)).

tff(c_61,plain,(
    ! [A_21,B_22] : k2_xboole_0(k4_xboole_0(A_21,B_22),k4_xboole_0(B_22,A_21)) = k5_xboole_0(A_21,B_22) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_12,plain,(
    ! [A_10,B_11] : k4_xboole_0(A_10,k2_xboole_0(A_10,B_11)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_85,plain,(
    ! [A_23,B_24] : k4_xboole_0(k4_xboole_0(A_23,B_24),k5_xboole_0(A_23,B_24)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_61,c_12])).

tff(c_10,plain,(
    ! [A_7,B_8,C_9] : k4_xboole_0(k4_xboole_0(A_7,B_8),C_9) = k4_xboole_0(A_7,k2_xboole_0(B_8,C_9)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_102,plain,(
    ! [A_23,B_24] : k4_xboole_0(A_23,k2_xboole_0(B_24,k5_xboole_0(A_23,B_24))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_85,c_10])).

tff(c_23,plain,(
    ! [A_16,B_17] :
      ( r1_tarski(A_16,B_17)
      | k4_xboole_0(A_16,B_17) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_14,plain,(
    ~ r1_tarski(k4_xboole_0('#skF_1','#skF_2'),k5_xboole_0('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_31,plain,(
    k4_xboole_0(k4_xboole_0('#skF_1','#skF_2'),k5_xboole_0('#skF_1','#skF_2')) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_23,c_14])).

tff(c_32,plain,(
    k4_xboole_0('#skF_1',k2_xboole_0('#skF_2',k5_xboole_0('#skF_1','#skF_2'))) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_31])).

tff(c_146,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_32])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:01:38 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.71/1.15  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.71/1.15  
% 1.71/1.15  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.71/1.15  %$ r1_tarski > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1
% 1.71/1.15  
% 1.71/1.15  %Foreground sorts:
% 1.71/1.15  
% 1.71/1.15  
% 1.71/1.15  %Background operators:
% 1.71/1.15  
% 1.71/1.15  
% 1.71/1.15  %Foreground operators:
% 1.71/1.15  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.71/1.15  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.71/1.15  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.71/1.15  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 1.71/1.15  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.71/1.15  tff('#skF_2', type, '#skF_2': $i).
% 1.71/1.15  tff('#skF_1', type, '#skF_1': $i).
% 1.71/1.15  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.71/1.15  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.71/1.15  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.71/1.15  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.71/1.15  
% 1.71/1.16  tff(f_27, axiom, (![A, B]: (k5_xboole_0(A, B) = k2_xboole_0(k4_xboole_0(A, B), k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d6_xboole_0)).
% 1.71/1.16  tff(f_37, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_xboole_1)).
% 1.71/1.16  tff(f_35, axiom, (![A, B, C]: (k4_xboole_0(k4_xboole_0(A, B), C) = k4_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_xboole_1)).
% 1.71/1.16  tff(f_31, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 1.71/1.16  tff(f_40, negated_conjecture, ~(![A, B]: r1_tarski(k4_xboole_0(A, B), k5_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t96_xboole_1)).
% 1.71/1.16  tff(c_61, plain, (![A_21, B_22]: (k2_xboole_0(k4_xboole_0(A_21, B_22), k4_xboole_0(B_22, A_21))=k5_xboole_0(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.71/1.16  tff(c_12, plain, (![A_10, B_11]: (k4_xboole_0(A_10, k2_xboole_0(A_10, B_11))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.71/1.16  tff(c_85, plain, (![A_23, B_24]: (k4_xboole_0(k4_xboole_0(A_23, B_24), k5_xboole_0(A_23, B_24))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_61, c_12])).
% 1.71/1.16  tff(c_10, plain, (![A_7, B_8, C_9]: (k4_xboole_0(k4_xboole_0(A_7, B_8), C_9)=k4_xboole_0(A_7, k2_xboole_0(B_8, C_9)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.71/1.16  tff(c_102, plain, (![A_23, B_24]: (k4_xboole_0(A_23, k2_xboole_0(B_24, k5_xboole_0(A_23, B_24)))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_85, c_10])).
% 1.71/1.16  tff(c_23, plain, (![A_16, B_17]: (r1_tarski(A_16, B_17) | k4_xboole_0(A_16, B_17)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.71/1.16  tff(c_14, plain, (~r1_tarski(k4_xboole_0('#skF_1', '#skF_2'), k5_xboole_0('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.71/1.16  tff(c_31, plain, (k4_xboole_0(k4_xboole_0('#skF_1', '#skF_2'), k5_xboole_0('#skF_1', '#skF_2'))!=k1_xboole_0), inference(resolution, [status(thm)], [c_23, c_14])).
% 1.71/1.16  tff(c_32, plain, (k4_xboole_0('#skF_1', k2_xboole_0('#skF_2', k5_xboole_0('#skF_1', '#skF_2')))!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_10, c_31])).
% 1.71/1.16  tff(c_146, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_102, c_32])).
% 1.71/1.16  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.71/1.16  
% 1.71/1.16  Inference rules
% 1.71/1.16  ----------------------
% 1.71/1.16  #Ref     : 0
% 1.71/1.16  #Sup     : 36
% 1.71/1.16  #Fact    : 0
% 1.71/1.16  #Define  : 0
% 1.71/1.16  #Split   : 0
% 1.71/1.16  #Chain   : 0
% 1.71/1.16  #Close   : 0
% 1.71/1.16  
% 1.71/1.16  Ordering : KBO
% 1.71/1.16  
% 1.71/1.16  Simplification rules
% 1.71/1.16  ----------------------
% 1.71/1.16  #Subsume      : 0
% 1.71/1.16  #Demod        : 6
% 1.71/1.16  #Tautology    : 11
% 1.71/1.16  #SimpNegUnit  : 0
% 1.71/1.16  #BackRed      : 2
% 1.71/1.16  
% 1.71/1.16  #Partial instantiations: 0
% 1.71/1.16  #Strategies tried      : 1
% 1.71/1.16  
% 1.71/1.16  Timing (in seconds)
% 1.71/1.16  ----------------------
% 1.71/1.17  Preprocessing        : 0.26
% 1.71/1.17  Parsing              : 0.14
% 1.71/1.17  CNF conversion       : 0.02
% 1.71/1.17  Main loop            : 0.15
% 1.71/1.17  Inferencing          : 0.06
% 1.71/1.17  Reduction            : 0.05
% 1.71/1.17  Demodulation         : 0.04
% 1.71/1.17  BG Simplification    : 0.01
% 1.71/1.17  Subsumption          : 0.02
% 1.71/1.17  Abstraction          : 0.01
% 1.71/1.17  MUC search           : 0.00
% 1.71/1.17  Cooper               : 0.00
% 1.71/1.17  Total                : 0.43
% 1.71/1.17  Index Insertion      : 0.00
% 1.71/1.17  Index Deletion       : 0.00
% 1.71/1.17  Index Matching       : 0.00
% 1.71/1.17  BG Taut test         : 0.00
%------------------------------------------------------------------------------

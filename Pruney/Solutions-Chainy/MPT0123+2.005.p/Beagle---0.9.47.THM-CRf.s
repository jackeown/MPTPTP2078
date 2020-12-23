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
% DateTime   : Thu Dec  3 09:45:35 EST 2020

% Result     : Theorem 1.63s
% Output     : CNFRefutation 1.63s
% Verified   : 
% Statistics : Number of formulae       :   21 (  25 expanded)
%              Number of leaves         :   13 (  15 expanded)
%              Depth                    :    5
%              Number of atoms          :   12 (  16 expanded)
%              Number of equality atoms :   11 (  15 expanded)
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
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_31,axiom,(
    ! [A,B,C] : k4_xboole_0(A,k3_xboole_0(B,C)) = k2_xboole_0(k4_xboole_0(A,B),k4_xboole_0(A,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_xboole_1)).

tff(f_29,axiom,(
    ! [A,B,C] : k4_xboole_0(A,k2_xboole_0(B,C)) = k3_xboole_0(k4_xboole_0(A,B),k4_xboole_0(A,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t53_xboole_1)).

tff(f_34,negated_conjecture,(
    ~ ! [A,B,C] : k3_xboole_0(A,k3_xboole_0(B,C)) = k3_xboole_0(k3_xboole_0(A,B),k3_xboole_0(A,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t116_xboole_1)).

tff(c_2,plain,(
    ! [A_1,B_2] : k4_xboole_0(A_1,k4_xboole_0(A_1,B_2)) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_6,plain,(
    ! [A_6,B_7,C_8] : k2_xboole_0(k4_xboole_0(A_6,B_7),k4_xboole_0(A_6,C_8)) = k4_xboole_0(A_6,k3_xboole_0(B_7,C_8)) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_58,plain,(
    ! [A_16,B_17,C_18] : k3_xboole_0(k4_xboole_0(A_16,B_17),k4_xboole_0(A_16,C_18)) = k4_xboole_0(A_16,k2_xboole_0(B_17,C_18)) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_127,plain,(
    ! [A_21,B_22,B_23] : k4_xboole_0(A_21,k2_xboole_0(B_22,k4_xboole_0(A_21,B_23))) = k3_xboole_0(k4_xboole_0(A_21,B_22),k3_xboole_0(A_21,B_23)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_58])).

tff(c_163,plain,(
    ! [A_6,B_7,C_8] : k3_xboole_0(k4_xboole_0(A_6,k4_xboole_0(A_6,B_7)),k3_xboole_0(A_6,C_8)) = k4_xboole_0(A_6,k4_xboole_0(A_6,k3_xboole_0(B_7,C_8))) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_127])).

tff(c_172,plain,(
    ! [A_6,B_7,C_8] : k3_xboole_0(k3_xboole_0(A_6,B_7),k3_xboole_0(A_6,C_8)) = k3_xboole_0(A_6,k3_xboole_0(B_7,C_8)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_2,c_163])).

tff(c_8,plain,(
    k3_xboole_0(k3_xboole_0('#skF_1','#skF_2'),k3_xboole_0('#skF_1','#skF_3')) != k3_xboole_0('#skF_1',k3_xboole_0('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_175,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_172,c_8])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n004.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 11:45:23 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.63/1.16  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.63/1.16  
% 1.63/1.16  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.63/1.16  %$ k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1
% 1.63/1.16  
% 1.63/1.16  %Foreground sorts:
% 1.63/1.16  
% 1.63/1.16  
% 1.63/1.16  %Background operators:
% 1.63/1.16  
% 1.63/1.16  
% 1.63/1.16  %Foreground operators:
% 1.63/1.16  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.63/1.16  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.63/1.16  tff('#skF_2', type, '#skF_2': $i).
% 1.63/1.16  tff('#skF_3', type, '#skF_3': $i).
% 1.63/1.16  tff('#skF_1', type, '#skF_1': $i).
% 1.63/1.16  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.63/1.16  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.63/1.16  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.63/1.16  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.63/1.16  
% 1.63/1.17  tff(f_27, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 1.63/1.17  tff(f_31, axiom, (![A, B, C]: (k4_xboole_0(A, k3_xboole_0(B, C)) = k2_xboole_0(k4_xboole_0(A, B), k4_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t54_xboole_1)).
% 1.63/1.17  tff(f_29, axiom, (![A, B, C]: (k4_xboole_0(A, k2_xboole_0(B, C)) = k3_xboole_0(k4_xboole_0(A, B), k4_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t53_xboole_1)).
% 1.63/1.17  tff(f_34, negated_conjecture, ~(![A, B, C]: (k3_xboole_0(A, k3_xboole_0(B, C)) = k3_xboole_0(k3_xboole_0(A, B), k3_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t116_xboole_1)).
% 1.63/1.17  tff(c_2, plain, (![A_1, B_2]: (k4_xboole_0(A_1, k4_xboole_0(A_1, B_2))=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.63/1.17  tff(c_6, plain, (![A_6, B_7, C_8]: (k2_xboole_0(k4_xboole_0(A_6, B_7), k4_xboole_0(A_6, C_8))=k4_xboole_0(A_6, k3_xboole_0(B_7, C_8)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.63/1.17  tff(c_58, plain, (![A_16, B_17, C_18]: (k3_xboole_0(k4_xboole_0(A_16, B_17), k4_xboole_0(A_16, C_18))=k4_xboole_0(A_16, k2_xboole_0(B_17, C_18)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.63/1.17  tff(c_127, plain, (![A_21, B_22, B_23]: (k4_xboole_0(A_21, k2_xboole_0(B_22, k4_xboole_0(A_21, B_23)))=k3_xboole_0(k4_xboole_0(A_21, B_22), k3_xboole_0(A_21, B_23)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_58])).
% 1.63/1.17  tff(c_163, plain, (![A_6, B_7, C_8]: (k3_xboole_0(k4_xboole_0(A_6, k4_xboole_0(A_6, B_7)), k3_xboole_0(A_6, C_8))=k4_xboole_0(A_6, k4_xboole_0(A_6, k3_xboole_0(B_7, C_8))))), inference(superposition, [status(thm), theory('equality')], [c_6, c_127])).
% 1.63/1.17  tff(c_172, plain, (![A_6, B_7, C_8]: (k3_xboole_0(k3_xboole_0(A_6, B_7), k3_xboole_0(A_6, C_8))=k3_xboole_0(A_6, k3_xboole_0(B_7, C_8)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_2, c_163])).
% 1.63/1.17  tff(c_8, plain, (k3_xboole_0(k3_xboole_0('#skF_1', '#skF_2'), k3_xboole_0('#skF_1', '#skF_3'))!=k3_xboole_0('#skF_1', k3_xboole_0('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.63/1.17  tff(c_175, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_172, c_8])).
% 1.63/1.17  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.63/1.17  
% 1.63/1.17  Inference rules
% 1.63/1.17  ----------------------
% 1.63/1.17  #Ref     : 0
% 1.63/1.17  #Sup     : 47
% 1.63/1.17  #Fact    : 0
% 1.63/1.17  #Define  : 0
% 1.63/1.17  #Split   : 0
% 1.63/1.17  #Chain   : 0
% 1.63/1.17  #Close   : 0
% 1.63/1.17  
% 1.63/1.17  Ordering : KBO
% 1.63/1.17  
% 1.63/1.17  Simplification rules
% 1.63/1.17  ----------------------
% 1.63/1.17  #Subsume      : 0
% 1.63/1.17  #Demod        : 6
% 1.63/1.17  #Tautology    : 15
% 1.63/1.17  #SimpNegUnit  : 0
% 1.63/1.17  #BackRed      : 1
% 1.63/1.17  
% 1.63/1.17  #Partial instantiations: 0
% 1.63/1.17  #Strategies tried      : 1
% 1.63/1.17  
% 1.63/1.17  Timing (in seconds)
% 1.63/1.17  ----------------------
% 1.63/1.18  Preprocessing        : 0.23
% 1.63/1.18  Parsing              : 0.12
% 1.63/1.18  CNF conversion       : 0.01
% 1.63/1.18  Main loop            : 0.15
% 1.63/1.18  Inferencing          : 0.07
% 1.63/1.18  Reduction            : 0.04
% 1.63/1.18  Demodulation         : 0.04
% 1.63/1.18  BG Simplification    : 0.01
% 1.83/1.18  Subsumption          : 0.02
% 1.83/1.18  Abstraction          : 0.01
% 1.83/1.18  MUC search           : 0.00
% 1.83/1.18  Cooper               : 0.00
% 1.83/1.18  Total                : 0.41
% 1.83/1.18  Index Insertion      : 0.00
% 1.83/1.18  Index Deletion       : 0.00
% 1.83/1.18  Index Matching       : 0.00
% 1.83/1.18  BG Taut test         : 0.00
%------------------------------------------------------------------------------

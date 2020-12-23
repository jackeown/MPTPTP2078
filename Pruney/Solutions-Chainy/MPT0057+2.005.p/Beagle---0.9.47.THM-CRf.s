%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:43:02 EST 2020

% Result     : Theorem 4.24s
% Output     : CNFRefutation 4.24s
% Verified   : 
% Statistics : Number of formulae       :   24 (  34 expanded)
%              Number of leaves         :   12 (  17 expanded)
%              Depth                    :    6
%              Number of atoms          :   16 (  26 expanded)
%              Number of equality atoms :   15 (  25 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k4_xboole_0 > k3_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1

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

tff(f_31,axiom,(
    ! [A,B,C] : k3_xboole_0(A,k4_xboole_0(B,C)) = k4_xboole_0(k3_xboole_0(A,B),C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_29,axiom,(
    ! [A,B] : k4_xboole_0(A,k3_xboole_0(A,B)) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

tff(f_34,negated_conjecture,(
    ~ ! [A,B,C] : k3_xboole_0(A,k4_xboole_0(B,C)) = k4_xboole_0(k3_xboole_0(A,B),k3_xboole_0(A,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_xboole_1)).

tff(c_6,plain,(
    ! [A_5,B_6,C_7] : k4_xboole_0(k3_xboole_0(A_5,B_6),C_7) = k3_xboole_0(A_5,k4_xboole_0(B_6,C_7)) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_86,plain,(
    ! [A_14,B_15,C_16] : k4_xboole_0(k3_xboole_0(A_14,B_15),C_16) = k3_xboole_0(A_14,k4_xboole_0(B_15,C_16)) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_121,plain,(
    ! [B_17,A_18,C_19] : k4_xboole_0(k3_xboole_0(B_17,A_18),C_19) = k3_xboole_0(A_18,k4_xboole_0(B_17,C_19)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_86])).

tff(c_141,plain,(
    ! [B_6,A_5,C_7] : k3_xboole_0(B_6,k4_xboole_0(A_5,C_7)) = k3_xboole_0(A_5,k4_xboole_0(B_6,C_7)) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_121])).

tff(c_4,plain,(
    ! [A_3,B_4] : k4_xboole_0(A_3,k3_xboole_0(A_3,B_4)) = k4_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_165,plain,(
    ! [B_20,A_21,C_22] : k3_xboole_0(B_20,k4_xboole_0(A_21,C_22)) = k3_xboole_0(A_21,k4_xboole_0(B_20,C_22)) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_121])).

tff(c_249,plain,(
    ! [A_3,A_21,B_4] : k3_xboole_0(A_3,k4_xboole_0(A_21,k3_xboole_0(A_3,B_4))) = k3_xboole_0(A_21,k4_xboole_0(A_3,B_4)) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_165])).

tff(c_8,plain,(
    k4_xboole_0(k3_xboole_0('#skF_1','#skF_2'),k3_xboole_0('#skF_1','#skF_3')) != k3_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_9,plain,(
    k3_xboole_0('#skF_1',k4_xboole_0('#skF_2',k3_xboole_0('#skF_1','#skF_3'))) != k3_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_8])).

tff(c_2360,plain,(
    k3_xboole_0('#skF_2',k4_xboole_0('#skF_1','#skF_3')) != k3_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_249,c_9])).

tff(c_2363,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_141,c_2360])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:32:29 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.24/1.76  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.24/1.76  
% 4.24/1.76  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.24/1.76  %$ k4_xboole_0 > k3_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1
% 4.24/1.76  
% 4.24/1.76  %Foreground sorts:
% 4.24/1.76  
% 4.24/1.76  
% 4.24/1.76  %Background operators:
% 4.24/1.76  
% 4.24/1.76  
% 4.24/1.76  %Foreground operators:
% 4.24/1.76  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.24/1.76  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.24/1.76  tff('#skF_2', type, '#skF_2': $i).
% 4.24/1.76  tff('#skF_3', type, '#skF_3': $i).
% 4.24/1.76  tff('#skF_1', type, '#skF_1': $i).
% 4.24/1.76  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.24/1.76  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.24/1.76  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.24/1.76  
% 4.24/1.77  tff(f_31, axiom, (![A, B, C]: (k3_xboole_0(A, k4_xboole_0(B, C)) = k4_xboole_0(k3_xboole_0(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_xboole_1)).
% 4.24/1.77  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 4.24/1.77  tff(f_29, axiom, (![A, B]: (k4_xboole_0(A, k3_xboole_0(A, B)) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_xboole_1)).
% 4.24/1.77  tff(f_34, negated_conjecture, ~(![A, B, C]: (k3_xboole_0(A, k4_xboole_0(B, C)) = k4_xboole_0(k3_xboole_0(A, B), k3_xboole_0(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_xboole_1)).
% 4.24/1.77  tff(c_6, plain, (![A_5, B_6, C_7]: (k4_xboole_0(k3_xboole_0(A_5, B_6), C_7)=k3_xboole_0(A_5, k4_xboole_0(B_6, C_7)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.24/1.77  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.24/1.77  tff(c_86, plain, (![A_14, B_15, C_16]: (k4_xboole_0(k3_xboole_0(A_14, B_15), C_16)=k3_xboole_0(A_14, k4_xboole_0(B_15, C_16)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.24/1.77  tff(c_121, plain, (![B_17, A_18, C_19]: (k4_xboole_0(k3_xboole_0(B_17, A_18), C_19)=k3_xboole_0(A_18, k4_xboole_0(B_17, C_19)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_86])).
% 4.24/1.77  tff(c_141, plain, (![B_6, A_5, C_7]: (k3_xboole_0(B_6, k4_xboole_0(A_5, C_7))=k3_xboole_0(A_5, k4_xboole_0(B_6, C_7)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_121])).
% 4.24/1.77  tff(c_4, plain, (![A_3, B_4]: (k4_xboole_0(A_3, k3_xboole_0(A_3, B_4))=k4_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.24/1.77  tff(c_165, plain, (![B_20, A_21, C_22]: (k3_xboole_0(B_20, k4_xboole_0(A_21, C_22))=k3_xboole_0(A_21, k4_xboole_0(B_20, C_22)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_121])).
% 4.24/1.77  tff(c_249, plain, (![A_3, A_21, B_4]: (k3_xboole_0(A_3, k4_xboole_0(A_21, k3_xboole_0(A_3, B_4)))=k3_xboole_0(A_21, k4_xboole_0(A_3, B_4)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_165])).
% 4.24/1.77  tff(c_8, plain, (k4_xboole_0(k3_xboole_0('#skF_1', '#skF_2'), k3_xboole_0('#skF_1', '#skF_3'))!=k3_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_34])).
% 4.24/1.77  tff(c_9, plain, (k3_xboole_0('#skF_1', k4_xboole_0('#skF_2', k3_xboole_0('#skF_1', '#skF_3')))!=k3_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_8])).
% 4.24/1.77  tff(c_2360, plain, (k3_xboole_0('#skF_2', k4_xboole_0('#skF_1', '#skF_3'))!=k3_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_249, c_9])).
% 4.24/1.77  tff(c_2363, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_141, c_2360])).
% 4.24/1.77  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.24/1.77  
% 4.24/1.77  Inference rules
% 4.24/1.77  ----------------------
% 4.24/1.77  #Ref     : 0
% 4.24/1.77  #Sup     : 610
% 4.24/1.77  #Fact    : 0
% 4.24/1.77  #Define  : 0
% 4.24/1.77  #Split   : 0
% 4.24/1.77  #Chain   : 0
% 4.24/1.77  #Close   : 0
% 4.24/1.77  
% 4.24/1.77  Ordering : KBO
% 4.24/1.77  
% 4.24/1.77  Simplification rules
% 4.24/1.77  ----------------------
% 4.24/1.77  #Subsume      : 100
% 4.24/1.77  #Demod        : 301
% 4.24/1.77  #Tautology    : 109
% 4.24/1.77  #SimpNegUnit  : 0
% 4.24/1.77  #BackRed      : 1
% 4.24/1.77  
% 4.24/1.77  #Partial instantiations: 0
% 4.24/1.77  #Strategies tried      : 1
% 4.24/1.77  
% 4.24/1.77  Timing (in seconds)
% 4.24/1.77  ----------------------
% 4.57/1.77  Preprocessing        : 0.26
% 4.57/1.77  Parsing              : 0.14
% 4.57/1.77  CNF conversion       : 0.01
% 4.57/1.77  Main loop            : 0.75
% 4.57/1.77  Inferencing          : 0.21
% 4.57/1.77  Reduction            : 0.38
% 4.57/1.77  Demodulation         : 0.34
% 4.57/1.77  BG Simplification    : 0.04
% 4.57/1.77  Subsumption          : 0.09
% 4.57/1.77  Abstraction          : 0.05
% 4.57/1.77  MUC search           : 0.00
% 4.57/1.77  Cooper               : 0.00
% 4.57/1.77  Total                : 1.03
% 4.57/1.77  Index Insertion      : 0.00
% 4.57/1.77  Index Deletion       : 0.00
% 4.57/1.77  Index Matching       : 0.00
% 4.57/1.77  BG Taut test         : 0.00
%------------------------------------------------------------------------------

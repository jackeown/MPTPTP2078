%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:45:37 EST 2020

% Result     : Theorem 3.67s
% Output     : CNFRefutation 3.67s
% Verified   : 
% Statistics : Number of formulae       :   37 (  39 expanded)
%              Number of leaves         :   18 (  20 expanded)
%              Depth                    :    7
%              Number of atoms          :   34 (  37 expanded)
%              Number of equality atoms :   22 (  24 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(f_50,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_tarski(C,B)
       => k4_xboole_0(A,C) = k2_xboole_0(k4_xboole_0(A,B),k3_xboole_0(A,k4_xboole_0(B,C))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t117_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

tff(f_33,axiom,(
    ! [A,B] : k3_xboole_0(A,k2_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_xboole_1)).

tff(f_45,axiom,(
    ! [A,B,C] : k4_xboole_0(A,k4_xboole_0(B,C)) = k2_xboole_0(k4_xboole_0(A,B),k3_xboole_0(A,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => B = k2_xboole_0(A,k4_xboole_0(B,A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] : k4_xboole_0(k2_xboole_0(A,B),B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).

tff(c_20,plain,(
    r1_tarski('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_8,plain,(
    ! [A_7,B_8] : r1_tarski(k4_xboole_0(A_7,B_8),A_7) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_53,plain,(
    ! [A_25,B_26] :
      ( k2_xboole_0(A_25,B_26) = B_26
      | ~ r1_tarski(A_25,B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_60,plain,(
    ! [A_7,B_8] : k2_xboole_0(k4_xboole_0(A_7,B_8),A_7) = A_7 ),
    inference(resolution,[status(thm)],[c_8,c_53])).

tff(c_2,plain,(
    ! [A_1] : k2_xboole_0(A_1,A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_32,plain,(
    ! [A_22,B_23] : k3_xboole_0(A_22,k2_xboole_0(A_22,B_23)) = A_22 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_41,plain,(
    ! [A_1] : k3_xboole_0(A_1,A_1) = A_1 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_32])).

tff(c_477,plain,(
    ! [A_52,B_53,C_54] : k2_xboole_0(k4_xboole_0(A_52,B_53),k3_xboole_0(A_52,C_54)) = k4_xboole_0(A_52,k4_xboole_0(B_53,C_54)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_528,plain,(
    ! [A_1,B_53] : k4_xboole_0(A_1,k4_xboole_0(B_53,A_1)) = k2_xboole_0(k4_xboole_0(A_1,B_53),A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_41,c_477])).

tff(c_538,plain,(
    ! [A_1,B_53] : k4_xboole_0(A_1,k4_xboole_0(B_53,A_1)) = A_1 ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_528])).

tff(c_136,plain,(
    ! [A_31,B_32] :
      ( k2_xboole_0(A_31,k4_xboole_0(B_32,A_31)) = B_32
      | ~ r1_tarski(A_31,B_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_10,plain,(
    ! [A_9,B_10] : k4_xboole_0(k2_xboole_0(A_9,B_10),B_10) = k4_xboole_0(A_9,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_142,plain,(
    ! [B_32,A_31] :
      ( k4_xboole_0(B_32,k4_xboole_0(B_32,A_31)) = k4_xboole_0(A_31,k4_xboole_0(B_32,A_31))
      | ~ r1_tarski(A_31,B_32) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_136,c_10])).

tff(c_2626,plain,(
    ! [B_93,A_94] :
      ( k4_xboole_0(B_93,k4_xboole_0(B_93,A_94)) = A_94
      | ~ r1_tarski(A_94,B_93) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_538,c_142])).

tff(c_16,plain,(
    ! [A_16,B_17,C_18] : k2_xboole_0(k4_xboole_0(A_16,B_17),k3_xboole_0(A_16,C_18)) = k4_xboole_0(A_16,k4_xboole_0(B_17,C_18)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_18,plain,(
    k2_xboole_0(k4_xboole_0('#skF_1','#skF_2'),k3_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_3'))) != k4_xboole_0('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_21,plain,(
    k4_xboole_0('#skF_1',k4_xboole_0('#skF_2',k4_xboole_0('#skF_2','#skF_3'))) != k4_xboole_0('#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_18])).

tff(c_2723,plain,(
    ~ r1_tarski('#skF_3','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_2626,c_21])).

tff(c_2823,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_2723])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n001.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 12:23:59 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.67/1.63  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.67/1.64  
% 3.67/1.64  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.67/1.64  %$ r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1
% 3.67/1.64  
% 3.67/1.64  %Foreground sorts:
% 3.67/1.64  
% 3.67/1.64  
% 3.67/1.64  %Background operators:
% 3.67/1.64  
% 3.67/1.64  
% 3.67/1.64  %Foreground operators:
% 3.67/1.64  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.67/1.64  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.67/1.64  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.67/1.64  tff('#skF_2', type, '#skF_2': $i).
% 3.67/1.64  tff('#skF_3', type, '#skF_3': $i).
% 3.67/1.64  tff('#skF_1', type, '#skF_1': $i).
% 3.67/1.64  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.67/1.64  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.67/1.64  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.67/1.64  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.67/1.64  
% 3.67/1.65  tff(f_50, negated_conjecture, ~(![A, B, C]: (r1_tarski(C, B) => (k4_xboole_0(A, C) = k2_xboole_0(k4_xboole_0(A, B), k3_xboole_0(A, k4_xboole_0(B, C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t117_xboole_1)).
% 3.67/1.65  tff(f_35, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 3.67/1.65  tff(f_31, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 3.67/1.65  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 3.67/1.65  tff(f_33, axiom, (![A, B]: (k3_xboole_0(A, k2_xboole_0(A, B)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_xboole_1)).
% 3.67/1.65  tff(f_45, axiom, (![A, B, C]: (k4_xboole_0(A, k4_xboole_0(B, C)) = k2_xboole_0(k4_xboole_0(A, B), k3_xboole_0(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_xboole_1)).
% 3.67/1.65  tff(f_41, axiom, (![A, B]: (r1_tarski(A, B) => (B = k2_xboole_0(A, k4_xboole_0(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t45_xboole_1)).
% 3.67/1.65  tff(f_37, axiom, (![A, B]: (k4_xboole_0(k2_xboole_0(A, B), B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t40_xboole_1)).
% 3.67/1.65  tff(c_20, plain, (r1_tarski('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.67/1.65  tff(c_8, plain, (![A_7, B_8]: (r1_tarski(k4_xboole_0(A_7, B_8), A_7))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.67/1.65  tff(c_53, plain, (![A_25, B_26]: (k2_xboole_0(A_25, B_26)=B_26 | ~r1_tarski(A_25, B_26))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.67/1.65  tff(c_60, plain, (![A_7, B_8]: (k2_xboole_0(k4_xboole_0(A_7, B_8), A_7)=A_7)), inference(resolution, [status(thm)], [c_8, c_53])).
% 3.67/1.65  tff(c_2, plain, (![A_1]: (k2_xboole_0(A_1, A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.67/1.65  tff(c_32, plain, (![A_22, B_23]: (k3_xboole_0(A_22, k2_xboole_0(A_22, B_23))=A_22)), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.67/1.65  tff(c_41, plain, (![A_1]: (k3_xboole_0(A_1, A_1)=A_1)), inference(superposition, [status(thm), theory('equality')], [c_2, c_32])).
% 3.67/1.65  tff(c_477, plain, (![A_52, B_53, C_54]: (k2_xboole_0(k4_xboole_0(A_52, B_53), k3_xboole_0(A_52, C_54))=k4_xboole_0(A_52, k4_xboole_0(B_53, C_54)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.67/1.65  tff(c_528, plain, (![A_1, B_53]: (k4_xboole_0(A_1, k4_xboole_0(B_53, A_1))=k2_xboole_0(k4_xboole_0(A_1, B_53), A_1))), inference(superposition, [status(thm), theory('equality')], [c_41, c_477])).
% 3.67/1.65  tff(c_538, plain, (![A_1, B_53]: (k4_xboole_0(A_1, k4_xboole_0(B_53, A_1))=A_1)), inference(demodulation, [status(thm), theory('equality')], [c_60, c_528])).
% 3.67/1.65  tff(c_136, plain, (![A_31, B_32]: (k2_xboole_0(A_31, k4_xboole_0(B_32, A_31))=B_32 | ~r1_tarski(A_31, B_32))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.67/1.65  tff(c_10, plain, (![A_9, B_10]: (k4_xboole_0(k2_xboole_0(A_9, B_10), B_10)=k4_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.67/1.65  tff(c_142, plain, (![B_32, A_31]: (k4_xboole_0(B_32, k4_xboole_0(B_32, A_31))=k4_xboole_0(A_31, k4_xboole_0(B_32, A_31)) | ~r1_tarski(A_31, B_32))), inference(superposition, [status(thm), theory('equality')], [c_136, c_10])).
% 3.67/1.65  tff(c_2626, plain, (![B_93, A_94]: (k4_xboole_0(B_93, k4_xboole_0(B_93, A_94))=A_94 | ~r1_tarski(A_94, B_93))), inference(demodulation, [status(thm), theory('equality')], [c_538, c_142])).
% 3.67/1.65  tff(c_16, plain, (![A_16, B_17, C_18]: (k2_xboole_0(k4_xboole_0(A_16, B_17), k3_xboole_0(A_16, C_18))=k4_xboole_0(A_16, k4_xboole_0(B_17, C_18)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.67/1.65  tff(c_18, plain, (k2_xboole_0(k4_xboole_0('#skF_1', '#skF_2'), k3_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_3')))!=k4_xboole_0('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.67/1.65  tff(c_21, plain, (k4_xboole_0('#skF_1', k4_xboole_0('#skF_2', k4_xboole_0('#skF_2', '#skF_3')))!=k4_xboole_0('#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_16, c_18])).
% 3.67/1.65  tff(c_2723, plain, (~r1_tarski('#skF_3', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_2626, c_21])).
% 3.67/1.65  tff(c_2823, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_20, c_2723])).
% 3.67/1.65  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.67/1.65  
% 3.67/1.65  Inference rules
% 3.67/1.65  ----------------------
% 3.67/1.65  #Ref     : 0
% 3.67/1.65  #Sup     : 722
% 3.67/1.65  #Fact    : 0
% 3.67/1.65  #Define  : 0
% 3.67/1.65  #Split   : 1
% 3.67/1.65  #Chain   : 0
% 3.67/1.65  #Close   : 0
% 3.67/1.65  
% 3.67/1.65  Ordering : KBO
% 3.67/1.65  
% 3.67/1.65  Simplification rules
% 3.67/1.65  ----------------------
% 3.67/1.65  #Subsume      : 15
% 3.67/1.65  #Demod        : 474
% 3.67/1.65  #Tautology    : 408
% 3.67/1.65  #SimpNegUnit  : 0
% 3.67/1.65  #BackRed      : 10
% 3.67/1.65  
% 3.67/1.65  #Partial instantiations: 0
% 3.67/1.65  #Strategies tried      : 1
% 3.67/1.65  
% 3.67/1.65  Timing (in seconds)
% 3.67/1.65  ----------------------
% 3.67/1.65  Preprocessing        : 0.29
% 3.67/1.65  Parsing              : 0.16
% 3.67/1.65  CNF conversion       : 0.02
% 3.67/1.65  Main loop            : 0.61
% 3.67/1.65  Inferencing          : 0.21
% 3.67/1.65  Reduction            : 0.23
% 3.67/1.65  Demodulation         : 0.18
% 3.67/1.65  BG Simplification    : 0.03
% 3.67/1.65  Subsumption          : 0.10
% 3.67/1.65  Abstraction          : 0.04
% 3.67/1.65  MUC search           : 0.00
% 3.67/1.65  Cooper               : 0.00
% 3.67/1.65  Total                : 0.92
% 3.67/1.65  Index Insertion      : 0.00
% 3.67/1.65  Index Deletion       : 0.00
% 3.67/1.65  Index Matching       : 0.00
% 3.67/1.65  BG Taut test         : 0.00
%------------------------------------------------------------------------------

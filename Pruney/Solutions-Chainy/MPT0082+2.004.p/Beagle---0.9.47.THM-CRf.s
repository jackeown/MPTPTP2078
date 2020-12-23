%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:43:59 EST 2020

% Result     : Theorem 1.89s
% Output     : CNFRefutation 1.96s
% Verified   : 
% Statistics : Number of formulae       :   40 (  83 expanded)
%              Number of leaves         :   15 (  35 expanded)
%              Depth                    :    9
%              Number of atoms          :   37 (  88 expanded)
%              Number of equality atoms :   24 (  62 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

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

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_46,negated_conjecture,(
    ~ ! [A,B] :
        ~ ( ~ r1_xboole_0(A,B)
          & r1_xboole_0(k3_xboole_0(A,B),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_39,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] : k4_xboole_0(A,k3_xboole_0(A,B)) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(c_91,plain,(
    ! [A_17,B_18] :
      ( r1_xboole_0(A_17,B_18)
      | k3_xboole_0(A_17,B_18) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_16,plain,(
    ~ r1_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_102,plain,(
    k3_xboole_0('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_91,c_16])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_12,plain,(
    ! [A_9,B_10] : k4_xboole_0(A_9,k4_xboole_0(A_9,B_10)) = k3_xboole_0(A_9,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_116,plain,(
    ! [A_21,B_22] : k4_xboole_0(A_21,k3_xboole_0(A_21,B_22)) = k4_xboole_0(A_21,B_22) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_131,plain,(
    ! [A_1,B_2] : k4_xboole_0(A_1,k3_xboole_0(B_2,A_1)) = k4_xboole_0(A_1,B_2) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_116])).

tff(c_14,plain,(
    r1_xboole_0(k3_xboole_0('#skF_1','#skF_2'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_58,plain,(
    ! [A_15,B_16] :
      ( k3_xboole_0(A_15,B_16) = k1_xboole_0
      | ~ r1_xboole_0(A_15,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_66,plain,(
    k3_xboole_0(k3_xboole_0('#skF_1','#skF_2'),'#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_14,c_58])).

tff(c_158,plain,(
    ! [A_25,B_26] : k4_xboole_0(A_25,k3_xboole_0(B_26,A_25)) = k4_xboole_0(A_25,B_26) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_116])).

tff(c_181,plain,(
    k4_xboole_0('#skF_2',k3_xboole_0('#skF_1','#skF_2')) = k4_xboole_0('#skF_2',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_66,c_158])).

tff(c_193,plain,(
    k4_xboole_0('#skF_2',k1_xboole_0) = k4_xboole_0('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_131,c_181])).

tff(c_199,plain,(
    k4_xboole_0('#skF_2',k4_xboole_0('#skF_2','#skF_1')) = k3_xboole_0('#skF_2',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_193,c_12])).

tff(c_202,plain,(
    k3_xboole_0('#skF_2',k1_xboole_0) = k3_xboole_0('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_12,c_199])).

tff(c_50,plain,(
    ! [B_13,A_14] :
      ( r1_xboole_0(B_13,A_14)
      | ~ r1_xboole_0(A_14,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_53,plain,(
    r1_xboole_0('#skF_2',k3_xboole_0('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_14,c_50])).

tff(c_65,plain,(
    k3_xboole_0('#skF_2',k3_xboole_0('#skF_1','#skF_2')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_53,c_58])).

tff(c_10,plain,(
    ! [A_7,B_8] : k4_xboole_0(A_7,k3_xboole_0(A_7,B_8)) = k4_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_137,plain,(
    ! [A_23,B_24] : k4_xboole_0(A_23,k4_xboole_0(A_23,B_24)) = k3_xboole_0(A_23,B_24) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_152,plain,(
    ! [A_7,B_8] : k4_xboole_0(A_7,k4_xboole_0(A_7,B_8)) = k3_xboole_0(A_7,k3_xboole_0(A_7,B_8)) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_137])).

tff(c_234,plain,(
    ! [A_27,B_28] : k3_xboole_0(A_27,k3_xboole_0(A_27,B_28)) = k3_xboole_0(A_27,B_28) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_152])).

tff(c_258,plain,(
    k3_xboole_0('#skF_2',k3_xboole_0('#skF_1','#skF_2')) = k3_xboole_0('#skF_2',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_202,c_234])).

tff(c_277,plain,(
    k3_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_202,c_65,c_258])).

tff(c_279,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_102,c_277])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:44:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.89/1.19  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.89/1.19  
% 1.89/1.19  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.89/1.20  %$ r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1
% 1.89/1.20  
% 1.89/1.20  %Foreground sorts:
% 1.89/1.20  
% 1.89/1.20  
% 1.89/1.20  %Background operators:
% 1.89/1.20  
% 1.89/1.20  
% 1.89/1.20  %Foreground operators:
% 1.89/1.20  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.89/1.20  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.89/1.20  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.89/1.20  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.89/1.20  tff('#skF_2', type, '#skF_2': $i).
% 1.89/1.20  tff('#skF_1', type, '#skF_1': $i).
% 1.89/1.20  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.89/1.20  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.89/1.20  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.89/1.20  
% 1.96/1.21  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 1.96/1.21  tff(f_46, negated_conjecture, ~(![A, B]: ~(~r1_xboole_0(A, B) & r1_xboole_0(k3_xboole_0(A, B), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t75_xboole_1)).
% 1.96/1.21  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 1.96/1.21  tff(f_39, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 1.96/1.21  tff(f_37, axiom, (![A, B]: (k4_xboole_0(A, k3_xboole_0(A, B)) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_xboole_1)).
% 1.96/1.21  tff(f_35, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 1.96/1.21  tff(c_91, plain, (![A_17, B_18]: (r1_xboole_0(A_17, B_18) | k3_xboole_0(A_17, B_18)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.96/1.21  tff(c_16, plain, (~r1_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.96/1.21  tff(c_102, plain, (k3_xboole_0('#skF_1', '#skF_2')!=k1_xboole_0), inference(resolution, [status(thm)], [c_91, c_16])).
% 1.96/1.21  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.96/1.21  tff(c_12, plain, (![A_9, B_10]: (k4_xboole_0(A_9, k4_xboole_0(A_9, B_10))=k3_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.96/1.21  tff(c_116, plain, (![A_21, B_22]: (k4_xboole_0(A_21, k3_xboole_0(A_21, B_22))=k4_xboole_0(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.96/1.21  tff(c_131, plain, (![A_1, B_2]: (k4_xboole_0(A_1, k3_xboole_0(B_2, A_1))=k4_xboole_0(A_1, B_2))), inference(superposition, [status(thm), theory('equality')], [c_2, c_116])).
% 1.96/1.21  tff(c_14, plain, (r1_xboole_0(k3_xboole_0('#skF_1', '#skF_2'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.96/1.21  tff(c_58, plain, (![A_15, B_16]: (k3_xboole_0(A_15, B_16)=k1_xboole_0 | ~r1_xboole_0(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.96/1.21  tff(c_66, plain, (k3_xboole_0(k3_xboole_0('#skF_1', '#skF_2'), '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_14, c_58])).
% 1.96/1.21  tff(c_158, plain, (![A_25, B_26]: (k4_xboole_0(A_25, k3_xboole_0(B_26, A_25))=k4_xboole_0(A_25, B_26))), inference(superposition, [status(thm), theory('equality')], [c_2, c_116])).
% 1.96/1.21  tff(c_181, plain, (k4_xboole_0('#skF_2', k3_xboole_0('#skF_1', '#skF_2'))=k4_xboole_0('#skF_2', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_66, c_158])).
% 1.96/1.21  tff(c_193, plain, (k4_xboole_0('#skF_2', k1_xboole_0)=k4_xboole_0('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_131, c_181])).
% 1.96/1.21  tff(c_199, plain, (k4_xboole_0('#skF_2', k4_xboole_0('#skF_2', '#skF_1'))=k3_xboole_0('#skF_2', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_193, c_12])).
% 1.96/1.21  tff(c_202, plain, (k3_xboole_0('#skF_2', k1_xboole_0)=k3_xboole_0('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_12, c_199])).
% 1.96/1.21  tff(c_50, plain, (![B_13, A_14]: (r1_xboole_0(B_13, A_14) | ~r1_xboole_0(A_14, B_13))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.96/1.21  tff(c_53, plain, (r1_xboole_0('#skF_2', k3_xboole_0('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_14, c_50])).
% 1.96/1.21  tff(c_65, plain, (k3_xboole_0('#skF_2', k3_xboole_0('#skF_1', '#skF_2'))=k1_xboole_0), inference(resolution, [status(thm)], [c_53, c_58])).
% 1.96/1.21  tff(c_10, plain, (![A_7, B_8]: (k4_xboole_0(A_7, k3_xboole_0(A_7, B_8))=k4_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.96/1.21  tff(c_137, plain, (![A_23, B_24]: (k4_xboole_0(A_23, k4_xboole_0(A_23, B_24))=k3_xboole_0(A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.96/1.21  tff(c_152, plain, (![A_7, B_8]: (k4_xboole_0(A_7, k4_xboole_0(A_7, B_8))=k3_xboole_0(A_7, k3_xboole_0(A_7, B_8)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_137])).
% 1.96/1.21  tff(c_234, plain, (![A_27, B_28]: (k3_xboole_0(A_27, k3_xboole_0(A_27, B_28))=k3_xboole_0(A_27, B_28))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_152])).
% 1.96/1.21  tff(c_258, plain, (k3_xboole_0('#skF_2', k3_xboole_0('#skF_1', '#skF_2'))=k3_xboole_0('#skF_2', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_202, c_234])).
% 1.96/1.21  tff(c_277, plain, (k3_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_202, c_65, c_258])).
% 1.96/1.21  tff(c_279, plain, $false, inference(negUnitSimplification, [status(thm)], [c_102, c_277])).
% 1.96/1.21  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.96/1.21  
% 1.96/1.21  Inference rules
% 1.96/1.21  ----------------------
% 1.96/1.21  #Ref     : 0
% 1.96/1.21  #Sup     : 72
% 1.96/1.21  #Fact    : 0
% 1.96/1.21  #Define  : 0
% 1.96/1.21  #Split   : 0
% 1.96/1.21  #Chain   : 0
% 1.96/1.21  #Close   : 0
% 1.96/1.21  
% 1.96/1.21  Ordering : KBO
% 1.96/1.21  
% 1.96/1.21  Simplification rules
% 1.96/1.21  ----------------------
% 1.96/1.21  #Subsume      : 2
% 1.96/1.21  #Demod        : 32
% 1.96/1.21  #Tautology    : 43
% 1.96/1.21  #SimpNegUnit  : 1
% 1.96/1.21  #BackRed      : 0
% 1.96/1.21  
% 1.96/1.21  #Partial instantiations: 0
% 1.96/1.21  #Strategies tried      : 1
% 1.96/1.21  
% 1.96/1.21  Timing (in seconds)
% 1.96/1.21  ----------------------
% 1.96/1.21  Preprocessing        : 0.25
% 1.96/1.21  Parsing              : 0.15
% 1.96/1.21  CNF conversion       : 0.01
% 1.96/1.21  Main loop            : 0.19
% 1.96/1.21  Inferencing          : 0.07
% 1.96/1.21  Reduction            : 0.08
% 1.96/1.21  Demodulation         : 0.07
% 1.96/1.21  BG Simplification    : 0.01
% 1.96/1.21  Subsumption          : 0.03
% 1.96/1.21  Abstraction          : 0.01
% 1.96/1.21  MUC search           : 0.00
% 1.96/1.21  Cooper               : 0.00
% 1.96/1.21  Total                : 0.47
% 1.96/1.21  Index Insertion      : 0.00
% 1.96/1.21  Index Deletion       : 0.00
% 1.96/1.21  Index Matching       : 0.00
% 1.96/1.21  BG Taut test         : 0.00
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:43:02 EST 2020

% Result     : Theorem 2.33s
% Output     : CNFRefutation 2.33s
% Verified   : 
% Statistics : Number of formulae       :   36 (  48 expanded)
%              Number of leaves         :   17 (  23 expanded)
%              Depth                    :    9
%              Number of atoms          :   28 (  42 expanded)
%              Number of equality atoms :   23 (  33 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

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
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_29,axiom,(
    ! [A,B] : k2_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

tff(f_35,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_42,negated_conjecture,(
    ~ ! [A,B] : k2_xboole_0(k3_xboole_0(A,B),k4_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_xboole_1)).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4,plain,(
    ! [A_3] : k2_xboole_0(A_3,A_3) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_10,plain,(
    ! [A_7,B_8] : r1_tarski(k4_xboole_0(A_7,B_8),A_7) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_60,plain,(
    ! [A_18,B_19] :
      ( k4_xboole_0(A_18,B_19) = k1_xboole_0
      | ~ r1_tarski(A_18,B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_64,plain,(
    ! [A_7,B_8] : k4_xboole_0(k4_xboole_0(A_7,B_8),A_7) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_10,c_60])).

tff(c_195,plain,(
    ! [A_31,B_32] : k2_xboole_0(A_31,k4_xboole_0(B_32,A_31)) = k2_xboole_0(A_31,B_32) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_348,plain,(
    ! [A_43,B_44] : k2_xboole_0(A_43,k4_xboole_0(A_43,B_44)) = k2_xboole_0(A_43,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_64,c_195])).

tff(c_12,plain,(
    ! [A_9,B_10] : k2_xboole_0(A_9,k4_xboole_0(B_10,A_9)) = k2_xboole_0(A_9,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_355,plain,(
    ! [B_44] : k2_xboole_0(B_44,k1_xboole_0) = k2_xboole_0(B_44,B_44) ),
    inference(superposition,[status(thm),theory(equality)],[c_348,c_12])).

tff(c_385,plain,(
    ! [B_44] : k2_xboole_0(B_44,k1_xboole_0) = B_44 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_355])).

tff(c_213,plain,(
    ! [A_7,B_8] : k2_xboole_0(A_7,k4_xboole_0(A_7,B_8)) = k2_xboole_0(A_7,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_64,c_195])).

tff(c_393,plain,(
    ! [A_7,B_8] : k2_xboole_0(A_7,k4_xboole_0(A_7,B_8)) = A_7 ),
    inference(demodulation,[status(thm),theory(equality)],[c_385,c_213])).

tff(c_14,plain,(
    ! [A_11,B_12] : k4_xboole_0(A_11,k4_xboole_0(A_11,B_12)) = k3_xboole_0(A_11,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_204,plain,(
    ! [A_11,B_12] : k2_xboole_0(k4_xboole_0(A_11,B_12),k3_xboole_0(A_11,B_12)) = k2_xboole_0(k4_xboole_0(A_11,B_12),A_11) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_195])).

tff(c_216,plain,(
    ! [A_11,B_12] : k2_xboole_0(k4_xboole_0(A_11,B_12),k3_xboole_0(A_11,B_12)) = k2_xboole_0(A_11,k4_xboole_0(A_11,B_12)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_204])).

tff(c_868,plain,(
    ! [A_60,B_61] : k2_xboole_0(k4_xboole_0(A_60,B_61),k3_xboole_0(A_60,B_61)) = A_60 ),
    inference(demodulation,[status(thm),theory(equality)],[c_393,c_216])).

tff(c_916,plain,(
    ! [A_60,B_61] : k2_xboole_0(k3_xboole_0(A_60,B_61),k4_xboole_0(A_60,B_61)) = A_60 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_868])).

tff(c_16,plain,(
    k2_xboole_0(k3_xboole_0('#skF_1','#skF_2'),k4_xboole_0('#skF_1','#skF_2')) != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_1060,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_916,c_16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:32:06 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.33/1.30  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.33/1.30  
% 2.33/1.30  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.33/1.30  %$ r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1
% 2.33/1.30  
% 2.33/1.30  %Foreground sorts:
% 2.33/1.30  
% 2.33/1.30  
% 2.33/1.30  %Background operators:
% 2.33/1.30  
% 2.33/1.30  
% 2.33/1.30  %Foreground operators:
% 2.33/1.30  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.33/1.30  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.33/1.30  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.33/1.30  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.33/1.30  tff('#skF_2', type, '#skF_2': $i).
% 2.33/1.30  tff('#skF_1', type, '#skF_1': $i).
% 2.33/1.30  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.33/1.30  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.33/1.30  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.33/1.30  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.33/1.30  
% 2.33/1.31  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 2.33/1.31  tff(f_29, axiom, (![A, B]: (k2_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 2.33/1.31  tff(f_35, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 2.33/1.31  tff(f_33, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 2.33/1.31  tff(f_37, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 2.33/1.31  tff(f_39, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 2.33/1.31  tff(f_42, negated_conjecture, ~(![A, B]: (k2_xboole_0(k3_xboole_0(A, B), k4_xboole_0(A, B)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t51_xboole_1)).
% 2.33/1.31  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.33/1.31  tff(c_4, plain, (![A_3]: (k2_xboole_0(A_3, A_3)=A_3)), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.33/1.31  tff(c_10, plain, (![A_7, B_8]: (r1_tarski(k4_xboole_0(A_7, B_8), A_7))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.33/1.31  tff(c_60, plain, (![A_18, B_19]: (k4_xboole_0(A_18, B_19)=k1_xboole_0 | ~r1_tarski(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.33/1.31  tff(c_64, plain, (![A_7, B_8]: (k4_xboole_0(k4_xboole_0(A_7, B_8), A_7)=k1_xboole_0)), inference(resolution, [status(thm)], [c_10, c_60])).
% 2.33/1.31  tff(c_195, plain, (![A_31, B_32]: (k2_xboole_0(A_31, k4_xboole_0(B_32, A_31))=k2_xboole_0(A_31, B_32))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.33/1.31  tff(c_348, plain, (![A_43, B_44]: (k2_xboole_0(A_43, k4_xboole_0(A_43, B_44))=k2_xboole_0(A_43, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_64, c_195])).
% 2.33/1.31  tff(c_12, plain, (![A_9, B_10]: (k2_xboole_0(A_9, k4_xboole_0(B_10, A_9))=k2_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.33/1.31  tff(c_355, plain, (![B_44]: (k2_xboole_0(B_44, k1_xboole_0)=k2_xboole_0(B_44, B_44))), inference(superposition, [status(thm), theory('equality')], [c_348, c_12])).
% 2.33/1.31  tff(c_385, plain, (![B_44]: (k2_xboole_0(B_44, k1_xboole_0)=B_44)), inference(demodulation, [status(thm), theory('equality')], [c_4, c_355])).
% 2.33/1.31  tff(c_213, plain, (![A_7, B_8]: (k2_xboole_0(A_7, k4_xboole_0(A_7, B_8))=k2_xboole_0(A_7, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_64, c_195])).
% 2.33/1.31  tff(c_393, plain, (![A_7, B_8]: (k2_xboole_0(A_7, k4_xboole_0(A_7, B_8))=A_7)), inference(demodulation, [status(thm), theory('equality')], [c_385, c_213])).
% 2.33/1.31  tff(c_14, plain, (![A_11, B_12]: (k4_xboole_0(A_11, k4_xboole_0(A_11, B_12))=k3_xboole_0(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.33/1.31  tff(c_204, plain, (![A_11, B_12]: (k2_xboole_0(k4_xboole_0(A_11, B_12), k3_xboole_0(A_11, B_12))=k2_xboole_0(k4_xboole_0(A_11, B_12), A_11))), inference(superposition, [status(thm), theory('equality')], [c_14, c_195])).
% 2.33/1.31  tff(c_216, plain, (![A_11, B_12]: (k2_xboole_0(k4_xboole_0(A_11, B_12), k3_xboole_0(A_11, B_12))=k2_xboole_0(A_11, k4_xboole_0(A_11, B_12)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_204])).
% 2.33/1.31  tff(c_868, plain, (![A_60, B_61]: (k2_xboole_0(k4_xboole_0(A_60, B_61), k3_xboole_0(A_60, B_61))=A_60)), inference(demodulation, [status(thm), theory('equality')], [c_393, c_216])).
% 2.33/1.31  tff(c_916, plain, (![A_60, B_61]: (k2_xboole_0(k3_xboole_0(A_60, B_61), k4_xboole_0(A_60, B_61))=A_60)), inference(superposition, [status(thm), theory('equality')], [c_2, c_868])).
% 2.33/1.31  tff(c_16, plain, (k2_xboole_0(k3_xboole_0('#skF_1', '#skF_2'), k4_xboole_0('#skF_1', '#skF_2'))!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.33/1.31  tff(c_1060, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_916, c_16])).
% 2.33/1.31  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.33/1.31  
% 2.33/1.31  Inference rules
% 2.33/1.31  ----------------------
% 2.33/1.31  #Ref     : 0
% 2.33/1.31  #Sup     : 254
% 2.33/1.31  #Fact    : 0
% 2.33/1.31  #Define  : 0
% 2.33/1.31  #Split   : 0
% 2.33/1.31  #Chain   : 0
% 2.33/1.31  #Close   : 0
% 2.33/1.31  
% 2.33/1.31  Ordering : KBO
% 2.33/1.31  
% 2.33/1.31  Simplification rules
% 2.33/1.31  ----------------------
% 2.33/1.31  #Subsume      : 0
% 2.33/1.31  #Demod        : 220
% 2.33/1.31  #Tautology    : 214
% 2.33/1.31  #SimpNegUnit  : 0
% 2.33/1.31  #BackRed      : 3
% 2.33/1.31  
% 2.33/1.31  #Partial instantiations: 0
% 2.33/1.31  #Strategies tried      : 1
% 2.33/1.31  
% 2.33/1.31  Timing (in seconds)
% 2.33/1.31  ----------------------
% 2.33/1.32  Preprocessing        : 0.25
% 2.33/1.32  Parsing              : 0.14
% 2.33/1.32  CNF conversion       : 0.01
% 2.33/1.32  Main loop            : 0.32
% 2.33/1.32  Inferencing          : 0.12
% 2.33/1.32  Reduction            : 0.13
% 2.33/1.32  Demodulation         : 0.10
% 2.33/1.32  BG Simplification    : 0.01
% 2.33/1.32  Subsumption          : 0.04
% 2.33/1.32  Abstraction          : 0.02
% 2.33/1.32  MUC search           : 0.00
% 2.33/1.32  Cooper               : 0.00
% 2.33/1.32  Total                : 0.59
% 2.33/1.32  Index Insertion      : 0.00
% 2.33/1.32  Index Deletion       : 0.00
% 2.33/1.32  Index Matching       : 0.00
% 2.33/1.32  BG Taut test         : 0.00
%------------------------------------------------------------------------------

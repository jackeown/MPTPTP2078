%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:45:32 EST 2020

% Result     : Theorem 7.58s
% Output     : CNFRefutation 7.68s
% Verified   : 
% Statistics : Number of formulae       :   36 (  49 expanded)
%              Number of leaves         :   17 (  24 expanded)
%              Depth                    :    7
%              Number of atoms          :   27 (  40 expanded)
%              Number of equality atoms :   21 (  34 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

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

tff(f_41,axiom,(
    ! [A,B,C] : k3_xboole_0(A,k4_xboole_0(B,C)) = k4_xboole_0(k3_xboole_0(A,B),C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_29,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_44,negated_conjecture,(
    ~ ! [A,B,C] : k4_xboole_0(k3_xboole_0(A,B),k3_xboole_0(C,B)) = k3_xboole_0(k4_xboole_0(A,C),B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t111_xboole_1)).

tff(c_14,plain,(
    ! [A_14,B_15,C_16] : k4_xboole_0(k3_xboole_0(A_14,B_15),C_16) = k3_xboole_0(A_14,k4_xboole_0(B_15,C_16)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_255,plain,(
    ! [A_40,B_41,C_42] : k4_xboole_0(k3_xboole_0(A_40,B_41),C_42) = k3_xboole_0(A_40,k4_xboole_0(B_41,C_42)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_1447,plain,(
    ! [B_80,A_81,C_82] : k4_xboole_0(k3_xboole_0(B_80,A_81),C_82) = k3_xboole_0(A_81,k4_xboole_0(B_80,C_82)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_255])).

tff(c_1484,plain,(
    ! [B_15,A_14,C_16] : k3_xboole_0(B_15,k4_xboole_0(A_14,C_16)) = k3_xboole_0(A_14,k4_xboole_0(B_15,C_16)) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_1447])).

tff(c_121,plain,(
    ! [A_31,B_32] : k5_xboole_0(A_31,k3_xboole_0(A_31,B_32)) = k4_xboole_0(A_31,B_32) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_136,plain,(
    ! [B_2,A_1] : k5_xboole_0(B_2,k3_xboole_0(A_1,B_2)) = k4_xboole_0(B_2,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_121])).

tff(c_33,plain,(
    ! [B_22,A_23] : k3_xboole_0(B_22,A_23) = k3_xboole_0(A_23,B_22) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_8,plain,(
    ! [A_8,B_9] : r1_tarski(k3_xboole_0(A_8,B_9),A_8) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_48,plain,(
    ! [B_22,A_23] : r1_tarski(k3_xboole_0(B_22,A_23),A_23) ),
    inference(superposition,[status(thm),theory(equality)],[c_33,c_8])).

tff(c_84,plain,(
    ! [A_26,B_27] :
      ( k3_xboole_0(A_26,B_27) = A_26
      | ~ r1_tarski(A_26,B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_1516,plain,(
    ! [B_83,A_84] : k3_xboole_0(k3_xboole_0(B_83,A_84),A_84) = k3_xboole_0(B_83,A_84) ),
    inference(resolution,[status(thm)],[c_48,c_84])).

tff(c_1585,plain,(
    ! [A_84,B_83] : k5_xboole_0(A_84,k3_xboole_0(B_83,A_84)) = k4_xboole_0(A_84,k3_xboole_0(B_83,A_84)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1516,c_136])).

tff(c_1689,plain,(
    ! [A_84,B_83] : k4_xboole_0(A_84,k3_xboole_0(B_83,A_84)) = k4_xboole_0(A_84,B_83) ),
    inference(demodulation,[status(thm),theory(equality)],[c_136,c_1585])).

tff(c_16,plain,(
    k4_xboole_0(k3_xboole_0('#skF_1','#skF_2'),k3_xboole_0('#skF_3','#skF_2')) != k3_xboole_0(k4_xboole_0('#skF_1','#skF_3'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_17,plain,(
    k3_xboole_0('#skF_1',k4_xboole_0('#skF_2',k3_xboole_0('#skF_3','#skF_2'))) != k3_xboole_0(k4_xboole_0('#skF_1','#skF_3'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_16])).

tff(c_18,plain,(
    k3_xboole_0('#skF_1',k4_xboole_0('#skF_2',k3_xboole_0('#skF_3','#skF_2'))) != k3_xboole_0('#skF_2',k4_xboole_0('#skF_1','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_17])).

tff(c_1787,plain,(
    k3_xboole_0('#skF_2',k4_xboole_0('#skF_1','#skF_3')) != k3_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1689,c_18])).

tff(c_9013,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1484,c_1787])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:45:42 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.58/2.72  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.58/2.72  
% 7.58/2.72  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.65/2.72  %$ r1_tarski > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1
% 7.65/2.72  
% 7.65/2.72  %Foreground sorts:
% 7.65/2.72  
% 7.65/2.72  
% 7.65/2.72  %Background operators:
% 7.65/2.72  
% 7.65/2.72  
% 7.65/2.72  %Foreground operators:
% 7.65/2.72  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.65/2.72  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 7.65/2.72  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 7.65/2.72  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.65/2.72  tff('#skF_2', type, '#skF_2': $i).
% 7.65/2.72  tff('#skF_3', type, '#skF_3': $i).
% 7.65/2.72  tff('#skF_1', type, '#skF_1': $i).
% 7.65/2.72  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.65/2.72  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.65/2.72  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 7.65/2.72  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 7.65/2.72  
% 7.68/2.73  tff(f_41, axiom, (![A, B, C]: (k3_xboole_0(A, k4_xboole_0(B, C)) = k4_xboole_0(k3_xboole_0(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_xboole_1)).
% 7.68/2.73  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 7.68/2.73  tff(f_29, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 7.68/2.73  tff(f_33, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 7.68/2.73  tff(f_39, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 7.68/2.73  tff(f_44, negated_conjecture, ~(![A, B, C]: (k4_xboole_0(k3_xboole_0(A, B), k3_xboole_0(C, B)) = k3_xboole_0(k4_xboole_0(A, C), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t111_xboole_1)).
% 7.68/2.73  tff(c_14, plain, (![A_14, B_15, C_16]: (k4_xboole_0(k3_xboole_0(A_14, B_15), C_16)=k3_xboole_0(A_14, k4_xboole_0(B_15, C_16)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 7.68/2.73  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 7.68/2.73  tff(c_255, plain, (![A_40, B_41, C_42]: (k4_xboole_0(k3_xboole_0(A_40, B_41), C_42)=k3_xboole_0(A_40, k4_xboole_0(B_41, C_42)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 7.68/2.73  tff(c_1447, plain, (![B_80, A_81, C_82]: (k4_xboole_0(k3_xboole_0(B_80, A_81), C_82)=k3_xboole_0(A_81, k4_xboole_0(B_80, C_82)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_255])).
% 7.68/2.73  tff(c_1484, plain, (![B_15, A_14, C_16]: (k3_xboole_0(B_15, k4_xboole_0(A_14, C_16))=k3_xboole_0(A_14, k4_xboole_0(B_15, C_16)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_1447])).
% 7.68/2.73  tff(c_121, plain, (![A_31, B_32]: (k5_xboole_0(A_31, k3_xboole_0(A_31, B_32))=k4_xboole_0(A_31, B_32))), inference(cnfTransformation, [status(thm)], [f_29])).
% 7.68/2.73  tff(c_136, plain, (![B_2, A_1]: (k5_xboole_0(B_2, k3_xboole_0(A_1, B_2))=k4_xboole_0(B_2, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_121])).
% 7.68/2.73  tff(c_33, plain, (![B_22, A_23]: (k3_xboole_0(B_22, A_23)=k3_xboole_0(A_23, B_22))), inference(cnfTransformation, [status(thm)], [f_27])).
% 7.68/2.73  tff(c_8, plain, (![A_8, B_9]: (r1_tarski(k3_xboole_0(A_8, B_9), A_8))), inference(cnfTransformation, [status(thm)], [f_33])).
% 7.68/2.73  tff(c_48, plain, (![B_22, A_23]: (r1_tarski(k3_xboole_0(B_22, A_23), A_23))), inference(superposition, [status(thm), theory('equality')], [c_33, c_8])).
% 7.68/2.73  tff(c_84, plain, (![A_26, B_27]: (k3_xboole_0(A_26, B_27)=A_26 | ~r1_tarski(A_26, B_27))), inference(cnfTransformation, [status(thm)], [f_39])).
% 7.68/2.73  tff(c_1516, plain, (![B_83, A_84]: (k3_xboole_0(k3_xboole_0(B_83, A_84), A_84)=k3_xboole_0(B_83, A_84))), inference(resolution, [status(thm)], [c_48, c_84])).
% 7.68/2.73  tff(c_1585, plain, (![A_84, B_83]: (k5_xboole_0(A_84, k3_xboole_0(B_83, A_84))=k4_xboole_0(A_84, k3_xboole_0(B_83, A_84)))), inference(superposition, [status(thm), theory('equality')], [c_1516, c_136])).
% 7.68/2.73  tff(c_1689, plain, (![A_84, B_83]: (k4_xboole_0(A_84, k3_xboole_0(B_83, A_84))=k4_xboole_0(A_84, B_83))), inference(demodulation, [status(thm), theory('equality')], [c_136, c_1585])).
% 7.68/2.73  tff(c_16, plain, (k4_xboole_0(k3_xboole_0('#skF_1', '#skF_2'), k3_xboole_0('#skF_3', '#skF_2'))!=k3_xboole_0(k4_xboole_0('#skF_1', '#skF_3'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_44])).
% 7.68/2.73  tff(c_17, plain, (k3_xboole_0('#skF_1', k4_xboole_0('#skF_2', k3_xboole_0('#skF_3', '#skF_2')))!=k3_xboole_0(k4_xboole_0('#skF_1', '#skF_3'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_14, c_16])).
% 7.68/2.73  tff(c_18, plain, (k3_xboole_0('#skF_1', k4_xboole_0('#skF_2', k3_xboole_0('#skF_3', '#skF_2')))!=k3_xboole_0('#skF_2', k4_xboole_0('#skF_1', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_17])).
% 7.68/2.73  tff(c_1787, plain, (k3_xboole_0('#skF_2', k4_xboole_0('#skF_1', '#skF_3'))!=k3_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_1689, c_18])).
% 7.68/2.73  tff(c_9013, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1484, c_1787])).
% 7.68/2.73  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.68/2.73  
% 7.68/2.73  Inference rules
% 7.68/2.73  ----------------------
% 7.68/2.73  #Ref     : 0
% 7.68/2.73  #Sup     : 2225
% 7.68/2.73  #Fact    : 0
% 7.68/2.73  #Define  : 0
% 7.68/2.73  #Split   : 0
% 7.68/2.73  #Chain   : 0
% 7.68/2.73  #Close   : 0
% 7.68/2.73  
% 7.68/2.73  Ordering : KBO
% 7.68/2.73  
% 7.68/2.73  Simplification rules
% 7.68/2.73  ----------------------
% 7.68/2.73  #Subsume      : 41
% 7.68/2.73  #Demod        : 2436
% 7.68/2.73  #Tautology    : 1191
% 7.68/2.73  #SimpNegUnit  : 0
% 7.68/2.73  #BackRed      : 2
% 7.68/2.73  
% 7.68/2.73  #Partial instantiations: 0
% 7.68/2.73  #Strategies tried      : 1
% 7.68/2.73  
% 7.68/2.73  Timing (in seconds)
% 7.68/2.73  ----------------------
% 7.68/2.74  Preprocessing        : 0.29
% 7.68/2.74  Parsing              : 0.16
% 7.68/2.74  CNF conversion       : 0.01
% 7.68/2.74  Main loop            : 1.63
% 7.68/2.74  Inferencing          : 0.34
% 7.68/2.74  Reduction            : 0.97
% 7.68/2.74  Demodulation         : 0.87
% 7.68/2.74  BG Simplification    : 0.05
% 7.68/2.74  Subsumption          : 0.20
% 7.68/2.74  Abstraction          : 0.07
% 7.68/2.74  MUC search           : 0.00
% 7.68/2.74  Cooper               : 0.00
% 7.68/2.74  Total                : 1.94
% 7.68/2.74  Index Insertion      : 0.00
% 7.68/2.74  Index Deletion       : 0.00
% 7.68/2.74  Index Matching       : 0.00
% 7.68/2.74  BG Taut test         : 0.00
%------------------------------------------------------------------------------

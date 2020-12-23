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
% DateTime   : Thu Dec  3 09:44:57 EST 2020

% Result     : Theorem 2.81s
% Output     : CNFRefutation 2.81s
% Verified   : 
% Statistics : Number of formulae       :   40 (  41 expanded)
%              Number of leaves         :   21 (  22 expanded)
%              Depth                    :    5
%              Number of atoms          :   31 (  32 expanded)
%              Number of equality atoms :   25 (  26 expanded)
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
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_45,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_37,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_47,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] : k4_xboole_0(A,k3_xboole_0(A,B)) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k2_xboole_0(k4_xboole_0(A,B),k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_xboole_0)).

tff(f_50,negated_conjecture,(
    ~ ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(c_48,plain,(
    ! [B_25,A_26] : k5_xboole_0(B_25,A_26) = k5_xboole_0(A_26,B_25) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_20,plain,(
    ! [A_17] : k5_xboole_0(A_17,k1_xboole_0) = A_17 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_64,plain,(
    ! [A_26] : k5_xboole_0(k1_xboole_0,A_26) = A_26 ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_20])).

tff(c_12,plain,(
    ! [A_9] : k4_xboole_0(A_9,k1_xboole_0) = A_9 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_443,plain,(
    ! [A_48,B_49] : k5_xboole_0(A_48,k4_xboole_0(B_49,A_48)) = k2_xboole_0(A_48,B_49) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_478,plain,(
    ! [A_9] : k5_xboole_0(k1_xboole_0,A_9) = k2_xboole_0(k1_xboole_0,A_9) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_443])).

tff(c_487,plain,(
    ! [A_9] : k2_xboole_0(k1_xboole_0,A_9) = A_9 ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_478])).

tff(c_203,plain,(
    ! [A_35,B_36] : k4_xboole_0(A_35,k4_xboole_0(A_35,B_36)) = k3_xboole_0(A_35,B_36) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_6,plain,(
    ! [A_5,B_6] : r1_tarski(k4_xboole_0(A_5,B_6),A_5) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_333,plain,(
    ! [A_42,B_43] : r1_tarski(k3_xboole_0(A_42,B_43),A_42) ),
    inference(superposition,[status(thm),theory(equality)],[c_203,c_6])).

tff(c_10,plain,(
    ! [A_7,B_8] :
      ( k4_xboole_0(A_7,B_8) = k1_xboole_0
      | ~ r1_tarski(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_346,plain,(
    ! [A_42,B_43] : k4_xboole_0(k3_xboole_0(A_42,B_43),A_42) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_333,c_10])).

tff(c_2,plain,(
    ! [B_2,A_1] : k5_xboole_0(B_2,A_1) = k5_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_14,plain,(
    ! [A_10,B_11] : k4_xboole_0(A_10,k3_xboole_0(A_10,B_11)) = k4_xboole_0(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_705,plain,(
    ! [A_60,B_61] : k2_xboole_0(k4_xboole_0(A_60,B_61),k4_xboole_0(B_61,A_60)) = k5_xboole_0(A_60,B_61) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_743,plain,(
    ! [A_10,B_11] : k2_xboole_0(k4_xboole_0(k3_xboole_0(A_10,B_11),A_10),k4_xboole_0(A_10,B_11)) = k5_xboole_0(k3_xboole_0(A_10,B_11),A_10) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_705])).

tff(c_777,plain,(
    ! [A_10,B_11] : k5_xboole_0(A_10,k3_xboole_0(A_10,B_11)) = k4_xboole_0(A_10,B_11) ),
    inference(demodulation,[status(thm),theory(equality)],[c_487,c_346,c_2,c_743])).

tff(c_24,plain,(
    k5_xboole_0('#skF_1',k3_xboole_0('#skF_1','#skF_2')) != k4_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_1361,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_777,c_24])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n010.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 19:55:29 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.81/1.44  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.81/1.44  
% 2.81/1.44  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.81/1.45  %$ r1_tarski > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1
% 2.81/1.45  
% 2.81/1.45  %Foreground sorts:
% 2.81/1.45  
% 2.81/1.45  
% 2.81/1.45  %Background operators:
% 2.81/1.45  
% 2.81/1.45  
% 2.81/1.45  %Foreground operators:
% 2.81/1.45  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.81/1.45  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.81/1.45  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.81/1.45  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.81/1.45  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.81/1.45  tff('#skF_2', type, '#skF_2': $i).
% 2.81/1.45  tff('#skF_1', type, '#skF_1': $i).
% 2.81/1.45  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.81/1.45  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.81/1.45  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.81/1.45  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.81/1.45  
% 2.81/1.46  tff(f_27, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 2.81/1.46  tff(f_45, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 2.81/1.46  tff(f_37, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 2.81/1.46  tff(f_47, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 2.81/1.46  tff(f_41, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 2.81/1.46  tff(f_31, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 2.81/1.46  tff(f_35, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t37_xboole_1)).
% 2.81/1.46  tff(f_39, axiom, (![A, B]: (k4_xboole_0(A, k3_xboole_0(A, B)) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_xboole_1)).
% 2.81/1.46  tff(f_29, axiom, (![A, B]: (k5_xboole_0(A, B) = k2_xboole_0(k4_xboole_0(A, B), k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_xboole_0)).
% 2.81/1.46  tff(f_50, negated_conjecture, ~(![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.81/1.46  tff(c_48, plain, (![B_25, A_26]: (k5_xboole_0(B_25, A_26)=k5_xboole_0(A_26, B_25))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.81/1.46  tff(c_20, plain, (![A_17]: (k5_xboole_0(A_17, k1_xboole_0)=A_17)), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.81/1.46  tff(c_64, plain, (![A_26]: (k5_xboole_0(k1_xboole_0, A_26)=A_26)), inference(superposition, [status(thm), theory('equality')], [c_48, c_20])).
% 2.81/1.46  tff(c_12, plain, (![A_9]: (k4_xboole_0(A_9, k1_xboole_0)=A_9)), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.81/1.46  tff(c_443, plain, (![A_48, B_49]: (k5_xboole_0(A_48, k4_xboole_0(B_49, A_48))=k2_xboole_0(A_48, B_49))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.81/1.46  tff(c_478, plain, (![A_9]: (k5_xboole_0(k1_xboole_0, A_9)=k2_xboole_0(k1_xboole_0, A_9))), inference(superposition, [status(thm), theory('equality')], [c_12, c_443])).
% 2.81/1.46  tff(c_487, plain, (![A_9]: (k2_xboole_0(k1_xboole_0, A_9)=A_9)), inference(demodulation, [status(thm), theory('equality')], [c_64, c_478])).
% 2.81/1.46  tff(c_203, plain, (![A_35, B_36]: (k4_xboole_0(A_35, k4_xboole_0(A_35, B_36))=k3_xboole_0(A_35, B_36))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.81/1.46  tff(c_6, plain, (![A_5, B_6]: (r1_tarski(k4_xboole_0(A_5, B_6), A_5))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.81/1.46  tff(c_333, plain, (![A_42, B_43]: (r1_tarski(k3_xboole_0(A_42, B_43), A_42))), inference(superposition, [status(thm), theory('equality')], [c_203, c_6])).
% 2.81/1.46  tff(c_10, plain, (![A_7, B_8]: (k4_xboole_0(A_7, B_8)=k1_xboole_0 | ~r1_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.81/1.46  tff(c_346, plain, (![A_42, B_43]: (k4_xboole_0(k3_xboole_0(A_42, B_43), A_42)=k1_xboole_0)), inference(resolution, [status(thm)], [c_333, c_10])).
% 2.81/1.46  tff(c_2, plain, (![B_2, A_1]: (k5_xboole_0(B_2, A_1)=k5_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.81/1.46  tff(c_14, plain, (![A_10, B_11]: (k4_xboole_0(A_10, k3_xboole_0(A_10, B_11))=k4_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.81/1.46  tff(c_705, plain, (![A_60, B_61]: (k2_xboole_0(k4_xboole_0(A_60, B_61), k4_xboole_0(B_61, A_60))=k5_xboole_0(A_60, B_61))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.81/1.46  tff(c_743, plain, (![A_10, B_11]: (k2_xboole_0(k4_xboole_0(k3_xboole_0(A_10, B_11), A_10), k4_xboole_0(A_10, B_11))=k5_xboole_0(k3_xboole_0(A_10, B_11), A_10))), inference(superposition, [status(thm), theory('equality')], [c_14, c_705])).
% 2.81/1.46  tff(c_777, plain, (![A_10, B_11]: (k5_xboole_0(A_10, k3_xboole_0(A_10, B_11))=k4_xboole_0(A_10, B_11))), inference(demodulation, [status(thm), theory('equality')], [c_487, c_346, c_2, c_743])).
% 2.81/1.46  tff(c_24, plain, (k5_xboole_0('#skF_1', k3_xboole_0('#skF_1', '#skF_2'))!=k4_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.81/1.46  tff(c_1361, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_777, c_24])).
% 2.81/1.46  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.81/1.46  
% 2.81/1.46  Inference rules
% 2.81/1.46  ----------------------
% 2.81/1.46  #Ref     : 0
% 2.81/1.46  #Sup     : 321
% 2.81/1.46  #Fact    : 0
% 2.81/1.46  #Define  : 0
% 2.81/1.46  #Split   : 0
% 2.81/1.46  #Chain   : 0
% 2.81/1.46  #Close   : 0
% 2.81/1.46  
% 2.81/1.46  Ordering : KBO
% 2.81/1.46  
% 2.81/1.46  Simplification rules
% 2.81/1.46  ----------------------
% 2.81/1.46  #Subsume      : 0
% 2.81/1.46  #Demod        : 257
% 2.81/1.46  #Tautology    : 243
% 2.81/1.46  #SimpNegUnit  : 0
% 2.81/1.46  #BackRed      : 1
% 2.81/1.46  
% 2.81/1.46  #Partial instantiations: 0
% 2.81/1.46  #Strategies tried      : 1
% 2.81/1.46  
% 2.81/1.46  Timing (in seconds)
% 2.81/1.46  ----------------------
% 2.81/1.46  Preprocessing        : 0.31
% 2.81/1.46  Parsing              : 0.17
% 2.81/1.46  CNF conversion       : 0.02
% 2.81/1.46  Main loop            : 0.35
% 2.81/1.46  Inferencing          : 0.13
% 2.81/1.46  Reduction            : 0.13
% 2.81/1.46  Demodulation         : 0.11
% 2.81/1.46  BG Simplification    : 0.02
% 2.81/1.46  Subsumption          : 0.05
% 2.81/1.46  Abstraction          : 0.02
% 2.81/1.46  MUC search           : 0.00
% 2.81/1.46  Cooper               : 0.00
% 2.81/1.46  Total                : 0.69
% 2.81/1.46  Index Insertion      : 0.00
% 2.81/1.46  Index Deletion       : 0.00
% 2.81/1.46  Index Matching       : 0.00
% 2.81/1.46  BG Taut test         : 0.00
%------------------------------------------------------------------------------

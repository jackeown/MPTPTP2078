%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:44:54 EST 2020

% Result     : Theorem 5.43s
% Output     : CNFRefutation 5.49s
% Verified   : 
% Statistics : Number of formulae       :   36 (  60 expanded)
%              Number of leaves         :   17 (  27 expanded)
%              Depth                    :   10
%              Number of atoms          :   26 (  50 expanded)
%              Number of equality atoms :   25 (  49 expanded)
%              Maximal formula depth    :    4 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1

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

tff(f_39,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_31,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_35,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_33,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_xboole_1)).

tff(f_42,negated_conjecture,(
    ~ ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_14,plain,(
    ! [A_12,B_13] : k5_xboole_0(A_12,k4_xboole_0(B_13,A_12)) = k2_xboole_0(A_12,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_6,plain,(
    ! [A_5] : k5_xboole_0(A_5,k1_xboole_0) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_10,plain,(
    ! [A_9] : k5_xboole_0(A_9,A_9) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_178,plain,(
    ! [A_26,B_27,C_28] : k5_xboole_0(k5_xboole_0(A_26,B_27),C_28) = k5_xboole_0(A_26,k5_xboole_0(B_27,C_28)) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_575,plain,(
    ! [A_35,C_36] : k5_xboole_0(A_35,k5_xboole_0(A_35,C_36)) = k5_xboole_0(k1_xboole_0,C_36) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_178])).

tff(c_677,plain,(
    ! [A_9] : k5_xboole_0(k1_xboole_0,A_9) = k5_xboole_0(A_9,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_575])).

tff(c_702,plain,(
    ! [A_9] : k5_xboole_0(k1_xboole_0,A_9) = A_9 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_677])).

tff(c_246,plain,(
    ! [A_9,C_28] : k5_xboole_0(A_9,k5_xboole_0(A_9,C_28)) = k5_xboole_0(k1_xboole_0,C_28) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_178])).

tff(c_781,plain,(
    ! [A_38,C_39] : k5_xboole_0(A_38,k5_xboole_0(A_38,C_39)) = C_39 ),
    inference(demodulation,[status(thm),theory(equality)],[c_702,c_246])).

tff(c_1798,plain,(
    ! [A_59,B_60] : k5_xboole_0(A_59,k2_xboole_0(A_59,B_60)) = k4_xboole_0(B_60,A_59) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_781])).

tff(c_1874,plain,(
    ! [A_1,B_2] : k5_xboole_0(A_1,k2_xboole_0(B_2,A_1)) = k4_xboole_0(B_2,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_1798])).

tff(c_12,plain,(
    ! [A_10,B_11] : k5_xboole_0(k5_xboole_0(A_10,B_11),k2_xboole_0(A_10,B_11)) = k3_xboole_0(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_229,plain,(
    ! [A_10,B_11] : k5_xboole_0(A_10,k5_xboole_0(B_11,k2_xboole_0(A_10,B_11))) = k3_xboole_0(A_10,B_11) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_178])).

tff(c_2326,plain,(
    ! [A_69,B_70] : k5_xboole_0(A_69,k4_xboole_0(A_69,B_70)) = k3_xboole_0(A_69,B_70) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1874,c_229])).

tff(c_703,plain,(
    ! [A_9,C_28] : k5_xboole_0(A_9,k5_xboole_0(A_9,C_28)) = C_28 ),
    inference(demodulation,[status(thm),theory(equality)],[c_702,c_246])).

tff(c_2344,plain,(
    ! [A_69,B_70] : k5_xboole_0(A_69,k3_xboole_0(A_69,B_70)) = k4_xboole_0(A_69,B_70) ),
    inference(superposition,[status(thm),theory(equality)],[c_2326,c_703])).

tff(c_16,plain,(
    k5_xboole_0('#skF_1',k3_xboole_0('#skF_1','#skF_2')) != k4_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_6578,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2344,c_16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.35  % Computer   : n025.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 16:01:50 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.21/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.43/2.09  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.43/2.09  
% 5.43/2.09  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.49/2.09  %$ k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1
% 5.49/2.09  
% 5.49/2.09  %Foreground sorts:
% 5.49/2.09  
% 5.49/2.09  
% 5.49/2.09  %Background operators:
% 5.49/2.09  
% 5.49/2.09  
% 5.49/2.09  %Foreground operators:
% 5.49/2.09  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.49/2.09  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 5.49/2.09  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.49/2.09  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 5.49/2.09  tff('#skF_2', type, '#skF_2': $i).
% 5.49/2.09  tff('#skF_1', type, '#skF_1': $i).
% 5.49/2.09  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.49/2.09  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.49/2.09  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.49/2.09  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 5.49/2.09  
% 5.49/2.10  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 5.49/2.10  tff(f_39, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 5.49/2.10  tff(f_31, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 5.49/2.10  tff(f_35, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_xboole_1)).
% 5.49/2.10  tff(f_33, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_xboole_1)).
% 5.49/2.10  tff(f_37, axiom, (![A, B]: (k3_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k2_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t95_xboole_1)).
% 5.49/2.10  tff(f_42, negated_conjecture, ~(![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 5.49/2.10  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 5.49/2.10  tff(c_14, plain, (![A_12, B_13]: (k5_xboole_0(A_12, k4_xboole_0(B_13, A_12))=k2_xboole_0(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_39])).
% 5.49/2.10  tff(c_6, plain, (![A_5]: (k5_xboole_0(A_5, k1_xboole_0)=A_5)), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.49/2.10  tff(c_10, plain, (![A_9]: (k5_xboole_0(A_9, A_9)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.49/2.10  tff(c_178, plain, (![A_26, B_27, C_28]: (k5_xboole_0(k5_xboole_0(A_26, B_27), C_28)=k5_xboole_0(A_26, k5_xboole_0(B_27, C_28)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 5.49/2.10  tff(c_575, plain, (![A_35, C_36]: (k5_xboole_0(A_35, k5_xboole_0(A_35, C_36))=k5_xboole_0(k1_xboole_0, C_36))), inference(superposition, [status(thm), theory('equality')], [c_10, c_178])).
% 5.49/2.10  tff(c_677, plain, (![A_9]: (k5_xboole_0(k1_xboole_0, A_9)=k5_xboole_0(A_9, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_10, c_575])).
% 5.49/2.10  tff(c_702, plain, (![A_9]: (k5_xboole_0(k1_xboole_0, A_9)=A_9)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_677])).
% 5.49/2.10  tff(c_246, plain, (![A_9, C_28]: (k5_xboole_0(A_9, k5_xboole_0(A_9, C_28))=k5_xboole_0(k1_xboole_0, C_28))), inference(superposition, [status(thm), theory('equality')], [c_10, c_178])).
% 5.49/2.10  tff(c_781, plain, (![A_38, C_39]: (k5_xboole_0(A_38, k5_xboole_0(A_38, C_39))=C_39)), inference(demodulation, [status(thm), theory('equality')], [c_702, c_246])).
% 5.49/2.10  tff(c_1798, plain, (![A_59, B_60]: (k5_xboole_0(A_59, k2_xboole_0(A_59, B_60))=k4_xboole_0(B_60, A_59))), inference(superposition, [status(thm), theory('equality')], [c_14, c_781])).
% 5.49/2.10  tff(c_1874, plain, (![A_1, B_2]: (k5_xboole_0(A_1, k2_xboole_0(B_2, A_1))=k4_xboole_0(B_2, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_1798])).
% 5.49/2.10  tff(c_12, plain, (![A_10, B_11]: (k5_xboole_0(k5_xboole_0(A_10, B_11), k2_xboole_0(A_10, B_11))=k3_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.49/2.10  tff(c_229, plain, (![A_10, B_11]: (k5_xboole_0(A_10, k5_xboole_0(B_11, k2_xboole_0(A_10, B_11)))=k3_xboole_0(A_10, B_11))), inference(superposition, [status(thm), theory('equality')], [c_12, c_178])).
% 5.49/2.10  tff(c_2326, plain, (![A_69, B_70]: (k5_xboole_0(A_69, k4_xboole_0(A_69, B_70))=k3_xboole_0(A_69, B_70))), inference(demodulation, [status(thm), theory('equality')], [c_1874, c_229])).
% 5.49/2.10  tff(c_703, plain, (![A_9, C_28]: (k5_xboole_0(A_9, k5_xboole_0(A_9, C_28))=C_28)), inference(demodulation, [status(thm), theory('equality')], [c_702, c_246])).
% 5.49/2.10  tff(c_2344, plain, (![A_69, B_70]: (k5_xboole_0(A_69, k3_xboole_0(A_69, B_70))=k4_xboole_0(A_69, B_70))), inference(superposition, [status(thm), theory('equality')], [c_2326, c_703])).
% 5.49/2.10  tff(c_16, plain, (k5_xboole_0('#skF_1', k3_xboole_0('#skF_1', '#skF_2'))!=k4_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_42])).
% 5.49/2.10  tff(c_6578, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2344, c_16])).
% 5.49/2.10  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.49/2.10  
% 5.49/2.10  Inference rules
% 5.49/2.10  ----------------------
% 5.49/2.10  #Ref     : 0
% 5.49/2.10  #Sup     : 1592
% 5.49/2.10  #Fact    : 0
% 5.49/2.10  #Define  : 0
% 5.49/2.10  #Split   : 0
% 5.49/2.10  #Chain   : 0
% 5.49/2.10  #Close   : 0
% 5.49/2.10  
% 5.49/2.10  Ordering : KBO
% 5.49/2.10  
% 5.49/2.10  Simplification rules
% 5.49/2.10  ----------------------
% 5.49/2.10  #Subsume      : 27
% 5.49/2.10  #Demod        : 1937
% 5.49/2.10  #Tautology    : 914
% 5.49/2.10  #SimpNegUnit  : 0
% 5.49/2.10  #BackRed      : 37
% 5.49/2.10  
% 5.49/2.10  #Partial instantiations: 0
% 5.49/2.10  #Strategies tried      : 1
% 5.49/2.10  
% 5.49/2.10  Timing (in seconds)
% 5.49/2.10  ----------------------
% 5.49/2.10  Preprocessing        : 0.26
% 5.49/2.10  Parsing              : 0.14
% 5.49/2.10  CNF conversion       : 0.01
% 5.49/2.10  Main loop            : 1.09
% 5.49/2.10  Inferencing          : 0.31
% 5.49/2.10  Reduction            : 0.54
% 5.49/2.10  Demodulation         : 0.47
% 5.49/2.10  BG Simplification    : 0.04
% 5.49/2.10  Subsumption          : 0.13
% 5.49/2.10  Abstraction          : 0.06
% 5.49/2.10  MUC search           : 0.00
% 5.49/2.10  Cooper               : 0.00
% 5.49/2.10  Total                : 1.37
% 5.49/2.10  Index Insertion      : 0.00
% 5.49/2.10  Index Deletion       : 0.00
% 5.49/2.11  Index Matching       : 0.00
% 5.49/2.11  BG Taut test         : 0.00
%------------------------------------------------------------------------------

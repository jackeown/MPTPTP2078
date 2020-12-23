%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:44:54 EST 2020

% Result     : Theorem 3.77s
% Output     : CNFRefutation 3.77s
% Verified   : 
% Statistics : Number of formulae       :   36 (  45 expanded)
%              Number of leaves         :   18 (  23 expanded)
%              Depth                    :    7
%              Number of atoms          :   26 (  35 expanded)
%              Number of equality atoms :   25 (  34 expanded)
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

tff(f_39,axiom,(
    ! [A,B] : k4_xboole_0(A,k3_xboole_0(A,B)) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_31,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_37,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

tff(f_35,axiom,(
    ! [A,B,C] : k4_xboole_0(k4_xboole_0(A,B),C) = k4_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k2_xboole_0(k4_xboole_0(A,B),k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_xboole_0)).

tff(f_46,negated_conjecture,(
    ~ ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(c_14,plain,(
    ! [A_12,B_13] : k4_xboole_0(A_12,k3_xboole_0(A_12,B_13)) = k4_xboole_0(A_12,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_284,plain,(
    ! [A_33,B_34] : k4_xboole_0(A_33,k4_xboole_0(A_33,B_34)) = k3_xboole_0(A_33,B_34) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_16,plain,(
    ! [A_14,B_15] : k4_xboole_0(A_14,k4_xboole_0(A_14,B_15)) = k3_xboole_0(A_14,B_15) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_287,plain,(
    ! [A_33,B_34] : k4_xboole_0(A_33,k3_xboole_0(A_33,B_34)) = k3_xboole_0(A_33,k4_xboole_0(A_33,B_34)) ),
    inference(superposition,[status(thm),theory(equality)],[c_284,c_16])).

tff(c_326,plain,(
    ! [A_33,B_34] : k3_xboole_0(A_33,k4_xboole_0(A_33,B_34)) = k4_xboole_0(A_33,B_34) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_287])).

tff(c_6,plain,(
    ! [A_5] : k2_xboole_0(A_5,k1_xboole_0) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_124,plain,(
    ! [A_23,B_24] : k4_xboole_0(A_23,k2_xboole_0(A_23,B_24)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_134,plain,(
    ! [A_1,B_2] : k4_xboole_0(A_1,k2_xboole_0(B_2,A_1)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_124])).

tff(c_10,plain,(
    ! [A_7,B_8,C_9] : k4_xboole_0(k4_xboole_0(A_7,B_8),C_9) = k4_xboole_0(A_7,k2_xboole_0(B_8,C_9)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_390,plain,(
    ! [A_38,B_39] : k2_xboole_0(k4_xboole_0(A_38,B_39),k4_xboole_0(B_39,A_38)) = k5_xboole_0(A_38,B_39) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_1577,plain,(
    ! [B_69,A_70] : k2_xboole_0(k4_xboole_0(B_69,A_70),k4_xboole_0(A_70,B_69)) = k5_xboole_0(A_70,B_69) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_390])).

tff(c_1669,plain,(
    ! [A_14,B_15] : k2_xboole_0(k4_xboole_0(k4_xboole_0(A_14,B_15),A_14),k3_xboole_0(A_14,B_15)) = k5_xboole_0(A_14,k4_xboole_0(A_14,B_15)) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_1577])).

tff(c_2076,plain,(
    ! [A_78,B_79] : k5_xboole_0(A_78,k4_xboole_0(A_78,B_79)) = k3_xboole_0(A_78,B_79) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_134,c_2,c_10,c_1669])).

tff(c_2130,plain,(
    ! [A_14,B_15] : k5_xboole_0(A_14,k3_xboole_0(A_14,B_15)) = k3_xboole_0(A_14,k4_xboole_0(A_14,B_15)) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_2076])).

tff(c_2168,plain,(
    ! [A_14,B_15] : k5_xboole_0(A_14,k3_xboole_0(A_14,B_15)) = k4_xboole_0(A_14,B_15) ),
    inference(demodulation,[status(thm),theory(equality)],[c_326,c_2130])).

tff(c_20,plain,(
    k5_xboole_0('#skF_1',k3_xboole_0('#skF_1','#skF_2')) != k4_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_3817,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2168,c_20])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:15:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.77/1.63  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.77/1.63  
% 3.77/1.63  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.77/1.63  %$ k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1
% 3.77/1.63  
% 3.77/1.63  %Foreground sorts:
% 3.77/1.63  
% 3.77/1.63  
% 3.77/1.63  %Background operators:
% 3.77/1.63  
% 3.77/1.63  
% 3.77/1.63  %Foreground operators:
% 3.77/1.63  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.77/1.63  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.77/1.63  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.77/1.63  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.77/1.63  tff('#skF_2', type, '#skF_2': $i).
% 3.77/1.63  tff('#skF_1', type, '#skF_1': $i).
% 3.77/1.63  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.77/1.63  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.77/1.63  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.77/1.63  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.77/1.63  
% 3.77/1.64  tff(f_39, axiom, (![A, B]: (k4_xboole_0(A, k3_xboole_0(A, B)) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_xboole_1)).
% 3.77/1.64  tff(f_41, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 3.77/1.64  tff(f_31, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 3.77/1.64  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 3.77/1.64  tff(f_37, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_xboole_1)).
% 3.77/1.64  tff(f_35, axiom, (![A, B, C]: (k4_xboole_0(k4_xboole_0(A, B), C) = k4_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_xboole_1)).
% 3.77/1.64  tff(f_29, axiom, (![A, B]: (k5_xboole_0(A, B) = k2_xboole_0(k4_xboole_0(A, B), k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d6_xboole_0)).
% 3.77/1.64  tff(f_46, negated_conjecture, ~(![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.77/1.64  tff(c_14, plain, (![A_12, B_13]: (k4_xboole_0(A_12, k3_xboole_0(A_12, B_13))=k4_xboole_0(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.77/1.64  tff(c_284, plain, (![A_33, B_34]: (k4_xboole_0(A_33, k4_xboole_0(A_33, B_34))=k3_xboole_0(A_33, B_34))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.77/1.64  tff(c_16, plain, (![A_14, B_15]: (k4_xboole_0(A_14, k4_xboole_0(A_14, B_15))=k3_xboole_0(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.77/1.64  tff(c_287, plain, (![A_33, B_34]: (k4_xboole_0(A_33, k3_xboole_0(A_33, B_34))=k3_xboole_0(A_33, k4_xboole_0(A_33, B_34)))), inference(superposition, [status(thm), theory('equality')], [c_284, c_16])).
% 3.77/1.64  tff(c_326, plain, (![A_33, B_34]: (k3_xboole_0(A_33, k4_xboole_0(A_33, B_34))=k4_xboole_0(A_33, B_34))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_287])).
% 3.77/1.64  tff(c_6, plain, (![A_5]: (k2_xboole_0(A_5, k1_xboole_0)=A_5)), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.77/1.64  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.77/1.64  tff(c_124, plain, (![A_23, B_24]: (k4_xboole_0(A_23, k2_xboole_0(A_23, B_24))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.77/1.64  tff(c_134, plain, (![A_1, B_2]: (k4_xboole_0(A_1, k2_xboole_0(B_2, A_1))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2, c_124])).
% 3.77/1.64  tff(c_10, plain, (![A_7, B_8, C_9]: (k4_xboole_0(k4_xboole_0(A_7, B_8), C_9)=k4_xboole_0(A_7, k2_xboole_0(B_8, C_9)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.77/1.64  tff(c_390, plain, (![A_38, B_39]: (k2_xboole_0(k4_xboole_0(A_38, B_39), k4_xboole_0(B_39, A_38))=k5_xboole_0(A_38, B_39))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.77/1.64  tff(c_1577, plain, (![B_69, A_70]: (k2_xboole_0(k4_xboole_0(B_69, A_70), k4_xboole_0(A_70, B_69))=k5_xboole_0(A_70, B_69))), inference(superposition, [status(thm), theory('equality')], [c_2, c_390])).
% 3.77/1.64  tff(c_1669, plain, (![A_14, B_15]: (k2_xboole_0(k4_xboole_0(k4_xboole_0(A_14, B_15), A_14), k3_xboole_0(A_14, B_15))=k5_xboole_0(A_14, k4_xboole_0(A_14, B_15)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_1577])).
% 3.77/1.64  tff(c_2076, plain, (![A_78, B_79]: (k5_xboole_0(A_78, k4_xboole_0(A_78, B_79))=k3_xboole_0(A_78, B_79))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_134, c_2, c_10, c_1669])).
% 3.77/1.64  tff(c_2130, plain, (![A_14, B_15]: (k5_xboole_0(A_14, k3_xboole_0(A_14, B_15))=k3_xboole_0(A_14, k4_xboole_0(A_14, B_15)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_2076])).
% 3.77/1.64  tff(c_2168, plain, (![A_14, B_15]: (k5_xboole_0(A_14, k3_xboole_0(A_14, B_15))=k4_xboole_0(A_14, B_15))), inference(demodulation, [status(thm), theory('equality')], [c_326, c_2130])).
% 3.77/1.64  tff(c_20, plain, (k5_xboole_0('#skF_1', k3_xboole_0('#skF_1', '#skF_2'))!=k4_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.77/1.64  tff(c_3817, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2168, c_20])).
% 3.77/1.64  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.77/1.64  
% 3.77/1.64  Inference rules
% 3.77/1.64  ----------------------
% 3.77/1.64  #Ref     : 0
% 3.77/1.64  #Sup     : 924
% 3.77/1.64  #Fact    : 0
% 3.77/1.64  #Define  : 0
% 3.77/1.64  #Split   : 0
% 3.77/1.64  #Chain   : 0
% 3.77/1.64  #Close   : 0
% 3.77/1.64  
% 3.77/1.64  Ordering : KBO
% 3.77/1.64  
% 3.77/1.64  Simplification rules
% 3.77/1.64  ----------------------
% 3.77/1.64  #Subsume      : 1
% 3.77/1.64  #Demod        : 799
% 3.77/1.64  #Tautology    : 647
% 3.77/1.64  #SimpNegUnit  : 0
% 3.77/1.64  #BackRed      : 1
% 3.77/1.64  
% 3.77/1.64  #Partial instantiations: 0
% 3.77/1.64  #Strategies tried      : 1
% 3.77/1.64  
% 3.77/1.64  Timing (in seconds)
% 3.77/1.64  ----------------------
% 3.77/1.64  Preprocessing        : 0.25
% 3.77/1.64  Parsing              : 0.14
% 3.77/1.64  CNF conversion       : 0.01
% 3.77/1.64  Main loop            : 0.63
% 3.77/1.64  Inferencing          : 0.20
% 3.77/1.64  Reduction            : 0.29
% 3.77/1.65  Demodulation         : 0.24
% 3.77/1.65  BG Simplification    : 0.02
% 3.77/1.65  Subsumption          : 0.08
% 3.77/1.65  Abstraction          : 0.04
% 3.77/1.65  MUC search           : 0.00
% 3.77/1.65  Cooper               : 0.00
% 3.77/1.65  Total                : 0.91
% 3.77/1.65  Index Insertion      : 0.00
% 3.77/1.65  Index Deletion       : 0.00
% 3.77/1.65  Index Matching       : 0.00
% 3.77/1.65  BG Taut test         : 0.00
%------------------------------------------------------------------------------

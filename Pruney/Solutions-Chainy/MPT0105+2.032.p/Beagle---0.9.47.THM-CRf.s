%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:44:51 EST 2020

% Result     : Theorem 2.50s
% Output     : CNFRefutation 2.78s
% Verified   : 
% Statistics : Number of formulae       :   32 (  32 expanded)
%              Number of leaves         :   18 (  18 expanded)
%              Depth                    :    6
%              Number of atoms          :   22 (  22 expanded)
%              Number of equality atoms :   21 (  21 expanded)
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

tff(f_29,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_31,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_35,axiom,(
    ! [A,B,C] : k3_xboole_0(A,k4_xboole_0(B,C)) = k4_xboole_0(k3_xboole_0(A,B),C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] : k2_xboole_0(k3_xboole_0(A,B),k4_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k2_xboole_0(k4_xboole_0(A,B),k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_xboole_0)).

tff(f_39,axiom,(
    ! [A,B] : k4_xboole_0(k2_xboole_0(A,B),k3_xboole_0(A,B)) = k2_xboole_0(k4_xboole_0(A,B),k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_xboole_1)).

tff(f_42,negated_conjecture,(
    ~ ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

tff(c_4,plain,(
    ! [A_3,B_4] : k2_xboole_0(A_3,k4_xboole_0(B_4,A_3)) = k2_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_6,plain,(
    ! [A_5] : k4_xboole_0(A_5,k1_xboole_0) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_389,plain,(
    ! [A_37,B_38,C_39] : k4_xboole_0(k3_xboole_0(A_37,B_38),C_39) = k3_xboole_0(A_37,k4_xboole_0(B_38,C_39)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_34,plain,(
    ! [A_18,B_19] : k2_xboole_0(k3_xboole_0(A_18,B_19),k4_xboole_0(A_18,B_19)) = A_18 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_8,plain,(
    ! [A_6,B_7] : k4_xboole_0(A_6,k2_xboole_0(A_6,B_7)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_40,plain,(
    ! [A_18,B_19] : k4_xboole_0(k3_xboole_0(A_18,B_19),A_18) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_8])).

tff(c_491,plain,(
    ! [C_41,B_42] : k3_xboole_0(C_41,k4_xboole_0(B_42,C_41)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_389,c_40])).

tff(c_2,plain,(
    ! [A_1,B_2] : k2_xboole_0(k4_xboole_0(A_1,B_2),k4_xboole_0(B_2,A_1)) = k5_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_14,plain,(
    ! [A_13,B_14] : k4_xboole_0(k2_xboole_0(A_13,B_14),k3_xboole_0(A_13,B_14)) = k2_xboole_0(k4_xboole_0(A_13,B_14),k4_xboole_0(B_14,A_13)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_17,plain,(
    ! [A_13,B_14] : k4_xboole_0(k2_xboole_0(A_13,B_14),k3_xboole_0(A_13,B_14)) = k5_xboole_0(A_13,B_14) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_14])).

tff(c_499,plain,(
    ! [C_41,B_42] : k4_xboole_0(k2_xboole_0(C_41,k4_xboole_0(B_42,C_41)),k1_xboole_0) = k5_xboole_0(C_41,k4_xboole_0(B_42,C_41)) ),
    inference(superposition,[status(thm),theory(equality)],[c_491,c_17])).

tff(c_537,plain,(
    ! [C_41,B_42] : k5_xboole_0(C_41,k4_xboole_0(B_42,C_41)) = k2_xboole_0(C_41,B_42) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_6,c_499])).

tff(c_16,plain,(
    k5_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_1')) != k2_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_1362,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_537,c_16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n015.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 17:23:08 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.50/1.38  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.78/1.38  
% 2.78/1.38  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.78/1.39  %$ k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1
% 2.78/1.39  
% 2.78/1.39  %Foreground sorts:
% 2.78/1.39  
% 2.78/1.39  
% 2.78/1.39  %Background operators:
% 2.78/1.39  
% 2.78/1.39  
% 2.78/1.39  %Foreground operators:
% 2.78/1.39  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.78/1.39  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.78/1.39  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.78/1.39  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.78/1.39  tff('#skF_2', type, '#skF_2': $i).
% 2.78/1.39  tff('#skF_1', type, '#skF_1': $i).
% 2.78/1.39  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.78/1.39  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.78/1.39  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.78/1.39  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.78/1.39  
% 2.78/1.40  tff(f_29, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 2.78/1.40  tff(f_31, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 2.78/1.40  tff(f_35, axiom, (![A, B, C]: (k3_xboole_0(A, k4_xboole_0(B, C)) = k4_xboole_0(k3_xboole_0(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_xboole_1)).
% 2.78/1.40  tff(f_37, axiom, (![A, B]: (k2_xboole_0(k3_xboole_0(A, B), k4_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_xboole_1)).
% 2.78/1.40  tff(f_33, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_xboole_1)).
% 2.78/1.40  tff(f_27, axiom, (![A, B]: (k5_xboole_0(A, B) = k2_xboole_0(k4_xboole_0(A, B), k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d6_xboole_0)).
% 2.78/1.40  tff(f_39, axiom, (![A, B]: (k4_xboole_0(k2_xboole_0(A, B), k3_xboole_0(A, B)) = k2_xboole_0(k4_xboole_0(A, B), k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_xboole_1)).
% 2.78/1.40  tff(f_42, negated_conjecture, ~(![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 2.78/1.40  tff(c_4, plain, (![A_3, B_4]: (k2_xboole_0(A_3, k4_xboole_0(B_4, A_3))=k2_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.78/1.40  tff(c_6, plain, (![A_5]: (k4_xboole_0(A_5, k1_xboole_0)=A_5)), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.78/1.40  tff(c_389, plain, (![A_37, B_38, C_39]: (k4_xboole_0(k3_xboole_0(A_37, B_38), C_39)=k3_xboole_0(A_37, k4_xboole_0(B_38, C_39)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.78/1.40  tff(c_34, plain, (![A_18, B_19]: (k2_xboole_0(k3_xboole_0(A_18, B_19), k4_xboole_0(A_18, B_19))=A_18)), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.78/1.40  tff(c_8, plain, (![A_6, B_7]: (k4_xboole_0(A_6, k2_xboole_0(A_6, B_7))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.78/1.40  tff(c_40, plain, (![A_18, B_19]: (k4_xboole_0(k3_xboole_0(A_18, B_19), A_18)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_34, c_8])).
% 2.78/1.40  tff(c_491, plain, (![C_41, B_42]: (k3_xboole_0(C_41, k4_xboole_0(B_42, C_41))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_389, c_40])).
% 2.78/1.40  tff(c_2, plain, (![A_1, B_2]: (k2_xboole_0(k4_xboole_0(A_1, B_2), k4_xboole_0(B_2, A_1))=k5_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.78/1.40  tff(c_14, plain, (![A_13, B_14]: (k4_xboole_0(k2_xboole_0(A_13, B_14), k3_xboole_0(A_13, B_14))=k2_xboole_0(k4_xboole_0(A_13, B_14), k4_xboole_0(B_14, A_13)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.78/1.40  tff(c_17, plain, (![A_13, B_14]: (k4_xboole_0(k2_xboole_0(A_13, B_14), k3_xboole_0(A_13, B_14))=k5_xboole_0(A_13, B_14))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_14])).
% 2.78/1.40  tff(c_499, plain, (![C_41, B_42]: (k4_xboole_0(k2_xboole_0(C_41, k4_xboole_0(B_42, C_41)), k1_xboole_0)=k5_xboole_0(C_41, k4_xboole_0(B_42, C_41)))), inference(superposition, [status(thm), theory('equality')], [c_491, c_17])).
% 2.78/1.40  tff(c_537, plain, (![C_41, B_42]: (k5_xboole_0(C_41, k4_xboole_0(B_42, C_41))=k2_xboole_0(C_41, B_42))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_6, c_499])).
% 2.78/1.40  tff(c_16, plain, (k5_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_1'))!=k2_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.78/1.40  tff(c_1362, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_537, c_16])).
% 2.78/1.40  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.78/1.40  
% 2.78/1.40  Inference rules
% 2.78/1.40  ----------------------
% 2.78/1.40  #Ref     : 0
% 2.78/1.40  #Sup     : 344
% 2.78/1.40  #Fact    : 0
% 2.78/1.40  #Define  : 0
% 2.78/1.40  #Split   : 0
% 2.78/1.40  #Chain   : 0
% 2.78/1.40  #Close   : 0
% 2.78/1.40  
% 2.78/1.40  Ordering : KBO
% 2.78/1.40  
% 2.78/1.40  Simplification rules
% 2.78/1.40  ----------------------
% 2.78/1.40  #Subsume      : 5
% 2.78/1.40  #Demod        : 239
% 2.78/1.40  #Tautology    : 237
% 2.78/1.40  #SimpNegUnit  : 0
% 2.78/1.40  #BackRed      : 7
% 2.78/1.40  
% 2.78/1.40  #Partial instantiations: 0
% 2.78/1.40  #Strategies tried      : 1
% 2.78/1.40  
% 2.78/1.40  Timing (in seconds)
% 2.78/1.40  ----------------------
% 2.78/1.40  Preprocessing        : 0.27
% 2.78/1.40  Parsing              : 0.14
% 2.78/1.40  CNF conversion       : 0.02
% 2.78/1.40  Main loop            : 0.36
% 2.78/1.40  Inferencing          : 0.13
% 2.78/1.40  Reduction            : 0.14
% 2.78/1.40  Demodulation         : 0.11
% 2.78/1.40  BG Simplification    : 0.02
% 2.78/1.40  Subsumption          : 0.05
% 2.78/1.40  Abstraction          : 0.03
% 2.78/1.40  MUC search           : 0.00
% 2.78/1.40  Cooper               : 0.00
% 2.78/1.40  Total                : 0.66
% 2.78/1.40  Index Insertion      : 0.00
% 2.78/1.40  Index Deletion       : 0.00
% 2.78/1.40  Index Matching       : 0.00
% 2.78/1.40  BG Taut test         : 0.00
%------------------------------------------------------------------------------

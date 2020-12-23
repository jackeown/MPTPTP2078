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
% DateTime   : Thu Dec  3 09:44:53 EST 2020

% Result     : Theorem 3.83s
% Output     : CNFRefutation 4.10s
% Verified   : 
% Statistics : Number of formulae       :   32 (  35 expanded)
%              Number of leaves         :   18 (  20 expanded)
%              Depth                    :    5
%              Number of atoms          :   22 (  25 expanded)
%              Number of equality atoms :   21 (  24 expanded)
%              Maximal formula depth    :    4 (   3 average)
%              Maximal term depth       :    4 (   3 average)

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
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_37,axiom,(
    ! [A,B] : k4_xboole_0(A,k3_xboole_0(A,B)) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_45,axiom,(
    ! [A,B,C] : k4_xboole_0(A,k4_xboole_0(B,C)) = k2_xboole_0(k4_xboole_0(A,B),k3_xboole_0(A,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_41,axiom,(
    ! [A,B,C] : k3_xboole_0(A,k4_xboole_0(B,C)) = k4_xboole_0(k3_xboole_0(A,B),C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k2_xboole_0(k4_xboole_0(A,B),k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_xboole_0)).

tff(f_50,negated_conjecture,(
    ~ ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(c_4,plain,(
    ! [B_4,A_3] : k3_xboole_0(B_4,A_3) = k3_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_275,plain,(
    ! [A_38,B_39] : k4_xboole_0(A_38,k3_xboole_0(A_38,B_39)) = k4_xboole_0(A_38,B_39) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_287,plain,(
    ! [A_3,B_4] : k4_xboole_0(A_3,k3_xboole_0(B_4,A_3)) = k4_xboole_0(A_3,B_4) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_275])).

tff(c_14,plain,(
    ! [A_12,B_13] : k4_xboole_0(A_12,k4_xboole_0(A_12,B_13)) = k3_xboole_0(A_12,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_20,plain,(
    ! [A_19,B_20,C_21] : k2_xboole_0(k4_xboole_0(A_19,B_20),k3_xboole_0(A_19,C_21)) = k4_xboole_0(A_19,k4_xboole_0(B_20,C_21)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_16,plain,(
    ! [A_14,B_15,C_16] : k4_xboole_0(k3_xboole_0(A_14,B_15),C_16) = k3_xboole_0(A_14,k4_xboole_0(B_15,C_16)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_12,plain,(
    ! [A_10,B_11] : k4_xboole_0(A_10,k3_xboole_0(A_10,B_11)) = k4_xboole_0(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_625,plain,(
    ! [A_50,B_51] : k2_xboole_0(k4_xboole_0(A_50,B_51),k4_xboole_0(B_51,A_50)) = k5_xboole_0(A_50,B_51) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_2640,plain,(
    ! [B_98,A_99] : k2_xboole_0(k4_xboole_0(B_98,A_99),k4_xboole_0(A_99,B_98)) = k5_xboole_0(A_99,B_98) ),
    inference(superposition,[status(thm),theory(equality)],[c_625,c_2])).

tff(c_2744,plain,(
    ! [A_10,B_11] : k2_xboole_0(k4_xboole_0(k3_xboole_0(A_10,B_11),A_10),k4_xboole_0(A_10,B_11)) = k5_xboole_0(A_10,k3_xboole_0(A_10,B_11)) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_2640])).

tff(c_2787,plain,(
    ! [A_10,B_11] : k5_xboole_0(A_10,k3_xboole_0(A_10,B_11)) = k4_xboole_0(A_10,B_11) ),
    inference(demodulation,[status(thm),theory(equality)],[c_287,c_14,c_20,c_2,c_16,c_2744])).

tff(c_24,plain,(
    k5_xboole_0('#skF_1',k3_xboole_0('#skF_1','#skF_2')) != k4_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_3714,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2787,c_24])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n010.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 15:01:59 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.83/1.70  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.83/1.70  
% 3.83/1.70  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.83/1.71  %$ k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1
% 3.83/1.71  
% 3.83/1.71  %Foreground sorts:
% 3.83/1.71  
% 3.83/1.71  
% 3.83/1.71  %Background operators:
% 3.83/1.71  
% 3.83/1.71  
% 3.83/1.71  %Foreground operators:
% 3.83/1.71  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.83/1.71  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.83/1.71  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.83/1.71  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.83/1.71  tff('#skF_2', type, '#skF_2': $i).
% 3.83/1.71  tff('#skF_1', type, '#skF_1': $i).
% 3.83/1.71  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.83/1.71  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.83/1.71  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.83/1.71  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.83/1.71  
% 4.10/1.72  tff(f_29, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 4.10/1.72  tff(f_37, axiom, (![A, B]: (k4_xboole_0(A, k3_xboole_0(A, B)) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_xboole_1)).
% 4.10/1.72  tff(f_39, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 4.10/1.72  tff(f_45, axiom, (![A, B, C]: (k4_xboole_0(A, k4_xboole_0(B, C)) = k2_xboole_0(k4_xboole_0(A, B), k3_xboole_0(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_xboole_1)).
% 4.10/1.72  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 4.10/1.72  tff(f_41, axiom, (![A, B, C]: (k3_xboole_0(A, k4_xboole_0(B, C)) = k4_xboole_0(k3_xboole_0(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_xboole_1)).
% 4.10/1.72  tff(f_31, axiom, (![A, B]: (k5_xboole_0(A, B) = k2_xboole_0(k4_xboole_0(A, B), k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_xboole_0)).
% 4.10/1.72  tff(f_50, negated_conjecture, ~(![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 4.10/1.72  tff(c_4, plain, (![B_4, A_3]: (k3_xboole_0(B_4, A_3)=k3_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.10/1.72  tff(c_275, plain, (![A_38, B_39]: (k4_xboole_0(A_38, k3_xboole_0(A_38, B_39))=k4_xboole_0(A_38, B_39))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.10/1.72  tff(c_287, plain, (![A_3, B_4]: (k4_xboole_0(A_3, k3_xboole_0(B_4, A_3))=k4_xboole_0(A_3, B_4))), inference(superposition, [status(thm), theory('equality')], [c_4, c_275])).
% 4.10/1.72  tff(c_14, plain, (![A_12, B_13]: (k4_xboole_0(A_12, k4_xboole_0(A_12, B_13))=k3_xboole_0(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.10/1.72  tff(c_20, plain, (![A_19, B_20, C_21]: (k2_xboole_0(k4_xboole_0(A_19, B_20), k3_xboole_0(A_19, C_21))=k4_xboole_0(A_19, k4_xboole_0(B_20, C_21)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.10/1.72  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.10/1.72  tff(c_16, plain, (![A_14, B_15, C_16]: (k4_xboole_0(k3_xboole_0(A_14, B_15), C_16)=k3_xboole_0(A_14, k4_xboole_0(B_15, C_16)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.10/1.72  tff(c_12, plain, (![A_10, B_11]: (k4_xboole_0(A_10, k3_xboole_0(A_10, B_11))=k4_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.10/1.72  tff(c_625, plain, (![A_50, B_51]: (k2_xboole_0(k4_xboole_0(A_50, B_51), k4_xboole_0(B_51, A_50))=k5_xboole_0(A_50, B_51))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.10/1.72  tff(c_2640, plain, (![B_98, A_99]: (k2_xboole_0(k4_xboole_0(B_98, A_99), k4_xboole_0(A_99, B_98))=k5_xboole_0(A_99, B_98))), inference(superposition, [status(thm), theory('equality')], [c_625, c_2])).
% 4.10/1.72  tff(c_2744, plain, (![A_10, B_11]: (k2_xboole_0(k4_xboole_0(k3_xboole_0(A_10, B_11), A_10), k4_xboole_0(A_10, B_11))=k5_xboole_0(A_10, k3_xboole_0(A_10, B_11)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_2640])).
% 4.10/1.72  tff(c_2787, plain, (![A_10, B_11]: (k5_xboole_0(A_10, k3_xboole_0(A_10, B_11))=k4_xboole_0(A_10, B_11))), inference(demodulation, [status(thm), theory('equality')], [c_287, c_14, c_20, c_2, c_16, c_2744])).
% 4.10/1.72  tff(c_24, plain, (k5_xboole_0('#skF_1', k3_xboole_0('#skF_1', '#skF_2'))!=k4_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_50])).
% 4.10/1.72  tff(c_3714, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2787, c_24])).
% 4.10/1.72  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.10/1.72  
% 4.10/1.72  Inference rules
% 4.10/1.72  ----------------------
% 4.10/1.72  #Ref     : 0
% 4.10/1.72  #Sup     : 907
% 4.10/1.72  #Fact    : 0
% 4.10/1.72  #Define  : 0
% 4.10/1.72  #Split   : 0
% 4.10/1.72  #Chain   : 0
% 4.10/1.72  #Close   : 0
% 4.10/1.72  
% 4.10/1.72  Ordering : KBO
% 4.10/1.72  
% 4.10/1.72  Simplification rules
% 4.10/1.72  ----------------------
% 4.10/1.72  #Subsume      : 4
% 4.10/1.72  #Demod        : 888
% 4.10/1.72  #Tautology    : 612
% 4.10/1.72  #SimpNegUnit  : 0
% 4.10/1.72  #BackRed      : 9
% 4.10/1.72  
% 4.10/1.72  #Partial instantiations: 0
% 4.10/1.72  #Strategies tried      : 1
% 4.10/1.72  
% 4.10/1.72  Timing (in seconds)
% 4.10/1.72  ----------------------
% 4.10/1.72  Preprocessing        : 0.29
% 4.10/1.72  Parsing              : 0.16
% 4.10/1.72  CNF conversion       : 0.01
% 4.10/1.72  Main loop            : 0.67
% 4.10/1.72  Inferencing          : 0.21
% 4.10/1.72  Reduction            : 0.31
% 4.10/1.72  Demodulation         : 0.26
% 4.10/1.72  BG Simplification    : 0.03
% 4.10/1.72  Subsumption          : 0.09
% 4.10/1.72  Abstraction          : 0.04
% 4.10/1.72  MUC search           : 0.00
% 4.10/1.72  Cooper               : 0.00
% 4.10/1.72  Total                : 0.99
% 4.10/1.72  Index Insertion      : 0.00
% 4.10/1.72  Index Deletion       : 0.00
% 4.10/1.72  Index Matching       : 0.00
% 4.10/1.72  BG Taut test         : 0.00
%------------------------------------------------------------------------------

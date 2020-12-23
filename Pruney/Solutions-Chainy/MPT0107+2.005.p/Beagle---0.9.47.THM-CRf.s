%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:44:53 EST 2020

% Result     : Theorem 4.60s
% Output     : CNFRefutation 4.60s
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

tff(c_182,plain,(
    ! [A_34,B_35] : k4_xboole_0(A_34,k3_xboole_0(A_34,B_35)) = k4_xboole_0(A_34,B_35) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_200,plain,(
    ! [B_4,A_3] : k4_xboole_0(B_4,k3_xboole_0(A_3,B_4)) = k4_xboole_0(B_4,A_3) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_182])).

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

tff(c_338,plain,(
    ! [A_43,B_44] : k2_xboole_0(k4_xboole_0(A_43,B_44),k4_xboole_0(B_44,A_43)) = k5_xboole_0(A_43,B_44) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_4208,plain,(
    ! [B_122,A_123] : k2_xboole_0(k4_xboole_0(B_122,A_123),k4_xboole_0(A_123,B_122)) = k5_xboole_0(A_123,B_122) ),
    inference(superposition,[status(thm),theory(equality)],[c_338,c_2])).

tff(c_4330,plain,(
    ! [A_10,B_11] : k2_xboole_0(k4_xboole_0(k3_xboole_0(A_10,B_11),A_10),k4_xboole_0(A_10,B_11)) = k5_xboole_0(A_10,k3_xboole_0(A_10,B_11)) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_4208])).

tff(c_4375,plain,(
    ! [A_10,B_11] : k5_xboole_0(A_10,k3_xboole_0(A_10,B_11)) = k4_xboole_0(A_10,B_11) ),
    inference(demodulation,[status(thm),theory(equality)],[c_200,c_14,c_20,c_2,c_16,c_4330])).

tff(c_24,plain,(
    k5_xboole_0('#skF_1',k3_xboole_0('#skF_1','#skF_2')) != k4_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_4825,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4375,c_24])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 16:05:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.60/1.86  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.60/1.86  
% 4.60/1.86  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.60/1.87  %$ k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1
% 4.60/1.87  
% 4.60/1.87  %Foreground sorts:
% 4.60/1.87  
% 4.60/1.87  
% 4.60/1.87  %Background operators:
% 4.60/1.87  
% 4.60/1.87  
% 4.60/1.87  %Foreground operators:
% 4.60/1.87  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.60/1.87  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.60/1.87  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.60/1.87  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 4.60/1.87  tff('#skF_2', type, '#skF_2': $i).
% 4.60/1.87  tff('#skF_1', type, '#skF_1': $i).
% 4.60/1.87  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.60/1.87  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.60/1.87  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.60/1.87  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.60/1.87  
% 4.60/1.88  tff(f_29, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 4.60/1.88  tff(f_37, axiom, (![A, B]: (k4_xboole_0(A, k3_xboole_0(A, B)) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_xboole_1)).
% 4.60/1.88  tff(f_39, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 4.60/1.88  tff(f_45, axiom, (![A, B, C]: (k4_xboole_0(A, k4_xboole_0(B, C)) = k2_xboole_0(k4_xboole_0(A, B), k3_xboole_0(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_xboole_1)).
% 4.60/1.88  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 4.60/1.88  tff(f_41, axiom, (![A, B, C]: (k3_xboole_0(A, k4_xboole_0(B, C)) = k4_xboole_0(k3_xboole_0(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_xboole_1)).
% 4.60/1.88  tff(f_31, axiom, (![A, B]: (k5_xboole_0(A, B) = k2_xboole_0(k4_xboole_0(A, B), k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_xboole_0)).
% 4.60/1.88  tff(f_50, negated_conjecture, ~(![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 4.60/1.88  tff(c_4, plain, (![B_4, A_3]: (k3_xboole_0(B_4, A_3)=k3_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.60/1.88  tff(c_182, plain, (![A_34, B_35]: (k4_xboole_0(A_34, k3_xboole_0(A_34, B_35))=k4_xboole_0(A_34, B_35))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.60/1.88  tff(c_200, plain, (![B_4, A_3]: (k4_xboole_0(B_4, k3_xboole_0(A_3, B_4))=k4_xboole_0(B_4, A_3))), inference(superposition, [status(thm), theory('equality')], [c_4, c_182])).
% 4.60/1.88  tff(c_14, plain, (![A_12, B_13]: (k4_xboole_0(A_12, k4_xboole_0(A_12, B_13))=k3_xboole_0(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.60/1.88  tff(c_20, plain, (![A_19, B_20, C_21]: (k2_xboole_0(k4_xboole_0(A_19, B_20), k3_xboole_0(A_19, C_21))=k4_xboole_0(A_19, k4_xboole_0(B_20, C_21)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.60/1.88  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.60/1.88  tff(c_16, plain, (![A_14, B_15, C_16]: (k4_xboole_0(k3_xboole_0(A_14, B_15), C_16)=k3_xboole_0(A_14, k4_xboole_0(B_15, C_16)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.60/1.88  tff(c_12, plain, (![A_10, B_11]: (k4_xboole_0(A_10, k3_xboole_0(A_10, B_11))=k4_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.60/1.88  tff(c_338, plain, (![A_43, B_44]: (k2_xboole_0(k4_xboole_0(A_43, B_44), k4_xboole_0(B_44, A_43))=k5_xboole_0(A_43, B_44))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.60/1.88  tff(c_4208, plain, (![B_122, A_123]: (k2_xboole_0(k4_xboole_0(B_122, A_123), k4_xboole_0(A_123, B_122))=k5_xboole_0(A_123, B_122))), inference(superposition, [status(thm), theory('equality')], [c_338, c_2])).
% 4.60/1.88  tff(c_4330, plain, (![A_10, B_11]: (k2_xboole_0(k4_xboole_0(k3_xboole_0(A_10, B_11), A_10), k4_xboole_0(A_10, B_11))=k5_xboole_0(A_10, k3_xboole_0(A_10, B_11)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_4208])).
% 4.60/1.88  tff(c_4375, plain, (![A_10, B_11]: (k5_xboole_0(A_10, k3_xboole_0(A_10, B_11))=k4_xboole_0(A_10, B_11))), inference(demodulation, [status(thm), theory('equality')], [c_200, c_14, c_20, c_2, c_16, c_4330])).
% 4.60/1.88  tff(c_24, plain, (k5_xboole_0('#skF_1', k3_xboole_0('#skF_1', '#skF_2'))!=k4_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_50])).
% 4.60/1.88  tff(c_4825, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4375, c_24])).
% 4.60/1.88  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.60/1.88  
% 4.60/1.88  Inference rules
% 4.60/1.88  ----------------------
% 4.60/1.88  #Ref     : 0
% 4.60/1.88  #Sup     : 1185
% 4.60/1.88  #Fact    : 0
% 4.60/1.88  #Define  : 0
% 4.60/1.88  #Split   : 0
% 4.60/1.88  #Chain   : 0
% 4.60/1.88  #Close   : 0
% 4.60/1.88  
% 4.60/1.88  Ordering : KBO
% 4.60/1.88  
% 4.60/1.88  Simplification rules
% 4.60/1.88  ----------------------
% 4.60/1.88  #Subsume      : 12
% 4.60/1.88  #Demod        : 1347
% 4.60/1.88  #Tautology    : 823
% 4.60/1.88  #SimpNegUnit  : 0
% 4.60/1.88  #BackRed      : 4
% 4.60/1.88  
% 4.60/1.88  #Partial instantiations: 0
% 4.60/1.88  #Strategies tried      : 1
% 4.60/1.88  
% 4.60/1.88  Timing (in seconds)
% 4.60/1.88  ----------------------
% 4.60/1.88  Preprocessing        : 0.28
% 4.60/1.88  Parsing              : 0.15
% 4.60/1.88  CNF conversion       : 0.01
% 4.60/1.88  Main loop            : 0.84
% 4.60/1.88  Inferencing          : 0.26
% 4.60/1.88  Reduction            : 0.41
% 4.60/1.88  Demodulation         : 0.35
% 4.60/1.88  BG Simplification    : 0.03
% 4.60/1.88  Subsumption          : 0.10
% 4.60/1.88  Abstraction          : 0.05
% 4.60/1.88  MUC search           : 0.00
% 4.60/1.88  Cooper               : 0.00
% 4.60/1.88  Total                : 1.15
% 4.60/1.88  Index Insertion      : 0.00
% 4.60/1.88  Index Deletion       : 0.00
% 4.60/1.88  Index Matching       : 0.00
% 4.60/1.88  BG Taut test         : 0.00
%------------------------------------------------------------------------------

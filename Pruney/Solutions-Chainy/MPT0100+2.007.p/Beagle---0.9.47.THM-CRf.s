%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:44:38 EST 2020

% Result     : Theorem 5.57s
% Output     : CNFRefutation 5.70s
% Verified   : 
% Statistics : Number of formulae       :   32 (  35 expanded)
%              Number of leaves         :   16 (  18 expanded)
%              Depth                    :    5
%              Number of atoms          :   23 (  26 expanded)
%              Number of equality atoms :   22 (  25 expanded)
%              Maximal formula depth    :    4 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

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
    ! [A,B] : k2_xboole_0(k3_xboole_0(A,B),k4_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] : k2_xboole_0(A,k3_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_xboole_1)).

tff(f_35,axiom,(
    ! [A,B,C] : k2_xboole_0(k2_xboole_0(A,B),C) = k2_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k2_xboole_0(k4_xboole_0(A,B),k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_xboole_0)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_40,negated_conjecture,(
    ~ ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(k5_xboole_0(A,B),k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t93_xboole_1)).

tff(c_4,plain,(
    ! [B_4,A_3] : k3_xboole_0(B_4,A_3) = k3_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_125,plain,(
    ! [A_22,B_23] : k2_xboole_0(k3_xboole_0(A_22,B_23),k4_xboole_0(A_22,B_23)) = A_22 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_134,plain,(
    ! [B_4,A_3] : k2_xboole_0(k3_xboole_0(B_4,A_3),k4_xboole_0(A_3,B_4)) = A_3 ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_125])).

tff(c_8,plain,(
    ! [A_7,B_8] : k2_xboole_0(A_7,k3_xboole_0(A_7,B_8)) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_189,plain,(
    ! [A_28,B_29,C_30] : k2_xboole_0(k2_xboole_0(A_28,B_29),C_30) = k2_xboole_0(A_28,k2_xboole_0(B_29,C_30)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_614,plain,(
    ! [A_41,B_42,C_43] : k2_xboole_0(A_41,k2_xboole_0(k3_xboole_0(A_41,B_42),C_43)) = k2_xboole_0(A_41,C_43) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_189])).

tff(c_674,plain,(
    ! [B_4,A_3] : k2_xboole_0(B_4,k4_xboole_0(A_3,B_4)) = k2_xboole_0(B_4,A_3) ),
    inference(superposition,[status(thm),theory(equality)],[c_134,c_614])).

tff(c_6,plain,(
    ! [A_5,B_6] : k2_xboole_0(k4_xboole_0(A_5,B_6),k4_xboole_0(B_6,A_5)) = k5_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_12,plain,(
    ! [A_12,B_13] : k2_xboole_0(k3_xboole_0(A_12,B_13),k4_xboole_0(A_12,B_13)) = A_12 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_2385,plain,(
    ! [A_91,B_92,C_93] : k2_xboole_0(k3_xboole_0(A_91,B_92),k2_xboole_0(k4_xboole_0(A_91,B_92),C_93)) = k2_xboole_0(A_91,C_93) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_189])).

tff(c_2489,plain,(
    ! [A_5,B_6] : k2_xboole_0(k3_xboole_0(A_5,B_6),k5_xboole_0(A_5,B_6)) = k2_xboole_0(A_5,k4_xboole_0(B_6,A_5)) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_2385])).

tff(c_2534,plain,(
    ! [A_5,B_6] : k2_xboole_0(k3_xboole_0(A_5,B_6),k5_xboole_0(A_5,B_6)) = k2_xboole_0(A_5,B_6) ),
    inference(demodulation,[status(thm),theory(equality)],[c_674,c_2489])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_14,plain,(
    k2_xboole_0(k5_xboole_0('#skF_1','#skF_2'),k3_xboole_0('#skF_1','#skF_2')) != k2_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_15,plain,(
    k2_xboole_0(k3_xboole_0('#skF_1','#skF_2'),k5_xboole_0('#skF_1','#skF_2')) != k2_xboole_0('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_14])).

tff(c_4716,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2534,c_15])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n002.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:59:21 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.57/2.07  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.57/2.07  
% 5.57/2.07  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.57/2.08  %$ k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > #skF_2 > #skF_1
% 5.57/2.08  
% 5.57/2.08  %Foreground sorts:
% 5.57/2.08  
% 5.57/2.08  
% 5.57/2.08  %Background operators:
% 5.57/2.08  
% 5.57/2.08  
% 5.57/2.08  %Foreground operators:
% 5.57/2.08  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.57/2.08  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 5.57/2.08  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 5.57/2.08  tff('#skF_2', type, '#skF_2': $i).
% 5.57/2.08  tff('#skF_1', type, '#skF_1': $i).
% 5.57/2.08  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.57/2.08  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.57/2.08  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.57/2.08  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 5.57/2.08  
% 5.70/2.09  tff(f_29, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 5.70/2.09  tff(f_37, axiom, (![A, B]: (k2_xboole_0(k3_xboole_0(A, B), k4_xboole_0(A, B)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t51_xboole_1)).
% 5.70/2.09  tff(f_33, axiom, (![A, B]: (k2_xboole_0(A, k3_xboole_0(A, B)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_xboole_1)).
% 5.70/2.09  tff(f_35, axiom, (![A, B, C]: (k2_xboole_0(k2_xboole_0(A, B), C) = k2_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_1)).
% 5.70/2.09  tff(f_31, axiom, (![A, B]: (k5_xboole_0(A, B) = k2_xboole_0(k4_xboole_0(A, B), k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_xboole_0)).
% 5.70/2.09  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 5.70/2.09  tff(f_40, negated_conjecture, ~(![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(k5_xboole_0(A, B), k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t93_xboole_1)).
% 5.70/2.09  tff(c_4, plain, (![B_4, A_3]: (k3_xboole_0(B_4, A_3)=k3_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 5.70/2.09  tff(c_125, plain, (![A_22, B_23]: (k2_xboole_0(k3_xboole_0(A_22, B_23), k4_xboole_0(A_22, B_23))=A_22)), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.70/2.09  tff(c_134, plain, (![B_4, A_3]: (k2_xboole_0(k3_xboole_0(B_4, A_3), k4_xboole_0(A_3, B_4))=A_3)), inference(superposition, [status(thm), theory('equality')], [c_4, c_125])).
% 5.70/2.09  tff(c_8, plain, (![A_7, B_8]: (k2_xboole_0(A_7, k3_xboole_0(A_7, B_8))=A_7)), inference(cnfTransformation, [status(thm)], [f_33])).
% 5.70/2.09  tff(c_189, plain, (![A_28, B_29, C_30]: (k2_xboole_0(k2_xboole_0(A_28, B_29), C_30)=k2_xboole_0(A_28, k2_xboole_0(B_29, C_30)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.70/2.09  tff(c_614, plain, (![A_41, B_42, C_43]: (k2_xboole_0(A_41, k2_xboole_0(k3_xboole_0(A_41, B_42), C_43))=k2_xboole_0(A_41, C_43))), inference(superposition, [status(thm), theory('equality')], [c_8, c_189])).
% 5.70/2.09  tff(c_674, plain, (![B_4, A_3]: (k2_xboole_0(B_4, k4_xboole_0(A_3, B_4))=k2_xboole_0(B_4, A_3))), inference(superposition, [status(thm), theory('equality')], [c_134, c_614])).
% 5.70/2.09  tff(c_6, plain, (![A_5, B_6]: (k2_xboole_0(k4_xboole_0(A_5, B_6), k4_xboole_0(B_6, A_5))=k5_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.70/2.09  tff(c_12, plain, (![A_12, B_13]: (k2_xboole_0(k3_xboole_0(A_12, B_13), k4_xboole_0(A_12, B_13))=A_12)), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.70/2.09  tff(c_2385, plain, (![A_91, B_92, C_93]: (k2_xboole_0(k3_xboole_0(A_91, B_92), k2_xboole_0(k4_xboole_0(A_91, B_92), C_93))=k2_xboole_0(A_91, C_93))), inference(superposition, [status(thm), theory('equality')], [c_12, c_189])).
% 5.70/2.09  tff(c_2489, plain, (![A_5, B_6]: (k2_xboole_0(k3_xboole_0(A_5, B_6), k5_xboole_0(A_5, B_6))=k2_xboole_0(A_5, k4_xboole_0(B_6, A_5)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_2385])).
% 5.70/2.09  tff(c_2534, plain, (![A_5, B_6]: (k2_xboole_0(k3_xboole_0(A_5, B_6), k5_xboole_0(A_5, B_6))=k2_xboole_0(A_5, B_6))), inference(demodulation, [status(thm), theory('equality')], [c_674, c_2489])).
% 5.70/2.09  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 5.70/2.09  tff(c_14, plain, (k2_xboole_0(k5_xboole_0('#skF_1', '#skF_2'), k3_xboole_0('#skF_1', '#skF_2'))!=k2_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_40])).
% 5.70/2.09  tff(c_15, plain, (k2_xboole_0(k3_xboole_0('#skF_1', '#skF_2'), k5_xboole_0('#skF_1', '#skF_2'))!=k2_xboole_0('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_14])).
% 5.70/2.09  tff(c_4716, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2534, c_15])).
% 5.70/2.09  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.70/2.09  
% 5.70/2.09  Inference rules
% 5.70/2.09  ----------------------
% 5.70/2.09  #Ref     : 0
% 5.70/2.09  #Sup     : 1161
% 5.70/2.09  #Fact    : 0
% 5.70/2.09  #Define  : 0
% 5.70/2.09  #Split   : 0
% 5.70/2.09  #Chain   : 0
% 5.70/2.09  #Close   : 0
% 5.70/2.09  
% 5.70/2.09  Ordering : KBO
% 5.70/2.09  
% 5.70/2.09  Simplification rules
% 5.70/2.09  ----------------------
% 5.70/2.09  #Subsume      : 54
% 5.70/2.09  #Demod        : 655
% 5.70/2.09  #Tautology    : 431
% 5.70/2.09  #SimpNegUnit  : 0
% 5.70/2.09  #BackRed      : 1
% 5.70/2.09  
% 5.70/2.09  #Partial instantiations: 0
% 5.70/2.09  #Strategies tried      : 1
% 5.70/2.09  
% 5.70/2.09  Timing (in seconds)
% 5.70/2.09  ----------------------
% 5.70/2.09  Preprocessing        : 0.27
% 5.70/2.09  Parsing              : 0.15
% 5.70/2.09  CNF conversion       : 0.02
% 5.70/2.09  Main loop            : 1.04
% 5.70/2.09  Inferencing          : 0.29
% 5.70/2.09  Reduction            : 0.55
% 5.70/2.09  Demodulation         : 0.50
% 5.70/2.09  BG Simplification    : 0.04
% 5.70/2.09  Subsumption          : 0.11
% 5.70/2.09  Abstraction          : 0.06
% 5.70/2.09  MUC search           : 0.00
% 5.70/2.09  Cooper               : 0.00
% 5.70/2.09  Total                : 1.34
% 5.70/2.09  Index Insertion      : 0.00
% 5.70/2.09  Index Deletion       : 0.00
% 5.70/2.09  Index Matching       : 0.00
% 5.70/2.09  BG Taut test         : 0.00
%------------------------------------------------------------------------------

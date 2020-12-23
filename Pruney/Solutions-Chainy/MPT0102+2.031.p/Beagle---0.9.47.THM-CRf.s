%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:44:45 EST 2020

% Result     : Theorem 14.88s
% Output     : CNFRefutation 14.88s
% Verified   : 
% Statistics : Number of formulae       :   36 (  58 expanded)
%              Number of leaves         :   17 (  27 expanded)
%              Depth                    :    7
%              Number of atoms          :   26 (  48 expanded)
%              Number of equality atoms :   25 (  47 expanded)
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
    ! [A,B] : k2_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

tff(f_37,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_39,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_xboole_1)).

tff(f_35,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_42,negated_conjecture,(
    ~ ! [A,B] : k3_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_xboole_1)).

tff(c_4,plain,(
    ! [A_3] : k2_xboole_0(A_3,A_3) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_12,plain,(
    ! [A_12] : k5_xboole_0(A_12,A_12) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_6,plain,(
    ! [A_5] : k3_xboole_0(A_5,A_5) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_485,plain,(
    ! [A_33,B_34] : k5_xboole_0(k5_xboole_0(A_33,B_34),k3_xboole_0(A_33,B_34)) = k2_xboole_0(A_33,B_34) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_549,plain,(
    ! [A_5] : k5_xboole_0(k5_xboole_0(A_5,A_5),A_5) = k2_xboole_0(A_5,A_5) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_485])).

tff(c_555,plain,(
    ! [A_5] : k5_xboole_0(k1_xboole_0,A_5) = A_5 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_12,c_549])).

tff(c_91,plain,(
    ! [A_22,B_23,C_24] : k5_xboole_0(k5_xboole_0(A_22,B_23),C_24) = k5_xboole_0(A_22,k5_xboole_0(B_23,C_24)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_130,plain,(
    ! [A_12,C_24] : k5_xboole_0(A_12,k5_xboole_0(A_12,C_24)) = k5_xboole_0(k1_xboole_0,C_24) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_91])).

tff(c_558,plain,(
    ! [A_12,C_24] : k5_xboole_0(A_12,k5_xboole_0(A_12,C_24)) = C_24 ),
    inference(demodulation,[status(thm),theory(equality)],[c_555,c_130])).

tff(c_14,plain,(
    ! [A_13,B_14] : k5_xboole_0(k5_xboole_0(A_13,B_14),k3_xboole_0(A_13,B_14)) = k2_xboole_0(A_13,B_14) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_2,plain,(
    ! [B_2,A_1] : k5_xboole_0(B_2,A_1) = k5_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_3577,plain,(
    ! [B_76,A_77,C_78] : k5_xboole_0(k5_xboole_0(B_76,A_77),C_78) = k5_xboole_0(A_77,k5_xboole_0(B_76,C_78)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_91])).

tff(c_3921,plain,(
    ! [B_79,A_80] : k5_xboole_0(B_79,k5_xboole_0(A_80,k3_xboole_0(A_80,B_79))) = k2_xboole_0(A_80,B_79) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_3577])).

tff(c_3978,plain,(
    ! [B_79,A_80] : k5_xboole_0(B_79,k2_xboole_0(A_80,B_79)) = k5_xboole_0(A_80,k3_xboole_0(A_80,B_79)) ),
    inference(superposition,[status(thm),theory(equality)],[c_3921,c_558])).

tff(c_10,plain,(
    ! [A_9,B_10,C_11] : k5_xboole_0(k5_xboole_0(A_9,B_10),C_11) = k5_xboole_0(A_9,k5_xboole_0(B_10,C_11)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_16,plain,(
    k5_xboole_0(k5_xboole_0('#skF_1','#skF_2'),k2_xboole_0('#skF_1','#skF_2')) != k3_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_17,plain,(
    k5_xboole_0('#skF_1',k5_xboole_0('#skF_2',k2_xboole_0('#skF_1','#skF_2'))) != k3_xboole_0('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_16])).

tff(c_30394,plain,(
    k5_xboole_0('#skF_1',k5_xboole_0('#skF_1',k3_xboole_0('#skF_1','#skF_2'))) != k3_xboole_0('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3978,c_17])).

tff(c_30397,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_558,c_30394])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:27:32 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 14.88/7.79  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 14.88/7.79  
% 14.88/7.79  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 14.88/7.79  %$ k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1
% 14.88/7.79  
% 14.88/7.79  %Foreground sorts:
% 14.88/7.79  
% 14.88/7.79  
% 14.88/7.79  %Background operators:
% 14.88/7.79  
% 14.88/7.79  
% 14.88/7.79  %Foreground operators:
% 14.88/7.79  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 14.88/7.79  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 14.88/7.79  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 14.88/7.79  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 14.88/7.79  tff('#skF_2', type, '#skF_2': $i).
% 14.88/7.79  tff('#skF_1', type, '#skF_1': $i).
% 14.88/7.79  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 14.88/7.79  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 14.88/7.79  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 14.88/7.79  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 14.88/7.79  
% 14.88/7.80  tff(f_29, axiom, (![A, B]: (k2_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 14.88/7.80  tff(f_37, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_xboole_1)).
% 14.88/7.80  tff(f_31, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 14.88/7.80  tff(f_39, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_xboole_1)).
% 14.88/7.80  tff(f_35, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_xboole_1)).
% 14.88/7.80  tff(f_27, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 14.88/7.80  tff(f_42, negated_conjecture, ~(![A, B]: (k3_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k2_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t95_xboole_1)).
% 14.88/7.80  tff(c_4, plain, (![A_3]: (k2_xboole_0(A_3, A_3)=A_3)), inference(cnfTransformation, [status(thm)], [f_29])).
% 14.88/7.80  tff(c_12, plain, (![A_12]: (k5_xboole_0(A_12, A_12)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 14.88/7.80  tff(c_6, plain, (![A_5]: (k3_xboole_0(A_5, A_5)=A_5)), inference(cnfTransformation, [status(thm)], [f_31])).
% 14.88/7.80  tff(c_485, plain, (![A_33, B_34]: (k5_xboole_0(k5_xboole_0(A_33, B_34), k3_xboole_0(A_33, B_34))=k2_xboole_0(A_33, B_34))), inference(cnfTransformation, [status(thm)], [f_39])).
% 14.88/7.80  tff(c_549, plain, (![A_5]: (k5_xboole_0(k5_xboole_0(A_5, A_5), A_5)=k2_xboole_0(A_5, A_5))), inference(superposition, [status(thm), theory('equality')], [c_6, c_485])).
% 14.88/7.80  tff(c_555, plain, (![A_5]: (k5_xboole_0(k1_xboole_0, A_5)=A_5)), inference(demodulation, [status(thm), theory('equality')], [c_4, c_12, c_549])).
% 14.88/7.80  tff(c_91, plain, (![A_22, B_23, C_24]: (k5_xboole_0(k5_xboole_0(A_22, B_23), C_24)=k5_xboole_0(A_22, k5_xboole_0(B_23, C_24)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 14.88/7.80  tff(c_130, plain, (![A_12, C_24]: (k5_xboole_0(A_12, k5_xboole_0(A_12, C_24))=k5_xboole_0(k1_xboole_0, C_24))), inference(superposition, [status(thm), theory('equality')], [c_12, c_91])).
% 14.88/7.80  tff(c_558, plain, (![A_12, C_24]: (k5_xboole_0(A_12, k5_xboole_0(A_12, C_24))=C_24)), inference(demodulation, [status(thm), theory('equality')], [c_555, c_130])).
% 14.88/7.80  tff(c_14, plain, (![A_13, B_14]: (k5_xboole_0(k5_xboole_0(A_13, B_14), k3_xboole_0(A_13, B_14))=k2_xboole_0(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_39])).
% 14.88/7.80  tff(c_2, plain, (![B_2, A_1]: (k5_xboole_0(B_2, A_1)=k5_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 14.88/7.80  tff(c_3577, plain, (![B_76, A_77, C_78]: (k5_xboole_0(k5_xboole_0(B_76, A_77), C_78)=k5_xboole_0(A_77, k5_xboole_0(B_76, C_78)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_91])).
% 14.88/7.80  tff(c_3921, plain, (![B_79, A_80]: (k5_xboole_0(B_79, k5_xboole_0(A_80, k3_xboole_0(A_80, B_79)))=k2_xboole_0(A_80, B_79))), inference(superposition, [status(thm), theory('equality')], [c_14, c_3577])).
% 14.88/7.80  tff(c_3978, plain, (![B_79, A_80]: (k5_xboole_0(B_79, k2_xboole_0(A_80, B_79))=k5_xboole_0(A_80, k3_xboole_0(A_80, B_79)))), inference(superposition, [status(thm), theory('equality')], [c_3921, c_558])).
% 14.88/7.80  tff(c_10, plain, (![A_9, B_10, C_11]: (k5_xboole_0(k5_xboole_0(A_9, B_10), C_11)=k5_xboole_0(A_9, k5_xboole_0(B_10, C_11)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 14.88/7.80  tff(c_16, plain, (k5_xboole_0(k5_xboole_0('#skF_1', '#skF_2'), k2_xboole_0('#skF_1', '#skF_2'))!=k3_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_42])).
% 14.88/7.80  tff(c_17, plain, (k5_xboole_0('#skF_1', k5_xboole_0('#skF_2', k2_xboole_0('#skF_1', '#skF_2')))!=k3_xboole_0('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_10, c_16])).
% 14.88/7.80  tff(c_30394, plain, (k5_xboole_0('#skF_1', k5_xboole_0('#skF_1', k3_xboole_0('#skF_1', '#skF_2')))!=k3_xboole_0('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_3978, c_17])).
% 14.88/7.80  tff(c_30397, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_558, c_30394])).
% 14.88/7.80  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 14.88/7.80  
% 14.88/7.80  Inference rules
% 14.88/7.80  ----------------------
% 14.88/7.80  #Ref     : 0
% 14.88/7.80  #Sup     : 8032
% 14.88/7.80  #Fact    : 0
% 14.88/7.80  #Define  : 0
% 14.88/7.80  #Split   : 0
% 14.88/7.80  #Chain   : 0
% 14.88/7.80  #Close   : 0
% 14.88/7.80  
% 14.88/7.80  Ordering : KBO
% 14.88/7.80  
% 14.88/7.80  Simplification rules
% 14.88/7.80  ----------------------
% 14.88/7.80  #Subsume      : 595
% 14.88/7.80  #Demod        : 10569
% 14.88/7.80  #Tautology    : 2597
% 14.88/7.80  #SimpNegUnit  : 0
% 14.88/7.80  #BackRed      : 6
% 14.88/7.80  
% 14.88/7.80  #Partial instantiations: 0
% 14.88/7.80  #Strategies tried      : 1
% 14.88/7.80  
% 14.88/7.80  Timing (in seconds)
% 14.88/7.80  ----------------------
% 14.88/7.80  Preprocessing        : 0.25
% 14.88/7.80  Parsing              : 0.14
% 14.88/7.80  CNF conversion       : 0.01
% 14.88/7.80  Main loop            : 6.81
% 14.88/7.80  Inferencing          : 0.88
% 14.88/7.80  Reduction            : 4.96
% 14.88/7.80  Demodulation         : 4.73
% 14.88/7.80  BG Simplification    : 0.15
% 14.88/7.80  Subsumption          : 0.64
% 14.88/7.80  Abstraction          : 0.24
% 14.88/7.80  MUC search           : 0.00
% 14.88/7.80  Cooper               : 0.00
% 14.88/7.80  Total                : 7.08
% 14.88/7.80  Index Insertion      : 0.00
% 14.88/7.81  Index Deletion       : 0.00
% 14.88/7.81  Index Matching       : 0.00
% 14.88/7.81  BG Taut test         : 0.00
%------------------------------------------------------------------------------

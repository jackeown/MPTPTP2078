%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:00:22 EST 2020

% Result     : Theorem 1.59s
% Output     : CNFRefutation 1.71s
% Verified   : 
% Statistics : Number of formulae       :   30 (  41 expanded)
%              Number of leaves         :   16 (  21 expanded)
%              Depth                    :    7
%              Number of atoms          :   26 (  38 expanded)
%              Number of equality atoms :   18 (  29 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_relat_1 > k8_relat_1 > k6_subset_1 > k4_xboole_0 > k3_xboole_0 > #nlpp > k1_xboole_0 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k8_relat_1,type,(
    k8_relat_1: ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k6_subset_1,type,(
    k6_subset_1: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(f_42,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => k8_relat_1(k1_xboole_0,A) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t137_relat_1)).

tff(f_27,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_29,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_31,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k8_relat_1(k6_subset_1(A,B),C) = k6_subset_1(k8_relat_1(A,C),k8_relat_1(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t136_relat_1)).

tff(c_12,plain,(
    k8_relat_1(k1_xboole_0,'#skF_1') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_14,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_2,plain,(
    ! [A_1] : k3_xboole_0(A_1,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4,plain,(
    ! [A_2] : k4_xboole_0(A_2,k1_xboole_0) = A_2 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_41,plain,(
    ! [A_14,B_15] : k4_xboole_0(A_14,k4_xboole_0(A_14,B_15)) = k3_xboole_0(A_14,B_15) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_56,plain,(
    ! [A_2] : k4_xboole_0(A_2,A_2) = k3_xboole_0(A_2,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_41])).

tff(c_59,plain,(
    ! [A_2] : k4_xboole_0(A_2,A_2) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_56])).

tff(c_8,plain,(
    ! [A_5,B_6] : k6_subset_1(A_5,B_6) = k4_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_10,plain,(
    ! [A_7,C_9,B_8] :
      ( k6_subset_1(k8_relat_1(A_7,C_9),k8_relat_1(B_8,C_9)) = k8_relat_1(k6_subset_1(A_7,B_8),C_9)
      | ~ v1_relat_1(C_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_162,plain,(
    ! [A_22,C_23,B_24] :
      ( k4_xboole_0(k8_relat_1(A_22,C_23),k8_relat_1(B_24,C_23)) = k8_relat_1(k4_xboole_0(A_22,B_24),C_23)
      | ~ v1_relat_1(C_23) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_8,c_10])).

tff(c_172,plain,(
    ! [B_24,C_23] :
      ( k8_relat_1(k4_xboole_0(B_24,B_24),C_23) = k1_xboole_0
      | ~ v1_relat_1(C_23) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_162,c_59])).

tff(c_188,plain,(
    ! [C_25] :
      ( k8_relat_1(k1_xboole_0,C_25) = k1_xboole_0
      | ~ v1_relat_1(C_25) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_59,c_172])).

tff(c_191,plain,(
    k8_relat_1(k1_xboole_0,'#skF_1') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_14,c_188])).

tff(c_195,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_12,c_191])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:47:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.59/1.22  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.59/1.23  
% 1.59/1.23  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.59/1.23  %$ v1_relat_1 > k8_relat_1 > k6_subset_1 > k4_xboole_0 > k3_xboole_0 > #nlpp > k1_xboole_0 > #skF_1
% 1.59/1.23  
% 1.59/1.23  %Foreground sorts:
% 1.59/1.23  
% 1.59/1.23  
% 1.59/1.23  %Background operators:
% 1.59/1.23  
% 1.59/1.23  
% 1.59/1.23  %Foreground operators:
% 1.59/1.23  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 1.59/1.23  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.59/1.23  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.59/1.23  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.59/1.23  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 1.59/1.23  tff('#skF_1', type, '#skF_1': $i).
% 1.59/1.23  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.59/1.23  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.59/1.23  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.59/1.23  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.59/1.23  
% 1.71/1.24  tff(f_42, negated_conjecture, ~(![A]: (v1_relat_1(A) => (k8_relat_1(k1_xboole_0, A) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t137_relat_1)).
% 1.71/1.24  tff(f_27, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 1.71/1.24  tff(f_29, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 1.71/1.24  tff(f_31, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 1.71/1.24  tff(f_33, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 1.71/1.24  tff(f_37, axiom, (![A, B, C]: (v1_relat_1(C) => (k8_relat_1(k6_subset_1(A, B), C) = k6_subset_1(k8_relat_1(A, C), k8_relat_1(B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t136_relat_1)).
% 1.71/1.24  tff(c_12, plain, (k8_relat_1(k1_xboole_0, '#skF_1')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.71/1.24  tff(c_14, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.71/1.24  tff(c_2, plain, (![A_1]: (k3_xboole_0(A_1, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.71/1.24  tff(c_4, plain, (![A_2]: (k4_xboole_0(A_2, k1_xboole_0)=A_2)), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.71/1.24  tff(c_41, plain, (![A_14, B_15]: (k4_xboole_0(A_14, k4_xboole_0(A_14, B_15))=k3_xboole_0(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.71/1.24  tff(c_56, plain, (![A_2]: (k4_xboole_0(A_2, A_2)=k3_xboole_0(A_2, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_4, c_41])).
% 1.71/1.24  tff(c_59, plain, (![A_2]: (k4_xboole_0(A_2, A_2)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_2, c_56])).
% 1.71/1.24  tff(c_8, plain, (![A_5, B_6]: (k6_subset_1(A_5, B_6)=k4_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.71/1.24  tff(c_10, plain, (![A_7, C_9, B_8]: (k6_subset_1(k8_relat_1(A_7, C_9), k8_relat_1(B_8, C_9))=k8_relat_1(k6_subset_1(A_7, B_8), C_9) | ~v1_relat_1(C_9))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.71/1.24  tff(c_162, plain, (![A_22, C_23, B_24]: (k4_xboole_0(k8_relat_1(A_22, C_23), k8_relat_1(B_24, C_23))=k8_relat_1(k4_xboole_0(A_22, B_24), C_23) | ~v1_relat_1(C_23))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_8, c_10])).
% 1.71/1.24  tff(c_172, plain, (![B_24, C_23]: (k8_relat_1(k4_xboole_0(B_24, B_24), C_23)=k1_xboole_0 | ~v1_relat_1(C_23))), inference(superposition, [status(thm), theory('equality')], [c_162, c_59])).
% 1.71/1.24  tff(c_188, plain, (![C_25]: (k8_relat_1(k1_xboole_0, C_25)=k1_xboole_0 | ~v1_relat_1(C_25))), inference(demodulation, [status(thm), theory('equality')], [c_59, c_172])).
% 1.71/1.24  tff(c_191, plain, (k8_relat_1(k1_xboole_0, '#skF_1')=k1_xboole_0), inference(resolution, [status(thm)], [c_14, c_188])).
% 1.71/1.24  tff(c_195, plain, $false, inference(negUnitSimplification, [status(thm)], [c_12, c_191])).
% 1.71/1.24  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.71/1.24  
% 1.71/1.24  Inference rules
% 1.71/1.24  ----------------------
% 1.71/1.24  #Ref     : 0
% 1.71/1.24  #Sup     : 43
% 1.71/1.24  #Fact    : 0
% 1.71/1.24  #Define  : 0
% 1.71/1.24  #Split   : 0
% 1.71/1.24  #Chain   : 0
% 1.71/1.24  #Close   : 0
% 1.71/1.24  
% 1.71/1.24  Ordering : KBO
% 1.71/1.24  
% 1.71/1.24  Simplification rules
% 1.71/1.24  ----------------------
% 1.71/1.24  #Subsume      : 0
% 1.71/1.24  #Demod        : 24
% 1.71/1.24  #Tautology    : 29
% 1.71/1.24  #SimpNegUnit  : 1
% 1.71/1.24  #BackRed      : 0
% 1.71/1.24  
% 1.71/1.24  #Partial instantiations: 0
% 1.71/1.24  #Strategies tried      : 1
% 1.71/1.24  
% 1.71/1.24  Timing (in seconds)
% 1.71/1.24  ----------------------
% 1.71/1.24  Preprocessing        : 0.26
% 1.71/1.24  Parsing              : 0.14
% 1.71/1.24  CNF conversion       : 0.01
% 1.71/1.24  Main loop            : 0.13
% 1.71/1.24  Inferencing          : 0.05
% 1.71/1.24  Reduction            : 0.04
% 1.71/1.24  Demodulation         : 0.04
% 1.71/1.24  BG Simplification    : 0.01
% 1.71/1.24  Subsumption          : 0.01
% 1.71/1.24  Abstraction          : 0.01
% 1.71/1.24  MUC search           : 0.00
% 1.71/1.24  Cooper               : 0.00
% 1.71/1.24  Total                : 0.41
% 1.71/1.24  Index Insertion      : 0.00
% 1.71/1.24  Index Deletion       : 0.00
% 1.71/1.24  Index Matching       : 0.00
% 1.71/1.24  BG Taut test         : 0.00
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:00:22 EST 2020

% Result     : Theorem 1.83s
% Output     : CNFRefutation 1.83s
% Verified   : 
% Statistics : Number of formulae       :   36 (  47 expanded)
%              Number of leaves         :   22 (  27 expanded)
%              Depth                    :    7
%              Number of atoms          :   26 (  38 expanded)
%              Number of equality atoms :   18 (  29 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_relat_1 > k5_enumset1 > k4_enumset1 > k2_enumset1 > k8_relat_1 > k6_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > k1_xboole_0 > #skF_1

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

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k6_subset_1,type,(
    k6_subset_1: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_50,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => k8_relat_1(k1_xboole_0,A) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t137_relat_1)).

tff(f_31,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_29,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k8_relat_1(k6_subset_1(A,B),C) = k6_subset_1(k8_relat_1(A,C),k8_relat_1(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t136_relat_1)).

tff(c_20,plain,(
    k8_relat_1(k1_xboole_0,'#skF_1') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_22,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_6,plain,(
    ! [A_5] : k5_xboole_0(A_5,A_5) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_2,plain,(
    ! [A_1] : k3_xboole_0(A_1,A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_67,plain,(
    ! [A_33,B_34] : k5_xboole_0(A_33,k3_xboole_0(A_33,B_34)) = k4_xboole_0(A_33,B_34) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_76,plain,(
    ! [A_1] : k5_xboole_0(A_1,A_1) = k4_xboole_0(A_1,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_67])).

tff(c_79,plain,(
    ! [A_1] : k4_xboole_0(A_1,A_1) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_76])).

tff(c_14,plain,(
    ! [A_18,B_19] : k6_subset_1(A_18,B_19) = k4_xboole_0(A_18,B_19) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_18,plain,(
    ! [A_22,C_24,B_23] :
      ( k6_subset_1(k8_relat_1(A_22,C_24),k8_relat_1(B_23,C_24)) = k8_relat_1(k6_subset_1(A_22,B_23),C_24)
      | ~ v1_relat_1(C_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_96,plain,(
    ! [A_40,C_41,B_42] :
      ( k4_xboole_0(k8_relat_1(A_40,C_41),k8_relat_1(B_42,C_41)) = k8_relat_1(k4_xboole_0(A_40,B_42),C_41)
      | ~ v1_relat_1(C_41) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_14,c_18])).

tff(c_103,plain,(
    ! [B_42,C_41] :
      ( k8_relat_1(k4_xboole_0(B_42,B_42),C_41) = k1_xboole_0
      | ~ v1_relat_1(C_41) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_96,c_79])).

tff(c_115,plain,(
    ! [C_43] :
      ( k8_relat_1(k1_xboole_0,C_43) = k1_xboole_0
      | ~ v1_relat_1(C_43) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_79,c_103])).

tff(c_118,plain,(
    k8_relat_1(k1_xboole_0,'#skF_1') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_22,c_115])).

tff(c_122,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_20,c_118])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:45:04 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.83/1.18  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.83/1.19  
% 1.83/1.19  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.83/1.19  %$ v1_relat_1 > k5_enumset1 > k4_enumset1 > k2_enumset1 > k8_relat_1 > k6_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > k1_xboole_0 > #skF_1
% 1.83/1.19  
% 1.83/1.19  %Foreground sorts:
% 1.83/1.19  
% 1.83/1.19  
% 1.83/1.19  %Background operators:
% 1.83/1.19  
% 1.83/1.19  
% 1.83/1.19  %Foreground operators:
% 1.83/1.19  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 1.83/1.19  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.83/1.19  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.83/1.19  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.83/1.19  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 1.83/1.19  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.83/1.19  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.83/1.19  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 1.83/1.19  tff('#skF_1', type, '#skF_1': $i).
% 1.83/1.19  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 1.83/1.19  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.83/1.19  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.83/1.19  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.83/1.19  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.83/1.19  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 1.83/1.19  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 1.83/1.19  
% 1.83/1.20  tff(f_50, negated_conjecture, ~(![A]: (v1_relat_1(A) => (k8_relat_1(k1_xboole_0, A) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t137_relat_1)).
% 1.83/1.20  tff(f_31, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_xboole_1)).
% 1.83/1.20  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 1.83/1.20  tff(f_29, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 1.83/1.20  tff(f_39, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 1.83/1.20  tff(f_45, axiom, (![A, B, C]: (v1_relat_1(C) => (k8_relat_1(k6_subset_1(A, B), C) = k6_subset_1(k8_relat_1(A, C), k8_relat_1(B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t136_relat_1)).
% 1.83/1.20  tff(c_20, plain, (k8_relat_1(k1_xboole_0, '#skF_1')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.83/1.20  tff(c_22, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.83/1.20  tff(c_6, plain, (![A_5]: (k5_xboole_0(A_5, A_5)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.83/1.20  tff(c_2, plain, (![A_1]: (k3_xboole_0(A_1, A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.83/1.20  tff(c_67, plain, (![A_33, B_34]: (k5_xboole_0(A_33, k3_xboole_0(A_33, B_34))=k4_xboole_0(A_33, B_34))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.83/1.20  tff(c_76, plain, (![A_1]: (k5_xboole_0(A_1, A_1)=k4_xboole_0(A_1, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_67])).
% 1.83/1.20  tff(c_79, plain, (![A_1]: (k4_xboole_0(A_1, A_1)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_76])).
% 1.83/1.20  tff(c_14, plain, (![A_18, B_19]: (k6_subset_1(A_18, B_19)=k4_xboole_0(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.83/1.20  tff(c_18, plain, (![A_22, C_24, B_23]: (k6_subset_1(k8_relat_1(A_22, C_24), k8_relat_1(B_23, C_24))=k8_relat_1(k6_subset_1(A_22, B_23), C_24) | ~v1_relat_1(C_24))), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.83/1.20  tff(c_96, plain, (![A_40, C_41, B_42]: (k4_xboole_0(k8_relat_1(A_40, C_41), k8_relat_1(B_42, C_41))=k8_relat_1(k4_xboole_0(A_40, B_42), C_41) | ~v1_relat_1(C_41))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_14, c_18])).
% 1.83/1.20  tff(c_103, plain, (![B_42, C_41]: (k8_relat_1(k4_xboole_0(B_42, B_42), C_41)=k1_xboole_0 | ~v1_relat_1(C_41))), inference(superposition, [status(thm), theory('equality')], [c_96, c_79])).
% 1.83/1.20  tff(c_115, plain, (![C_43]: (k8_relat_1(k1_xboole_0, C_43)=k1_xboole_0 | ~v1_relat_1(C_43))), inference(demodulation, [status(thm), theory('equality')], [c_79, c_103])).
% 1.83/1.20  tff(c_118, plain, (k8_relat_1(k1_xboole_0, '#skF_1')=k1_xboole_0), inference(resolution, [status(thm)], [c_22, c_115])).
% 1.83/1.20  tff(c_122, plain, $false, inference(negUnitSimplification, [status(thm)], [c_20, c_118])).
% 1.83/1.20  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.83/1.20  
% 1.83/1.20  Inference rules
% 1.83/1.20  ----------------------
% 1.83/1.20  #Ref     : 0
% 1.83/1.20  #Sup     : 22
% 1.83/1.20  #Fact    : 0
% 1.83/1.20  #Define  : 0
% 1.83/1.20  #Split   : 0
% 1.83/1.20  #Chain   : 0
% 1.83/1.20  #Close   : 0
% 1.83/1.20  
% 1.83/1.20  Ordering : KBO
% 1.83/1.20  
% 1.83/1.20  Simplification rules
% 1.83/1.20  ----------------------
% 1.83/1.20  #Subsume      : 0
% 1.83/1.20  #Demod        : 5
% 1.83/1.20  #Tautology    : 18
% 1.83/1.20  #SimpNegUnit  : 1
% 1.83/1.20  #BackRed      : 0
% 1.83/1.20  
% 1.83/1.20  #Partial instantiations: 0
% 1.83/1.20  #Strategies tried      : 1
% 1.83/1.20  
% 1.83/1.20  Timing (in seconds)
% 1.83/1.20  ----------------------
% 1.83/1.20  Preprocessing        : 0.30
% 1.83/1.20  Parsing              : 0.17
% 1.83/1.20  CNF conversion       : 0.02
% 1.83/1.20  Main loop            : 0.10
% 1.83/1.20  Inferencing          : 0.04
% 1.83/1.20  Reduction            : 0.03
% 1.83/1.20  Demodulation         : 0.03
% 1.83/1.20  BG Simplification    : 0.01
% 1.83/1.20  Subsumption          : 0.01
% 1.83/1.20  Abstraction          : 0.01
% 1.83/1.20  MUC search           : 0.00
% 1.83/1.20  Cooper               : 0.00
% 1.83/1.20  Total                : 0.43
% 1.83/1.20  Index Insertion      : 0.00
% 1.83/1.20  Index Deletion       : 0.00
% 1.83/1.20  Index Matching       : 0.00
% 1.83/1.20  BG Taut test         : 0.00
%------------------------------------------------------------------------------

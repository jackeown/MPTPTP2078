%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:00:22 EST 2020

% Result     : Theorem 1.82s
% Output     : CNFRefutation 1.92s
% Verified   : 
% Statistics : Number of formulae       :   45 (  62 expanded)
%              Number of leaves         :   27 (  34 expanded)
%              Depth                    :    9
%              Number of atoms          :   32 (  50 expanded)
%              Number of equality atoms :   24 (  41 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_relat_1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k8_relat_1 > k6_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k8_relat_1,type,(
    k8_relat_1: ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

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

tff(f_56,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => k8_relat_1(k1_xboole_0,A) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t137_relat_1)).

tff(f_29,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_45,axiom,(
    ! [A] : k1_setfam_1(k1_tarski(A)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_setfam_1)).

tff(f_31,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_47,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_27,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k8_relat_1(k6_subset_1(A,B),C) = k6_subset_1(k8_relat_1(A,C),k8_relat_1(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t136_relat_1)).

tff(c_26,plain,(
    k8_relat_1(k1_xboole_0,'#skF_1') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_28,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_4,plain,(
    ! [A_3] : k5_xboole_0(A_3,A_3) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_20,plain,(
    ! [A_27] : k1_setfam_1(k1_tarski(A_27)) = A_27 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_6,plain,(
    ! [A_4] : k2_tarski(A_4,A_4) = k1_tarski(A_4) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_73,plain,(
    ! [A_40,B_41] : k1_setfam_1(k2_tarski(A_40,B_41)) = k3_xboole_0(A_40,B_41) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_82,plain,(
    ! [A_4] : k3_xboole_0(A_4,A_4) = k1_setfam_1(k1_tarski(A_4)) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_73])).

tff(c_85,plain,(
    ! [A_4] : k3_xboole_0(A_4,A_4) = A_4 ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_82])).

tff(c_95,plain,(
    ! [A_43,B_44] : k5_xboole_0(A_43,k3_xboole_0(A_43,B_44)) = k4_xboole_0(A_43,B_44) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_104,plain,(
    ! [A_4] : k5_xboole_0(A_4,A_4) = k4_xboole_0(A_4,A_4) ),
    inference(superposition,[status(thm),theory(equality)],[c_85,c_95])).

tff(c_107,plain,(
    ! [A_4] : k4_xboole_0(A_4,A_4) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_104])).

tff(c_18,plain,(
    ! [A_25,B_26] : k6_subset_1(A_25,B_26) = k4_xboole_0(A_25,B_26) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_24,plain,(
    ! [A_30,C_32,B_31] :
      ( k6_subset_1(k8_relat_1(A_30,C_32),k8_relat_1(B_31,C_32)) = k8_relat_1(k6_subset_1(A_30,B_31),C_32)
      | ~ v1_relat_1(C_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_142,plain,(
    ! [A_58,C_59,B_60] :
      ( k4_xboole_0(k8_relat_1(A_58,C_59),k8_relat_1(B_60,C_59)) = k8_relat_1(k4_xboole_0(A_58,B_60),C_59)
      | ~ v1_relat_1(C_59) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_18,c_24])).

tff(c_149,plain,(
    ! [B_60,C_59] :
      ( k8_relat_1(k4_xboole_0(B_60,B_60),C_59) = k1_xboole_0
      | ~ v1_relat_1(C_59) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_142,c_107])).

tff(c_170,plain,(
    ! [C_67] :
      ( k8_relat_1(k1_xboole_0,C_67) = k1_xboole_0
      | ~ v1_relat_1(C_67) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_107,c_149])).

tff(c_173,plain,(
    k8_relat_1(k1_xboole_0,'#skF_1') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_28,c_170])).

tff(c_177,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_173])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:37:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.82/1.17  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.82/1.17  
% 1.82/1.17  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.82/1.17  %$ v1_relat_1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k8_relat_1 > k6_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_1
% 1.82/1.17  
% 1.82/1.17  %Foreground sorts:
% 1.82/1.17  
% 1.82/1.17  
% 1.82/1.17  %Background operators:
% 1.82/1.17  
% 1.82/1.17  
% 1.82/1.17  %Foreground operators:
% 1.82/1.17  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 1.82/1.17  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.82/1.17  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.82/1.17  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.82/1.17  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.82/1.17  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 1.82/1.17  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 1.82/1.17  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.82/1.17  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.82/1.17  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.82/1.17  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 1.82/1.17  tff('#skF_1', type, '#skF_1': $i).
% 1.82/1.17  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 1.82/1.17  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.82/1.17  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.82/1.17  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.82/1.17  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.82/1.17  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 1.82/1.17  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 1.82/1.17  
% 1.92/1.18  tff(f_56, negated_conjecture, ~(![A]: (v1_relat_1(A) => (k8_relat_1(k1_xboole_0, A) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t137_relat_1)).
% 1.92/1.18  tff(f_29, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 1.92/1.18  tff(f_45, axiom, (![A]: (k1_setfam_1(k1_tarski(A)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_setfam_1)).
% 1.92/1.18  tff(f_31, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 1.92/1.18  tff(f_47, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 1.92/1.18  tff(f_27, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 1.92/1.18  tff(f_43, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 1.92/1.19  tff(f_51, axiom, (![A, B, C]: (v1_relat_1(C) => (k8_relat_1(k6_subset_1(A, B), C) = k6_subset_1(k8_relat_1(A, C), k8_relat_1(B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t136_relat_1)).
% 1.92/1.19  tff(c_26, plain, (k8_relat_1(k1_xboole_0, '#skF_1')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.92/1.19  tff(c_28, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.92/1.19  tff(c_4, plain, (![A_3]: (k5_xboole_0(A_3, A_3)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.92/1.19  tff(c_20, plain, (![A_27]: (k1_setfam_1(k1_tarski(A_27))=A_27)), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.92/1.19  tff(c_6, plain, (![A_4]: (k2_tarski(A_4, A_4)=k1_tarski(A_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.92/1.19  tff(c_73, plain, (![A_40, B_41]: (k1_setfam_1(k2_tarski(A_40, B_41))=k3_xboole_0(A_40, B_41))), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.92/1.19  tff(c_82, plain, (![A_4]: (k3_xboole_0(A_4, A_4)=k1_setfam_1(k1_tarski(A_4)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_73])).
% 1.92/1.19  tff(c_85, plain, (![A_4]: (k3_xboole_0(A_4, A_4)=A_4)), inference(demodulation, [status(thm), theory('equality')], [c_20, c_82])).
% 1.92/1.19  tff(c_95, plain, (![A_43, B_44]: (k5_xboole_0(A_43, k3_xboole_0(A_43, B_44))=k4_xboole_0(A_43, B_44))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.92/1.19  tff(c_104, plain, (![A_4]: (k5_xboole_0(A_4, A_4)=k4_xboole_0(A_4, A_4))), inference(superposition, [status(thm), theory('equality')], [c_85, c_95])).
% 1.92/1.19  tff(c_107, plain, (![A_4]: (k4_xboole_0(A_4, A_4)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_4, c_104])).
% 1.92/1.19  tff(c_18, plain, (![A_25, B_26]: (k6_subset_1(A_25, B_26)=k4_xboole_0(A_25, B_26))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.92/1.19  tff(c_24, plain, (![A_30, C_32, B_31]: (k6_subset_1(k8_relat_1(A_30, C_32), k8_relat_1(B_31, C_32))=k8_relat_1(k6_subset_1(A_30, B_31), C_32) | ~v1_relat_1(C_32))), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.92/1.19  tff(c_142, plain, (![A_58, C_59, B_60]: (k4_xboole_0(k8_relat_1(A_58, C_59), k8_relat_1(B_60, C_59))=k8_relat_1(k4_xboole_0(A_58, B_60), C_59) | ~v1_relat_1(C_59))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_18, c_24])).
% 1.92/1.19  tff(c_149, plain, (![B_60, C_59]: (k8_relat_1(k4_xboole_0(B_60, B_60), C_59)=k1_xboole_0 | ~v1_relat_1(C_59))), inference(superposition, [status(thm), theory('equality')], [c_142, c_107])).
% 1.92/1.19  tff(c_170, plain, (![C_67]: (k8_relat_1(k1_xboole_0, C_67)=k1_xboole_0 | ~v1_relat_1(C_67))), inference(demodulation, [status(thm), theory('equality')], [c_107, c_149])).
% 1.92/1.19  tff(c_173, plain, (k8_relat_1(k1_xboole_0, '#skF_1')=k1_xboole_0), inference(resolution, [status(thm)], [c_28, c_170])).
% 1.92/1.19  tff(c_177, plain, $false, inference(negUnitSimplification, [status(thm)], [c_26, c_173])).
% 1.92/1.19  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.92/1.19  
% 1.92/1.19  Inference rules
% 1.92/1.19  ----------------------
% 1.92/1.19  #Ref     : 0
% 1.92/1.19  #Sup     : 33
% 1.92/1.19  #Fact    : 0
% 1.92/1.19  #Define  : 0
% 1.92/1.19  #Split   : 0
% 1.92/1.19  #Chain   : 0
% 1.92/1.19  #Close   : 0
% 1.92/1.19  
% 1.92/1.19  Ordering : KBO
% 1.92/1.19  
% 1.92/1.19  Simplification rules
% 1.92/1.19  ----------------------
% 1.92/1.19  #Subsume      : 0
% 1.92/1.19  #Demod        : 6
% 1.92/1.19  #Tautology    : 28
% 1.92/1.19  #SimpNegUnit  : 1
% 1.92/1.19  #BackRed      : 0
% 1.92/1.19  
% 1.92/1.19  #Partial instantiations: 0
% 1.92/1.19  #Strategies tried      : 1
% 1.92/1.19  
% 1.92/1.19  Timing (in seconds)
% 1.92/1.19  ----------------------
% 1.92/1.19  Preprocessing        : 0.30
% 1.92/1.19  Parsing              : 0.16
% 1.92/1.19  CNF conversion       : 0.02
% 1.92/1.19  Main loop            : 0.12
% 1.92/1.19  Inferencing          : 0.05
% 1.92/1.19  Reduction            : 0.04
% 1.92/1.19  Demodulation         : 0.03
% 1.92/1.19  BG Simplification    : 0.01
% 1.92/1.19  Subsumption          : 0.01
% 1.92/1.19  Abstraction          : 0.01
% 1.92/1.19  MUC search           : 0.00
% 1.92/1.19  Cooper               : 0.00
% 1.92/1.19  Total                : 0.45
% 1.92/1.19  Index Insertion      : 0.00
% 1.92/1.19  Index Deletion       : 0.00
% 1.92/1.19  Index Matching       : 0.00
% 1.92/1.19  BG Taut test         : 0.00
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:23 EST 2020

% Result     : Theorem 3.08s
% Output     : CNFRefutation 3.08s
% Verified   : 
% Statistics : Number of formulae       :   48 (  51 expanded)
%              Number of leaves         :   30 (  33 expanded)
%              Depth                    :    7
%              Number of atoms          :   33 (  42 expanded)
%              Number of equality atoms :   22 (  25 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > v1_funct_1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k6_subset_1 > k5_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff(k6_subset_1,type,(
    k6_subset_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_117,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ! [B,C] :
            ( r1_tarski(k10_relat_1(A,C),B)
           => k10_relat_1(A,C) = k10_relat_1(k7_relat_1(A,B),C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t175_funct_2)).

tff(f_95,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k10_relat_1(k7_relat_1(C,A),B) = k3_xboole_0(A,k10_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t139_funct_1)).

tff(f_49,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_55,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_45,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_35,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(c_52,plain,(
    k10_relat_1(k7_relat_1('#skF_1','#skF_2'),'#skF_3') != k10_relat_1('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_58,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_1451,plain,(
    ! [A_125,C_126,B_127] :
      ( k3_xboole_0(A_125,k10_relat_1(C_126,B_127)) = k10_relat_1(k7_relat_1(C_126,A_125),B_127)
      | ~ v1_relat_1(C_126) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_20,plain,(
    ! [B_14,A_13] : k2_tarski(B_14,A_13) = k2_tarski(A_13,B_14) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_272,plain,(
    ! [A_67,B_68] : k1_setfam_1(k2_tarski(A_67,B_68)) = k3_xboole_0(A_67,B_68) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_287,plain,(
    ! [B_69,A_70] : k1_setfam_1(k2_tarski(B_69,A_70)) = k3_xboole_0(A_70,B_69) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_272])).

tff(c_26,plain,(
    ! [A_19,B_20] : k1_setfam_1(k2_tarski(A_19,B_20)) = k3_xboole_0(A_19,B_20) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_293,plain,(
    ! [B_69,A_70] : k3_xboole_0(B_69,A_70) = k3_xboole_0(A_70,B_69) ),
    inference(superposition,[status(thm),theory(equality)],[c_287,c_26])).

tff(c_16,plain,(
    ! [A_10] : k4_xboole_0(A_10,k1_xboole_0) = A_10 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_54,plain,(
    r1_tarski(k10_relat_1('#skF_1','#skF_3'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_147,plain,(
    ! [A_58,B_59] :
      ( k4_xboole_0(A_58,B_59) = k1_xboole_0
      | ~ r1_tarski(A_58,B_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_157,plain,(
    k4_xboole_0(k10_relat_1('#skF_1','#skF_3'),'#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_54,c_147])).

tff(c_343,plain,(
    ! [A_73,B_74] : k4_xboole_0(A_73,k4_xboole_0(A_73,B_74)) = k3_xboole_0(A_73,B_74) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_371,plain,(
    k4_xboole_0(k10_relat_1('#skF_1','#skF_3'),k1_xboole_0) = k3_xboole_0(k10_relat_1('#skF_1','#skF_3'),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_157,c_343])).

tff(c_388,plain,(
    k3_xboole_0('#skF_2',k10_relat_1('#skF_1','#skF_3')) = k10_relat_1('#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_293,c_16,c_371])).

tff(c_1489,plain,
    ( k10_relat_1(k7_relat_1('#skF_1','#skF_2'),'#skF_3') = k10_relat_1('#skF_1','#skF_3')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_1451,c_388])).

tff(c_1541,plain,(
    k10_relat_1(k7_relat_1('#skF_1','#skF_2'),'#skF_3') = k10_relat_1('#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_1489])).

tff(c_1543,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_1541])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:43:20 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.08/1.62  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.08/1.62  
% 3.08/1.62  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.08/1.62  %$ r1_tarski > v1_relat_1 > v1_funct_1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k6_subset_1 > k5_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 3.08/1.62  
% 3.08/1.62  %Foreground sorts:
% 3.08/1.62  
% 3.08/1.62  
% 3.08/1.62  %Background operators:
% 3.08/1.62  
% 3.08/1.62  
% 3.08/1.62  %Foreground operators:
% 3.08/1.62  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.08/1.62  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.08/1.62  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.08/1.62  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 3.08/1.62  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.08/1.62  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 3.08/1.62  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.08/1.62  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.08/1.62  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.08/1.62  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.08/1.62  tff('#skF_2', type, '#skF_2': $i).
% 3.08/1.62  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 3.08/1.62  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 3.08/1.62  tff('#skF_3', type, '#skF_3': $i).
% 3.08/1.62  tff('#skF_1', type, '#skF_1': $i).
% 3.08/1.62  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.08/1.62  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 3.08/1.62  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.08/1.62  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 3.08/1.62  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.08/1.62  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.08/1.62  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.08/1.62  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 3.08/1.62  
% 3.08/1.63  tff(f_117, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B, C]: (r1_tarski(k10_relat_1(A, C), B) => (k10_relat_1(A, C) = k10_relat_1(k7_relat_1(A, B), C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t175_funct_2)).
% 3.08/1.63  tff(f_95, axiom, (![A, B, C]: (v1_relat_1(C) => (k10_relat_1(k7_relat_1(C, A), B) = k3_xboole_0(A, k10_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t139_funct_1)).
% 3.08/1.63  tff(f_49, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 3.08/1.63  tff(f_55, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 3.08/1.63  tff(f_45, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 3.08/1.63  tff(f_35, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 3.08/1.63  tff(f_47, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 3.08/1.63  tff(c_52, plain, (k10_relat_1(k7_relat_1('#skF_1', '#skF_2'), '#skF_3')!=k10_relat_1('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_117])).
% 3.08/1.63  tff(c_58, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_117])).
% 3.08/1.63  tff(c_1451, plain, (![A_125, C_126, B_127]: (k3_xboole_0(A_125, k10_relat_1(C_126, B_127))=k10_relat_1(k7_relat_1(C_126, A_125), B_127) | ~v1_relat_1(C_126))), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.08/1.63  tff(c_20, plain, (![B_14, A_13]: (k2_tarski(B_14, A_13)=k2_tarski(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.08/1.63  tff(c_272, plain, (![A_67, B_68]: (k1_setfam_1(k2_tarski(A_67, B_68))=k3_xboole_0(A_67, B_68))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.08/1.63  tff(c_287, plain, (![B_69, A_70]: (k1_setfam_1(k2_tarski(B_69, A_70))=k3_xboole_0(A_70, B_69))), inference(superposition, [status(thm), theory('equality')], [c_20, c_272])).
% 3.08/1.63  tff(c_26, plain, (![A_19, B_20]: (k1_setfam_1(k2_tarski(A_19, B_20))=k3_xboole_0(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.08/1.63  tff(c_293, plain, (![B_69, A_70]: (k3_xboole_0(B_69, A_70)=k3_xboole_0(A_70, B_69))), inference(superposition, [status(thm), theory('equality')], [c_287, c_26])).
% 3.08/1.63  tff(c_16, plain, (![A_10]: (k4_xboole_0(A_10, k1_xboole_0)=A_10)), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.08/1.63  tff(c_54, plain, (r1_tarski(k10_relat_1('#skF_1', '#skF_3'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_117])).
% 3.08/1.63  tff(c_147, plain, (![A_58, B_59]: (k4_xboole_0(A_58, B_59)=k1_xboole_0 | ~r1_tarski(A_58, B_59))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.08/1.63  tff(c_157, plain, (k4_xboole_0(k10_relat_1('#skF_1', '#skF_3'), '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_54, c_147])).
% 3.08/1.63  tff(c_343, plain, (![A_73, B_74]: (k4_xboole_0(A_73, k4_xboole_0(A_73, B_74))=k3_xboole_0(A_73, B_74))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.08/1.63  tff(c_371, plain, (k4_xboole_0(k10_relat_1('#skF_1', '#skF_3'), k1_xboole_0)=k3_xboole_0(k10_relat_1('#skF_1', '#skF_3'), '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_157, c_343])).
% 3.08/1.63  tff(c_388, plain, (k3_xboole_0('#skF_2', k10_relat_1('#skF_1', '#skF_3'))=k10_relat_1('#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_293, c_16, c_371])).
% 3.08/1.63  tff(c_1489, plain, (k10_relat_1(k7_relat_1('#skF_1', '#skF_2'), '#skF_3')=k10_relat_1('#skF_1', '#skF_3') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_1451, c_388])).
% 3.08/1.63  tff(c_1541, plain, (k10_relat_1(k7_relat_1('#skF_1', '#skF_2'), '#skF_3')=k10_relat_1('#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_1489])).
% 3.08/1.63  tff(c_1543, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_1541])).
% 3.08/1.63  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.08/1.63  
% 3.08/1.63  Inference rules
% 3.08/1.63  ----------------------
% 3.08/1.63  #Ref     : 1
% 3.08/1.63  #Sup     : 363
% 3.08/1.63  #Fact    : 0
% 3.08/1.63  #Define  : 0
% 3.08/1.63  #Split   : 1
% 3.08/1.63  #Chain   : 0
% 3.08/1.63  #Close   : 0
% 3.08/1.63  
% 3.08/1.63  Ordering : KBO
% 3.08/1.63  
% 3.08/1.63  Simplification rules
% 3.08/1.63  ----------------------
% 3.08/1.63  #Subsume      : 30
% 3.08/1.63  #Demod        : 137
% 3.08/1.63  #Tautology    : 246
% 3.08/1.63  #SimpNegUnit  : 1
% 3.08/1.63  #BackRed      : 0
% 3.08/1.63  
% 3.08/1.63  #Partial instantiations: 0
% 3.08/1.63  #Strategies tried      : 1
% 3.08/1.63  
% 3.08/1.63  Timing (in seconds)
% 3.08/1.63  ----------------------
% 3.08/1.63  Preprocessing        : 0.32
% 3.08/1.63  Parsing              : 0.17
% 3.08/1.63  CNF conversion       : 0.02
% 3.08/1.63  Main loop            : 0.45
% 3.08/1.63  Inferencing          : 0.15
% 3.08/1.64  Reduction            : 0.17
% 3.08/1.64  Demodulation         : 0.13
% 3.08/1.64  BG Simplification    : 0.02
% 3.08/1.64  Subsumption          : 0.07
% 3.08/1.64  Abstraction          : 0.03
% 3.08/1.64  MUC search           : 0.00
% 3.08/1.64  Cooper               : 0.00
% 3.08/1.64  Total                : 0.80
% 3.08/1.64  Index Insertion      : 0.00
% 3.08/1.64  Index Deletion       : 0.00
% 3.08/1.64  Index Matching       : 0.00
% 3.08/1.64  BG Taut test         : 0.00
%------------------------------------------------------------------------------

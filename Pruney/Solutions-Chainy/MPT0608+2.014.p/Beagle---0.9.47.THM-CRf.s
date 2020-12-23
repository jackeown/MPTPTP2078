%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:30 EST 2020

% Result     : Theorem 2.62s
% Output     : CNFRefutation 2.74s
% Verified   : 
% Statistics : Number of formulae       :   37 (  45 expanded)
%              Number of leaves         :   19 (  24 expanded)
%              Depth                    :    7
%              Number of atoms          :   39 (  48 expanded)
%              Number of equality atoms :   22 (  30 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_relat_1 > k7_relat_1 > k6_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > #nlpp > k1_relat_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_50,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => k1_relat_1(k6_subset_1(B,k7_relat_1(B,A))) = k6_subset_1(k1_relat_1(B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t212_relat_1)).

tff(f_45,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k7_relat_1(A,k1_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_relat_1)).

tff(f_33,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k7_relat_1(C,k6_subset_1(A,B)) = k6_subset_1(k7_relat_1(C,A),k7_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t109_relat_1)).

tff(f_29,axiom,(
    ! [A,B] : k4_xboole_0(A,k3_xboole_0(A,B)) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k1_relat_1(k7_relat_1(B,A)) = k3_xboole_0(k1_relat_1(B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_relat_1)).

tff(c_18,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_14,plain,(
    ! [A_14] :
      ( k7_relat_1(A_14,k1_relat_1(A_14)) = A_14
      | ~ v1_relat_1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_8,plain,(
    ! [A_7,B_8] : k6_subset_1(A_7,B_8) = k4_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_10,plain,(
    ! [C_11,A_9,B_10] :
      ( k6_subset_1(k7_relat_1(C_11,A_9),k7_relat_1(C_11,B_10)) = k7_relat_1(C_11,k6_subset_1(A_9,B_10))
      | ~ v1_relat_1(C_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_222,plain,(
    ! [C_36,A_37,B_38] :
      ( k4_xboole_0(k7_relat_1(C_36,A_37),k7_relat_1(C_36,B_38)) = k7_relat_1(C_36,k4_xboole_0(A_37,B_38))
      | ~ v1_relat_1(C_36) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_8,c_10])).

tff(c_455,plain,(
    ! [A_48,B_49] :
      ( k7_relat_1(A_48,k4_xboole_0(k1_relat_1(A_48),B_49)) = k4_xboole_0(A_48,k7_relat_1(A_48,B_49))
      | ~ v1_relat_1(A_48)
      | ~ v1_relat_1(A_48) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_222])).

tff(c_4,plain,(
    ! [A_3,B_4] : k4_xboole_0(A_3,k3_xboole_0(A_3,B_4)) = k4_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_57,plain,(
    ! [A_22,B_23] : k4_xboole_0(A_22,k4_xboole_0(A_22,B_23)) = k3_xboole_0(A_22,B_23) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_6,plain,(
    ! [A_5,B_6] : k4_xboole_0(A_5,k4_xboole_0(A_5,B_6)) = k3_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_60,plain,(
    ! [A_22,B_23] : k4_xboole_0(A_22,k3_xboole_0(A_22,B_23)) = k3_xboole_0(A_22,k4_xboole_0(A_22,B_23)) ),
    inference(superposition,[status(thm),theory(equality)],[c_57,c_6])).

tff(c_73,plain,(
    ! [A_22,B_23] : k3_xboole_0(A_22,k4_xboole_0(A_22,B_23)) = k4_xboole_0(A_22,B_23) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_60])).

tff(c_151,plain,(
    ! [B_30,A_31] :
      ( k3_xboole_0(k1_relat_1(B_30),A_31) = k1_relat_1(k7_relat_1(B_30,A_31))
      | ~ v1_relat_1(B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_182,plain,(
    ! [B_30,B_23] :
      ( k1_relat_1(k7_relat_1(B_30,k4_xboole_0(k1_relat_1(B_30),B_23))) = k4_xboole_0(k1_relat_1(B_30),B_23)
      | ~ v1_relat_1(B_30) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_73,c_151])).

tff(c_588,plain,(
    ! [A_52,B_53] :
      ( k1_relat_1(k4_xboole_0(A_52,k7_relat_1(A_52,B_53))) = k4_xboole_0(k1_relat_1(A_52),B_53)
      | ~ v1_relat_1(A_52)
      | ~ v1_relat_1(A_52)
      | ~ v1_relat_1(A_52) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_455,c_182])).

tff(c_16,plain,(
    k1_relat_1(k6_subset_1('#skF_2',k7_relat_1('#skF_2','#skF_1'))) != k6_subset_1(k1_relat_1('#skF_2'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_19,plain,(
    k1_relat_1(k4_xboole_0('#skF_2',k7_relat_1('#skF_2','#skF_1'))) != k4_xboole_0(k1_relat_1('#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_8,c_16])).

tff(c_624,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_588,c_19])).

tff(c_644,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_624])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 19:48:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.62/1.46  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.62/1.47  
% 2.62/1.47  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.62/1.47  %$ v1_relat_1 > k7_relat_1 > k6_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > #nlpp > k1_relat_1 > #skF_2 > #skF_1
% 2.62/1.47  
% 2.62/1.47  %Foreground sorts:
% 2.62/1.47  
% 2.62/1.47  
% 2.62/1.47  %Background operators:
% 2.62/1.47  
% 2.62/1.47  
% 2.62/1.47  %Foreground operators:
% 2.62/1.47  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.62/1.47  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.62/1.47  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.62/1.47  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.62/1.47  tff('#skF_2', type, '#skF_2': $i).
% 2.62/1.47  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 2.62/1.47  tff('#skF_1', type, '#skF_1': $i).
% 2.62/1.47  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.62/1.47  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.62/1.47  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.62/1.47  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.62/1.47  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.62/1.47  
% 2.74/1.48  tff(f_50, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (k1_relat_1(k6_subset_1(B, k7_relat_1(B, A))) = k6_subset_1(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t212_relat_1)).
% 2.74/1.48  tff(f_45, axiom, (![A]: (v1_relat_1(A) => (k7_relat_1(A, k1_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_relat_1)).
% 2.74/1.48  tff(f_33, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 2.74/1.48  tff(f_37, axiom, (![A, B, C]: (v1_relat_1(C) => (k7_relat_1(C, k6_subset_1(A, B)) = k6_subset_1(k7_relat_1(C, A), k7_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t109_relat_1)).
% 2.74/1.48  tff(f_29, axiom, (![A, B]: (k4_xboole_0(A, k3_xboole_0(A, B)) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_xboole_1)).
% 2.74/1.48  tff(f_31, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 2.74/1.48  tff(f_41, axiom, (![A, B]: (v1_relat_1(B) => (k1_relat_1(k7_relat_1(B, A)) = k3_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t90_relat_1)).
% 2.74/1.48  tff(c_18, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.74/1.48  tff(c_14, plain, (![A_14]: (k7_relat_1(A_14, k1_relat_1(A_14))=A_14 | ~v1_relat_1(A_14))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.74/1.48  tff(c_8, plain, (![A_7, B_8]: (k6_subset_1(A_7, B_8)=k4_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.74/1.48  tff(c_10, plain, (![C_11, A_9, B_10]: (k6_subset_1(k7_relat_1(C_11, A_9), k7_relat_1(C_11, B_10))=k7_relat_1(C_11, k6_subset_1(A_9, B_10)) | ~v1_relat_1(C_11))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.74/1.48  tff(c_222, plain, (![C_36, A_37, B_38]: (k4_xboole_0(k7_relat_1(C_36, A_37), k7_relat_1(C_36, B_38))=k7_relat_1(C_36, k4_xboole_0(A_37, B_38)) | ~v1_relat_1(C_36))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_8, c_10])).
% 2.74/1.48  tff(c_455, plain, (![A_48, B_49]: (k7_relat_1(A_48, k4_xboole_0(k1_relat_1(A_48), B_49))=k4_xboole_0(A_48, k7_relat_1(A_48, B_49)) | ~v1_relat_1(A_48) | ~v1_relat_1(A_48))), inference(superposition, [status(thm), theory('equality')], [c_14, c_222])).
% 2.74/1.48  tff(c_4, plain, (![A_3, B_4]: (k4_xboole_0(A_3, k3_xboole_0(A_3, B_4))=k4_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.74/1.48  tff(c_57, plain, (![A_22, B_23]: (k4_xboole_0(A_22, k4_xboole_0(A_22, B_23))=k3_xboole_0(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.74/1.48  tff(c_6, plain, (![A_5, B_6]: (k4_xboole_0(A_5, k4_xboole_0(A_5, B_6))=k3_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.74/1.48  tff(c_60, plain, (![A_22, B_23]: (k4_xboole_0(A_22, k3_xboole_0(A_22, B_23))=k3_xboole_0(A_22, k4_xboole_0(A_22, B_23)))), inference(superposition, [status(thm), theory('equality')], [c_57, c_6])).
% 2.74/1.48  tff(c_73, plain, (![A_22, B_23]: (k3_xboole_0(A_22, k4_xboole_0(A_22, B_23))=k4_xboole_0(A_22, B_23))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_60])).
% 2.74/1.48  tff(c_151, plain, (![B_30, A_31]: (k3_xboole_0(k1_relat_1(B_30), A_31)=k1_relat_1(k7_relat_1(B_30, A_31)) | ~v1_relat_1(B_30))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.74/1.48  tff(c_182, plain, (![B_30, B_23]: (k1_relat_1(k7_relat_1(B_30, k4_xboole_0(k1_relat_1(B_30), B_23)))=k4_xboole_0(k1_relat_1(B_30), B_23) | ~v1_relat_1(B_30))), inference(superposition, [status(thm), theory('equality')], [c_73, c_151])).
% 2.74/1.48  tff(c_588, plain, (![A_52, B_53]: (k1_relat_1(k4_xboole_0(A_52, k7_relat_1(A_52, B_53)))=k4_xboole_0(k1_relat_1(A_52), B_53) | ~v1_relat_1(A_52) | ~v1_relat_1(A_52) | ~v1_relat_1(A_52))), inference(superposition, [status(thm), theory('equality')], [c_455, c_182])).
% 2.74/1.48  tff(c_16, plain, (k1_relat_1(k6_subset_1('#skF_2', k7_relat_1('#skF_2', '#skF_1')))!=k6_subset_1(k1_relat_1('#skF_2'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.74/1.48  tff(c_19, plain, (k1_relat_1(k4_xboole_0('#skF_2', k7_relat_1('#skF_2', '#skF_1')))!=k4_xboole_0(k1_relat_1('#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_8, c_8, c_16])).
% 2.74/1.48  tff(c_624, plain, (~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_588, c_19])).
% 2.74/1.48  tff(c_644, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_18, c_624])).
% 2.74/1.48  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.74/1.48  
% 2.74/1.48  Inference rules
% 2.74/1.48  ----------------------
% 2.74/1.48  #Ref     : 0
% 2.74/1.48  #Sup     : 168
% 2.74/1.48  #Fact    : 0
% 2.74/1.48  #Define  : 0
% 2.74/1.48  #Split   : 0
% 2.74/1.48  #Chain   : 0
% 2.74/1.48  #Close   : 0
% 2.74/1.48  
% 2.74/1.48  Ordering : KBO
% 2.74/1.48  
% 2.74/1.48  Simplification rules
% 2.74/1.48  ----------------------
% 2.74/1.48  #Subsume      : 20
% 2.74/1.48  #Demod        : 61
% 2.74/1.48  #Tautology    : 58
% 2.74/1.48  #SimpNegUnit  : 0
% 2.74/1.48  #BackRed      : 0
% 2.74/1.48  
% 2.74/1.48  #Partial instantiations: 0
% 2.74/1.48  #Strategies tried      : 1
% 2.74/1.48  
% 2.74/1.48  Timing (in seconds)
% 2.74/1.48  ----------------------
% 2.74/1.48  Preprocessing        : 0.30
% 2.74/1.48  Parsing              : 0.16
% 2.74/1.48  CNF conversion       : 0.02
% 2.74/1.48  Main loop            : 0.34
% 2.74/1.48  Inferencing          : 0.14
% 2.74/1.48  Reduction            : 0.11
% 2.74/1.48  Demodulation         : 0.08
% 2.74/1.48  BG Simplification    : 0.02
% 2.74/1.48  Subsumption          : 0.05
% 2.74/1.48  Abstraction          : 0.03
% 2.74/1.48  MUC search           : 0.00
% 2.74/1.49  Cooper               : 0.00
% 2.74/1.49  Total                : 0.67
% 2.74/1.49  Index Insertion      : 0.00
% 2.74/1.49  Index Deletion       : 0.00
% 2.74/1.49  Index Matching       : 0.00
% 2.74/1.49  BG Taut test         : 0.00
%------------------------------------------------------------------------------

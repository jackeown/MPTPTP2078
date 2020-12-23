%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:30 EST 2020

% Result     : Theorem 2.21s
% Output     : CNFRefutation 2.43s
% Verified   : 
% Statistics : Number of formulae       :   38 (  46 expanded)
%              Number of leaves         :   20 (  25 expanded)
%              Depth                    :    7
%              Number of atoms          :   40 (  49 expanded)
%              Number of equality atoms :   21 (  29 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k7_relat_1 > k6_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > #nlpp > k1_relat_1 > #skF_2 > #skF_1

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(f_54,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => k1_relat_1(k6_subset_1(B,k7_relat_1(B,A))) = k6_subset_1(k1_relat_1(B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t212_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_39,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_tarski(k1_relat_1(C),A)
       => k6_subset_1(C,k7_relat_1(C,B)) = k7_relat_1(C,k6_subset_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t211_relat_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k1_relat_1(k7_relat_1(B,A)) = k3_xboole_0(k1_relat_1(B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_relat_1)).

tff(f_35,axiom,(
    ! [A,B] : k4_xboole_0(A,k3_xboole_0(A,B)) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(c_22,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_14,plain,(
    ! [A_9,B_10] : k6_subset_1(A_9,B_10) = k4_xboole_0(A_9,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_16,plain,(
    ! [C_13,A_11,B_12] :
      ( k7_relat_1(C_13,k6_subset_1(A_11,B_12)) = k6_subset_1(C_13,k7_relat_1(C_13,B_12))
      | ~ r1_tarski(k1_relat_1(C_13),A_11)
      | ~ v1_relat_1(C_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_210,plain,(
    ! [C_37,A_38,B_39] :
      ( k7_relat_1(C_37,k4_xboole_0(A_38,B_39)) = k4_xboole_0(C_37,k7_relat_1(C_37,B_39))
      | ~ r1_tarski(k1_relat_1(C_37),A_38)
      | ~ v1_relat_1(C_37) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_14,c_16])).

tff(c_214,plain,(
    ! [C_37,B_39] :
      ( k7_relat_1(C_37,k4_xboole_0(k1_relat_1(C_37),B_39)) = k4_xboole_0(C_37,k7_relat_1(C_37,B_39))
      | ~ v1_relat_1(C_37) ) ),
    inference(resolution,[status(thm)],[c_6,c_210])).

tff(c_155,plain,(
    ! [B_33,A_34] :
      ( k3_xboole_0(k1_relat_1(B_33),A_34) = k1_relat_1(k7_relat_1(B_33,A_34))
      | ~ v1_relat_1(B_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_10,plain,(
    ! [A_5,B_6] : k4_xboole_0(A_5,k3_xboole_0(A_5,B_6)) = k4_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_61,plain,(
    ! [A_25,B_26] : k4_xboole_0(A_25,k4_xboole_0(A_25,B_26)) = k3_xboole_0(A_25,B_26) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_12,plain,(
    ! [A_7,B_8] : k4_xboole_0(A_7,k4_xboole_0(A_7,B_8)) = k3_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_64,plain,(
    ! [A_25,B_26] : k4_xboole_0(A_25,k3_xboole_0(A_25,B_26)) = k3_xboole_0(A_25,k4_xboole_0(A_25,B_26)) ),
    inference(superposition,[status(thm),theory(equality)],[c_61,c_12])).

tff(c_77,plain,(
    ! [A_25,B_26] : k3_xboole_0(A_25,k4_xboole_0(A_25,B_26)) = k4_xboole_0(A_25,B_26) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_64])).

tff(c_284,plain,(
    ! [B_46,B_47] :
      ( k1_relat_1(k7_relat_1(B_46,k4_xboole_0(k1_relat_1(B_46),B_47))) = k4_xboole_0(k1_relat_1(B_46),B_47)
      | ~ v1_relat_1(B_46) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_155,c_77])).

tff(c_467,plain,(
    ! [C_52,B_53] :
      ( k1_relat_1(k4_xboole_0(C_52,k7_relat_1(C_52,B_53))) = k4_xboole_0(k1_relat_1(C_52),B_53)
      | ~ v1_relat_1(C_52)
      | ~ v1_relat_1(C_52) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_214,c_284])).

tff(c_20,plain,(
    k1_relat_1(k6_subset_1('#skF_2',k7_relat_1('#skF_2','#skF_1'))) != k6_subset_1(k1_relat_1('#skF_2'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_23,plain,(
    k1_relat_1(k4_xboole_0('#skF_2',k7_relat_1('#skF_2','#skF_1'))) != k4_xboole_0(k1_relat_1('#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_14,c_20])).

tff(c_499,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_467,c_23])).

tff(c_513,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_499])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:03:34 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.21/1.35  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.21/1.35  
% 2.21/1.35  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.21/1.35  %$ r1_tarski > v1_relat_1 > k7_relat_1 > k6_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > #nlpp > k1_relat_1 > #skF_2 > #skF_1
% 2.21/1.35  
% 2.21/1.35  %Foreground sorts:
% 2.21/1.35  
% 2.21/1.35  
% 2.21/1.35  %Background operators:
% 2.21/1.35  
% 2.21/1.35  
% 2.21/1.35  %Foreground operators:
% 2.21/1.35  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.21/1.35  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.21/1.35  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.21/1.35  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.21/1.35  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.21/1.35  tff('#skF_2', type, '#skF_2': $i).
% 2.21/1.35  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 2.21/1.35  tff('#skF_1', type, '#skF_1': $i).
% 2.21/1.35  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.21/1.35  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.21/1.35  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.21/1.35  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.21/1.35  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.21/1.35  
% 2.43/1.36  tff(f_54, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (k1_relat_1(k6_subset_1(B, k7_relat_1(B, A))) = k6_subset_1(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t212_relat_1)).
% 2.43/1.36  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.43/1.36  tff(f_39, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 2.43/1.36  tff(f_45, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_tarski(k1_relat_1(C), A) => (k6_subset_1(C, k7_relat_1(C, B)) = k7_relat_1(C, k6_subset_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t211_relat_1)).
% 2.43/1.36  tff(f_49, axiom, (![A, B]: (v1_relat_1(B) => (k1_relat_1(k7_relat_1(B, A)) = k3_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t90_relat_1)).
% 2.43/1.36  tff(f_35, axiom, (![A, B]: (k4_xboole_0(A, k3_xboole_0(A, B)) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_xboole_1)).
% 2.43/1.36  tff(f_37, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 2.43/1.36  tff(c_22, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.43/1.36  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.43/1.36  tff(c_14, plain, (![A_9, B_10]: (k6_subset_1(A_9, B_10)=k4_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.43/1.36  tff(c_16, plain, (![C_13, A_11, B_12]: (k7_relat_1(C_13, k6_subset_1(A_11, B_12))=k6_subset_1(C_13, k7_relat_1(C_13, B_12)) | ~r1_tarski(k1_relat_1(C_13), A_11) | ~v1_relat_1(C_13))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.43/1.36  tff(c_210, plain, (![C_37, A_38, B_39]: (k7_relat_1(C_37, k4_xboole_0(A_38, B_39))=k4_xboole_0(C_37, k7_relat_1(C_37, B_39)) | ~r1_tarski(k1_relat_1(C_37), A_38) | ~v1_relat_1(C_37))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_14, c_16])).
% 2.43/1.36  tff(c_214, plain, (![C_37, B_39]: (k7_relat_1(C_37, k4_xboole_0(k1_relat_1(C_37), B_39))=k4_xboole_0(C_37, k7_relat_1(C_37, B_39)) | ~v1_relat_1(C_37))), inference(resolution, [status(thm)], [c_6, c_210])).
% 2.43/1.36  tff(c_155, plain, (![B_33, A_34]: (k3_xboole_0(k1_relat_1(B_33), A_34)=k1_relat_1(k7_relat_1(B_33, A_34)) | ~v1_relat_1(B_33))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.43/1.36  tff(c_10, plain, (![A_5, B_6]: (k4_xboole_0(A_5, k3_xboole_0(A_5, B_6))=k4_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.43/1.36  tff(c_61, plain, (![A_25, B_26]: (k4_xboole_0(A_25, k4_xboole_0(A_25, B_26))=k3_xboole_0(A_25, B_26))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.43/1.36  tff(c_12, plain, (![A_7, B_8]: (k4_xboole_0(A_7, k4_xboole_0(A_7, B_8))=k3_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.43/1.36  tff(c_64, plain, (![A_25, B_26]: (k4_xboole_0(A_25, k3_xboole_0(A_25, B_26))=k3_xboole_0(A_25, k4_xboole_0(A_25, B_26)))), inference(superposition, [status(thm), theory('equality')], [c_61, c_12])).
% 2.43/1.36  tff(c_77, plain, (![A_25, B_26]: (k3_xboole_0(A_25, k4_xboole_0(A_25, B_26))=k4_xboole_0(A_25, B_26))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_64])).
% 2.43/1.36  tff(c_284, plain, (![B_46, B_47]: (k1_relat_1(k7_relat_1(B_46, k4_xboole_0(k1_relat_1(B_46), B_47)))=k4_xboole_0(k1_relat_1(B_46), B_47) | ~v1_relat_1(B_46))), inference(superposition, [status(thm), theory('equality')], [c_155, c_77])).
% 2.43/1.36  tff(c_467, plain, (![C_52, B_53]: (k1_relat_1(k4_xboole_0(C_52, k7_relat_1(C_52, B_53)))=k4_xboole_0(k1_relat_1(C_52), B_53) | ~v1_relat_1(C_52) | ~v1_relat_1(C_52))), inference(superposition, [status(thm), theory('equality')], [c_214, c_284])).
% 2.43/1.36  tff(c_20, plain, (k1_relat_1(k6_subset_1('#skF_2', k7_relat_1('#skF_2', '#skF_1')))!=k6_subset_1(k1_relat_1('#skF_2'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.43/1.36  tff(c_23, plain, (k1_relat_1(k4_xboole_0('#skF_2', k7_relat_1('#skF_2', '#skF_1')))!=k4_xboole_0(k1_relat_1('#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_14, c_14, c_20])).
% 2.43/1.36  tff(c_499, plain, (~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_467, c_23])).
% 2.43/1.36  tff(c_513, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_22, c_499])).
% 2.43/1.36  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.43/1.36  
% 2.43/1.36  Inference rules
% 2.43/1.36  ----------------------
% 2.43/1.36  #Ref     : 0
% 2.43/1.36  #Sup     : 126
% 2.43/1.36  #Fact    : 0
% 2.43/1.36  #Define  : 0
% 2.43/1.36  #Split   : 0
% 2.43/1.36  #Chain   : 0
% 2.43/1.36  #Close   : 0
% 2.43/1.36  
% 2.43/1.36  Ordering : KBO
% 2.43/1.36  
% 2.43/1.36  Simplification rules
% 2.43/1.36  ----------------------
% 2.43/1.36  #Subsume      : 13
% 2.43/1.36  #Demod        : 60
% 2.43/1.36  #Tautology    : 50
% 2.43/1.36  #SimpNegUnit  : 0
% 2.43/1.36  #BackRed      : 0
% 2.43/1.36  
% 2.43/1.36  #Partial instantiations: 0
% 2.43/1.36  #Strategies tried      : 1
% 2.43/1.36  
% 2.43/1.36  Timing (in seconds)
% 2.43/1.36  ----------------------
% 2.43/1.37  Preprocessing        : 0.30
% 2.43/1.37  Parsing              : 0.16
% 2.43/1.37  CNF conversion       : 0.02
% 2.43/1.37  Main loop            : 0.26
% 2.43/1.37  Inferencing          : 0.10
% 2.43/1.37  Reduction            : 0.09
% 2.43/1.37  Demodulation         : 0.07
% 2.43/1.37  BG Simplification    : 0.02
% 2.43/1.37  Subsumption          : 0.04
% 2.43/1.37  Abstraction          : 0.02
% 2.43/1.37  MUC search           : 0.00
% 2.43/1.37  Cooper               : 0.00
% 2.43/1.37  Total                : 0.58
% 2.43/1.37  Index Insertion      : 0.00
% 2.43/1.37  Index Deletion       : 0.00
% 2.43/1.37  Index Matching       : 0.00
% 2.43/1.37  BG Taut test         : 0.00
%------------------------------------------------------------------------------

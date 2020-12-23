%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:01:02 EST 2020

% Result     : Theorem 1.99s
% Output     : CNFRefutation 2.11s
% Verified   : 
% Statistics : Number of formulae       :   36 (  45 expanded)
%              Number of leaves         :   19 (  24 expanded)
%              Depth                    :    7
%              Number of atoms          :   35 (  48 expanded)
%              Number of equality atoms :    7 (  13 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k9_relat_1 > k6_subset_1 > k4_xboole_0 > k2_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_52,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => r1_tarski(k6_subset_1(k9_relat_1(C,A),k9_relat_1(C,B)),k9_relat_1(C,k6_subset_1(A,B))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t155_relat_1)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k9_relat_1(C,k2_xboole_0(A,B)) = k2_xboole_0(k9_relat_1(C,A),k9_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t153_relat_1)).

tff(f_33,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k4_xboole_0(A,B),C)
     => r1_tarski(A,k2_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_xboole_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k2_xboole_0(B,C))
     => r1_tarski(k4_xboole_0(A,B),C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(c_20,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_216,plain,(
    ! [C_57,A_58,B_59] :
      ( k2_xboole_0(k9_relat_1(C_57,A_58),k9_relat_1(C_57,B_59)) = k9_relat_1(C_57,k2_xboole_0(A_58,B_59))
      | ~ v1_relat_1(C_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_8,plain,(
    ! [A_3,B_4] : k2_xboole_0(A_3,k4_xboole_0(B_4,A_3)) = k2_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_49,plain,(
    ! [A_23,B_24,C_25] :
      ( r1_tarski(A_23,k2_xboole_0(B_24,C_25))
      | ~ r1_tarski(k4_xboole_0(A_23,B_24),C_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_53,plain,(
    ! [A_23,B_24] : r1_tarski(A_23,k2_xboole_0(B_24,k4_xboole_0(A_23,B_24))) ),
    inference(resolution,[status(thm)],[c_6,c_49])).

tff(c_55,plain,(
    ! [A_23,B_24] : r1_tarski(A_23,k2_xboole_0(B_24,A_23)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_53])).

tff(c_263,plain,(
    ! [C_60,B_61,A_62] :
      ( r1_tarski(k9_relat_1(C_60,B_61),k9_relat_1(C_60,k2_xboole_0(A_62,B_61)))
      | ~ v1_relat_1(C_60) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_216,c_55])).

tff(c_132,plain,(
    ! [A_41,B_42,C_43] :
      ( r1_tarski(k4_xboole_0(A_41,B_42),C_43)
      | ~ r1_tarski(A_41,k2_xboole_0(B_42,C_43)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_14,plain,(
    ! [A_11,B_12] : k6_subset_1(A_11,B_12) = k4_xboole_0(A_11,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_18,plain,(
    ~ r1_tarski(k6_subset_1(k9_relat_1('#skF_3','#skF_1'),k9_relat_1('#skF_3','#skF_2')),k9_relat_1('#skF_3',k6_subset_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_21,plain,(
    ~ r1_tarski(k4_xboole_0(k9_relat_1('#skF_3','#skF_1'),k9_relat_1('#skF_3','#skF_2')),k9_relat_1('#skF_3',k4_xboole_0('#skF_1','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_14,c_18])).

tff(c_141,plain,(
    ~ r1_tarski(k9_relat_1('#skF_3','#skF_1'),k2_xboole_0(k9_relat_1('#skF_3','#skF_2'),k9_relat_1('#skF_3',k4_xboole_0('#skF_1','#skF_2')))) ),
    inference(resolution,[status(thm)],[c_132,c_21])).

tff(c_231,plain,
    ( ~ r1_tarski(k9_relat_1('#skF_3','#skF_1'),k9_relat_1('#skF_3',k2_xboole_0('#skF_2',k4_xboole_0('#skF_1','#skF_2'))))
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_216,c_141])).

tff(c_261,plain,(
    ~ r1_tarski(k9_relat_1('#skF_3','#skF_1'),k9_relat_1('#skF_3',k2_xboole_0('#skF_2','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_8,c_231])).

tff(c_266,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_263,c_261])).

tff(c_278,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_266])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:49:41 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.99/1.20  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.99/1.20  
% 1.99/1.20  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.99/1.20  %$ r1_tarski > v1_relat_1 > k9_relat_1 > k6_subset_1 > k4_xboole_0 > k2_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1
% 1.99/1.20  
% 1.99/1.20  %Foreground sorts:
% 1.99/1.20  
% 1.99/1.20  
% 1.99/1.20  %Background operators:
% 1.99/1.20  
% 1.99/1.20  
% 1.99/1.20  %Foreground operators:
% 1.99/1.20  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.99/1.20  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.99/1.20  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.99/1.20  tff('#skF_2', type, '#skF_2': $i).
% 1.99/1.20  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 1.99/1.20  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 1.99/1.20  tff('#skF_3', type, '#skF_3': $i).
% 1.99/1.20  tff('#skF_1', type, '#skF_1': $i).
% 1.99/1.20  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.99/1.20  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.99/1.20  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.99/1.20  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.99/1.20  
% 2.11/1.21  tff(f_52, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => r1_tarski(k6_subset_1(k9_relat_1(C, A), k9_relat_1(C, B)), k9_relat_1(C, k6_subset_1(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t155_relat_1)).
% 2.11/1.21  tff(f_47, axiom, (![A, B, C]: (v1_relat_1(C) => (k9_relat_1(C, k2_xboole_0(A, B)) = k2_xboole_0(k9_relat_1(C, A), k9_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t153_relat_1)).
% 2.11/1.21  tff(f_33, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 2.11/1.21  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.11/1.21  tff(f_41, axiom, (![A, B, C]: (r1_tarski(k4_xboole_0(A, B), C) => r1_tarski(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_xboole_1)).
% 2.11/1.21  tff(f_37, axiom, (![A, B, C]: (r1_tarski(A, k2_xboole_0(B, C)) => r1_tarski(k4_xboole_0(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_xboole_1)).
% 2.11/1.21  tff(f_43, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 2.11/1.21  tff(c_20, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.11/1.21  tff(c_216, plain, (![C_57, A_58, B_59]: (k2_xboole_0(k9_relat_1(C_57, A_58), k9_relat_1(C_57, B_59))=k9_relat_1(C_57, k2_xboole_0(A_58, B_59)) | ~v1_relat_1(C_57))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.11/1.21  tff(c_8, plain, (![A_3, B_4]: (k2_xboole_0(A_3, k4_xboole_0(B_4, A_3))=k2_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.11/1.21  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.11/1.21  tff(c_49, plain, (![A_23, B_24, C_25]: (r1_tarski(A_23, k2_xboole_0(B_24, C_25)) | ~r1_tarski(k4_xboole_0(A_23, B_24), C_25))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.11/1.21  tff(c_53, plain, (![A_23, B_24]: (r1_tarski(A_23, k2_xboole_0(B_24, k4_xboole_0(A_23, B_24))))), inference(resolution, [status(thm)], [c_6, c_49])).
% 2.11/1.21  tff(c_55, plain, (![A_23, B_24]: (r1_tarski(A_23, k2_xboole_0(B_24, A_23)))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_53])).
% 2.11/1.21  tff(c_263, plain, (![C_60, B_61, A_62]: (r1_tarski(k9_relat_1(C_60, B_61), k9_relat_1(C_60, k2_xboole_0(A_62, B_61))) | ~v1_relat_1(C_60))), inference(superposition, [status(thm), theory('equality')], [c_216, c_55])).
% 2.11/1.21  tff(c_132, plain, (![A_41, B_42, C_43]: (r1_tarski(k4_xboole_0(A_41, B_42), C_43) | ~r1_tarski(A_41, k2_xboole_0(B_42, C_43)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.11/1.21  tff(c_14, plain, (![A_11, B_12]: (k6_subset_1(A_11, B_12)=k4_xboole_0(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.11/1.21  tff(c_18, plain, (~r1_tarski(k6_subset_1(k9_relat_1('#skF_3', '#skF_1'), k9_relat_1('#skF_3', '#skF_2')), k9_relat_1('#skF_3', k6_subset_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.11/1.21  tff(c_21, plain, (~r1_tarski(k4_xboole_0(k9_relat_1('#skF_3', '#skF_1'), k9_relat_1('#skF_3', '#skF_2')), k9_relat_1('#skF_3', k4_xboole_0('#skF_1', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_14, c_18])).
% 2.11/1.21  tff(c_141, plain, (~r1_tarski(k9_relat_1('#skF_3', '#skF_1'), k2_xboole_0(k9_relat_1('#skF_3', '#skF_2'), k9_relat_1('#skF_3', k4_xboole_0('#skF_1', '#skF_2'))))), inference(resolution, [status(thm)], [c_132, c_21])).
% 2.11/1.21  tff(c_231, plain, (~r1_tarski(k9_relat_1('#skF_3', '#skF_1'), k9_relat_1('#skF_3', k2_xboole_0('#skF_2', k4_xboole_0('#skF_1', '#skF_2')))) | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_216, c_141])).
% 2.11/1.21  tff(c_261, plain, (~r1_tarski(k9_relat_1('#skF_3', '#skF_1'), k9_relat_1('#skF_3', k2_xboole_0('#skF_2', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_8, c_231])).
% 2.11/1.21  tff(c_266, plain, (~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_263, c_261])).
% 2.11/1.21  tff(c_278, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_20, c_266])).
% 2.11/1.21  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.11/1.21  
% 2.11/1.21  Inference rules
% 2.11/1.21  ----------------------
% 2.11/1.21  #Ref     : 0
% 2.11/1.21  #Sup     : 64
% 2.11/1.21  #Fact    : 0
% 2.11/1.21  #Define  : 0
% 2.11/1.21  #Split   : 0
% 2.11/1.21  #Chain   : 0
% 2.11/1.21  #Close   : 0
% 2.11/1.21  
% 2.11/1.21  Ordering : KBO
% 2.11/1.21  
% 2.11/1.21  Simplification rules
% 2.11/1.21  ----------------------
% 2.11/1.21  #Subsume      : 0
% 2.11/1.21  #Demod        : 14
% 2.11/1.21  #Tautology    : 14
% 2.11/1.21  #SimpNegUnit  : 0
% 2.11/1.21  #BackRed      : 0
% 2.11/1.21  
% 2.11/1.21  #Partial instantiations: 0
% 2.11/1.21  #Strategies tried      : 1
% 2.11/1.21  
% 2.11/1.21  Timing (in seconds)
% 2.11/1.21  ----------------------
% 2.11/1.22  Preprocessing        : 0.25
% 2.11/1.22  Parsing              : 0.14
% 2.11/1.22  CNF conversion       : 0.02
% 2.11/1.22  Main loop            : 0.20
% 2.11/1.22  Inferencing          : 0.07
% 2.11/1.22  Reduction            : 0.06
% 2.11/1.22  Demodulation         : 0.05
% 2.11/1.22  BG Simplification    : 0.01
% 2.11/1.22  Subsumption          : 0.04
% 2.11/1.22  Abstraction          : 0.01
% 2.11/1.22  MUC search           : 0.00
% 2.11/1.22  Cooper               : 0.00
% 2.11/1.22  Total                : 0.47
% 2.11/1.22  Index Insertion      : 0.00
% 2.11/1.22  Index Deletion       : 0.00
% 2.11/1.22  Index Matching       : 0.00
% 2.11/1.22  BG Taut test         : 0.00
%------------------------------------------------------------------------------

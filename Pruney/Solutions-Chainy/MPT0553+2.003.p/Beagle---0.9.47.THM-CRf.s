%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:01:02 EST 2020

% Result     : Theorem 1.96s
% Output     : CNFRefutation 1.96s
% Verified   : 
% Statistics : Number of formulae       :   34 (  41 expanded)
%              Number of leaves         :   19 (  23 expanded)
%              Depth                    :    7
%              Number of atoms          :   35 (  46 expanded)
%              Number of equality atoms :    7 (  11 expanded)
%              Maximal formula depth    :    8 (   4 average)
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t155_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k9_relat_1(C,k2_xboole_0(A,B)) = k2_xboole_0(k9_relat_1(C,A),k9_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t153_relat_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(A,k2_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k2_xboole_0(B,C))
     => r1_tarski(k4_xboole_0(A,B),C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(c_20,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_116,plain,(
    ! [C_41,A_42,B_43] :
      ( k2_xboole_0(k9_relat_1(C_41,A_42),k9_relat_1(C_41,B_43)) = k9_relat_1(C_41,k2_xboole_0(A_42,B_43))
      | ~ v1_relat_1(C_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_8,plain,(
    ! [A_3,C_5,B_4] :
      ( r1_tarski(A_3,k2_xboole_0(C_5,B_4))
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_174,plain,(
    ! [A_51,C_52,A_53,B_54] :
      ( r1_tarski(A_51,k9_relat_1(C_52,k2_xboole_0(A_53,B_54)))
      | ~ r1_tarski(A_51,k9_relat_1(C_52,B_54))
      | ~ v1_relat_1(C_52) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_116,c_8])).

tff(c_10,plain,(
    ! [A_6,B_7] : k2_xboole_0(A_6,k4_xboole_0(B_7,A_6)) = k2_xboole_0(A_6,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_12,plain,(
    ! [A_8,B_9,C_10] :
      ( r1_tarski(k4_xboole_0(A_8,B_9),C_10)
      | ~ r1_tarski(A_8,k2_xboole_0(B_9,C_10)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_14,plain,(
    ! [A_11,B_12] : k6_subset_1(A_11,B_12) = k4_xboole_0(A_11,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_18,plain,(
    ~ r1_tarski(k6_subset_1(k9_relat_1('#skF_3','#skF_1'),k9_relat_1('#skF_3','#skF_2')),k9_relat_1('#skF_3',k6_subset_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_21,plain,(
    ~ r1_tarski(k4_xboole_0(k9_relat_1('#skF_3','#skF_1'),k9_relat_1('#skF_3','#skF_2')),k9_relat_1('#skF_3',k4_xboole_0('#skF_1','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_14,c_18])).

tff(c_81,plain,(
    ~ r1_tarski(k9_relat_1('#skF_3','#skF_1'),k2_xboole_0(k9_relat_1('#skF_3','#skF_2'),k9_relat_1('#skF_3',k4_xboole_0('#skF_1','#skF_2')))) ),
    inference(resolution,[status(thm)],[c_12,c_21])).

tff(c_122,plain,
    ( ~ r1_tarski(k9_relat_1('#skF_3','#skF_1'),k9_relat_1('#skF_3',k2_xboole_0('#skF_2',k4_xboole_0('#skF_1','#skF_2'))))
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_116,c_81])).

tff(c_143,plain,(
    ~ r1_tarski(k9_relat_1('#skF_3','#skF_1'),k9_relat_1('#skF_3',k2_xboole_0('#skF_2','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_10,c_122])).

tff(c_177,plain,
    ( ~ r1_tarski(k9_relat_1('#skF_3','#skF_1'),k9_relat_1('#skF_3','#skF_1'))
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_174,c_143])).

tff(c_193,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_6,c_177])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n011.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 09:38:57 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.96/1.20  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.96/1.21  
% 1.96/1.21  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.96/1.21  %$ r1_tarski > v1_relat_1 > k9_relat_1 > k6_subset_1 > k4_xboole_0 > k2_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1
% 1.96/1.21  
% 1.96/1.21  %Foreground sorts:
% 1.96/1.21  
% 1.96/1.21  
% 1.96/1.21  %Background operators:
% 1.96/1.21  
% 1.96/1.21  
% 1.96/1.21  %Foreground operators:
% 1.96/1.21  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.96/1.21  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.96/1.21  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.96/1.21  tff('#skF_2', type, '#skF_2': $i).
% 1.96/1.21  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 1.96/1.21  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 1.96/1.21  tff('#skF_3', type, '#skF_3': $i).
% 1.96/1.21  tff('#skF_1', type, '#skF_1': $i).
% 1.96/1.21  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.96/1.21  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.96/1.21  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.96/1.21  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.96/1.21  
% 1.96/1.22  tff(f_52, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => r1_tarski(k6_subset_1(k9_relat_1(C, A), k9_relat_1(C, B)), k9_relat_1(C, k6_subset_1(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t155_relat_1)).
% 1.96/1.22  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 1.96/1.22  tff(f_47, axiom, (![A, B, C]: (v1_relat_1(C) => (k9_relat_1(C, k2_xboole_0(A, B)) = k2_xboole_0(k9_relat_1(C, A), k9_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t153_relat_1)).
% 1.96/1.22  tff(f_35, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(A, k2_xboole_0(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_xboole_1)).
% 1.96/1.22  tff(f_37, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 1.96/1.22  tff(f_41, axiom, (![A, B, C]: (r1_tarski(A, k2_xboole_0(B, C)) => r1_tarski(k4_xboole_0(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_xboole_1)).
% 1.96/1.22  tff(f_43, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 1.96/1.22  tff(c_20, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.96/1.22  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.96/1.22  tff(c_116, plain, (![C_41, A_42, B_43]: (k2_xboole_0(k9_relat_1(C_41, A_42), k9_relat_1(C_41, B_43))=k9_relat_1(C_41, k2_xboole_0(A_42, B_43)) | ~v1_relat_1(C_41))), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.96/1.22  tff(c_8, plain, (![A_3, C_5, B_4]: (r1_tarski(A_3, k2_xboole_0(C_5, B_4)) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.96/1.22  tff(c_174, plain, (![A_51, C_52, A_53, B_54]: (r1_tarski(A_51, k9_relat_1(C_52, k2_xboole_0(A_53, B_54))) | ~r1_tarski(A_51, k9_relat_1(C_52, B_54)) | ~v1_relat_1(C_52))), inference(superposition, [status(thm), theory('equality')], [c_116, c_8])).
% 1.96/1.22  tff(c_10, plain, (![A_6, B_7]: (k2_xboole_0(A_6, k4_xboole_0(B_7, A_6))=k2_xboole_0(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.96/1.22  tff(c_12, plain, (![A_8, B_9, C_10]: (r1_tarski(k4_xboole_0(A_8, B_9), C_10) | ~r1_tarski(A_8, k2_xboole_0(B_9, C_10)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.96/1.22  tff(c_14, plain, (![A_11, B_12]: (k6_subset_1(A_11, B_12)=k4_xboole_0(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.96/1.22  tff(c_18, plain, (~r1_tarski(k6_subset_1(k9_relat_1('#skF_3', '#skF_1'), k9_relat_1('#skF_3', '#skF_2')), k9_relat_1('#skF_3', k6_subset_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.96/1.22  tff(c_21, plain, (~r1_tarski(k4_xboole_0(k9_relat_1('#skF_3', '#skF_1'), k9_relat_1('#skF_3', '#skF_2')), k9_relat_1('#skF_3', k4_xboole_0('#skF_1', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_14, c_18])).
% 1.96/1.22  tff(c_81, plain, (~r1_tarski(k9_relat_1('#skF_3', '#skF_1'), k2_xboole_0(k9_relat_1('#skF_3', '#skF_2'), k9_relat_1('#skF_3', k4_xboole_0('#skF_1', '#skF_2'))))), inference(resolution, [status(thm)], [c_12, c_21])).
% 1.96/1.22  tff(c_122, plain, (~r1_tarski(k9_relat_1('#skF_3', '#skF_1'), k9_relat_1('#skF_3', k2_xboole_0('#skF_2', k4_xboole_0('#skF_1', '#skF_2')))) | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_116, c_81])).
% 1.96/1.22  tff(c_143, plain, (~r1_tarski(k9_relat_1('#skF_3', '#skF_1'), k9_relat_1('#skF_3', k2_xboole_0('#skF_2', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_10, c_122])).
% 1.96/1.22  tff(c_177, plain, (~r1_tarski(k9_relat_1('#skF_3', '#skF_1'), k9_relat_1('#skF_3', '#skF_1')) | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_174, c_143])).
% 1.96/1.22  tff(c_193, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_20, c_6, c_177])).
% 1.96/1.22  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.96/1.22  
% 1.96/1.22  Inference rules
% 1.96/1.22  ----------------------
% 1.96/1.22  #Ref     : 0
% 1.96/1.22  #Sup     : 41
% 1.96/1.22  #Fact    : 0
% 1.96/1.22  #Define  : 0
% 1.96/1.22  #Split   : 0
% 1.96/1.22  #Chain   : 0
% 1.96/1.22  #Close   : 0
% 1.96/1.22  
% 1.96/1.22  Ordering : KBO
% 1.96/1.22  
% 1.96/1.22  Simplification rules
% 1.96/1.22  ----------------------
% 1.96/1.22  #Subsume      : 0
% 1.96/1.22  #Demod        : 11
% 1.96/1.22  #Tautology    : 10
% 1.96/1.22  #SimpNegUnit  : 0
% 1.96/1.22  #BackRed      : 0
% 1.96/1.22  
% 1.96/1.22  #Partial instantiations: 0
% 1.96/1.22  #Strategies tried      : 1
% 1.96/1.22  
% 1.96/1.22  Timing (in seconds)
% 1.96/1.22  ----------------------
% 1.96/1.22  Preprocessing        : 0.29
% 1.96/1.22  Parsing              : 0.16
% 1.96/1.22  CNF conversion       : 0.02
% 1.96/1.22  Main loop            : 0.17
% 1.96/1.22  Inferencing          : 0.06
% 1.96/1.22  Reduction            : 0.05
% 1.96/1.22  Demodulation         : 0.04
% 1.96/1.22  BG Simplification    : 0.01
% 1.96/1.22  Subsumption          : 0.04
% 1.96/1.22  Abstraction          : 0.01
% 1.96/1.22  MUC search           : 0.00
% 1.96/1.22  Cooper               : 0.00
% 1.96/1.22  Total                : 0.48
% 1.96/1.22  Index Insertion      : 0.00
% 1.96/1.22  Index Deletion       : 0.00
% 1.96/1.22  Index Matching       : 0.00
% 1.96/1.22  BG Taut test         : 0.00
%------------------------------------------------------------------------------

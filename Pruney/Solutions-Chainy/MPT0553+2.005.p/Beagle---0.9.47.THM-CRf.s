%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:01:02 EST 2020

% Result     : Theorem 1.87s
% Output     : CNFRefutation 1.96s
% Verified   : 
% Statistics : Number of formulae       :   39 (  46 expanded)
%              Number of leaves         :   21 (  26 expanded)
%              Depth                    :    7
%              Number of atoms          :   41 (  53 expanded)
%              Number of equality atoms :    7 (  10 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > k9_relat_1 > k6_subset_1 > k4_xboole_0 > k2_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

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

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_53,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => r1_tarski(k6_subset_1(k9_relat_1(C,A),k9_relat_1(C,B)),k9_relat_1(C,k6_subset_1(A,B))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t155_relat_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_48,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k9_relat_1(C,k2_xboole_0(A,B)) = k2_xboole_0(k9_relat_1(C,A),k9_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t153_relat_1)).

tff(f_36,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(A,k2_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_xboole_1)).

tff(f_38,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_42,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k2_xboole_0(B,C))
     => r1_tarski(k4_xboole_0(A,B),C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_xboole_1)).

tff(f_44,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(c_20,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_32,plain,(
    ! [A_23,B_24] :
      ( ~ r2_hidden('#skF_1'(A_23,B_24),B_24)
      | r1_tarski(A_23,B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_37,plain,(
    ! [A_1] : r1_tarski(A_1,A_1) ),
    inference(resolution,[status(thm)],[c_6,c_32])).

tff(c_93,plain,(
    ! [C_49,A_50,B_51] :
      ( k2_xboole_0(k9_relat_1(C_49,A_50),k9_relat_1(C_49,B_51)) = k9_relat_1(C_49,k2_xboole_0(A_50,B_51))
      | ~ v1_relat_1(C_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_8,plain,(
    ! [A_6,C_8,B_7] :
      ( r1_tarski(A_6,k2_xboole_0(C_8,B_7))
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_130,plain,(
    ! [A_54,C_55,A_56,B_57] :
      ( r1_tarski(A_54,k9_relat_1(C_55,k2_xboole_0(A_56,B_57)))
      | ~ r1_tarski(A_54,k9_relat_1(C_55,B_57))
      | ~ v1_relat_1(C_55) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_93,c_8])).

tff(c_10,plain,(
    ! [A_9,B_10] : k2_xboole_0(A_9,k4_xboole_0(B_10,A_9)) = k2_xboole_0(A_9,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_16,plain,(
    ! [C_18,A_16,B_17] :
      ( k2_xboole_0(k9_relat_1(C_18,A_16),k9_relat_1(C_18,B_17)) = k9_relat_1(C_18,k2_xboole_0(A_16,B_17))
      | ~ v1_relat_1(C_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_12,plain,(
    ! [A_11,B_12,C_13] :
      ( r1_tarski(k4_xboole_0(A_11,B_12),C_13)
      | ~ r1_tarski(A_11,k2_xboole_0(B_12,C_13)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_14,plain,(
    ! [A_14,B_15] : k6_subset_1(A_14,B_15) = k4_xboole_0(A_14,B_15) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_18,plain,(
    ~ r1_tarski(k6_subset_1(k9_relat_1('#skF_4','#skF_2'),k9_relat_1('#skF_4','#skF_3')),k9_relat_1('#skF_4',k6_subset_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_21,plain,(
    ~ r1_tarski(k4_xboole_0(k9_relat_1('#skF_4','#skF_2'),k9_relat_1('#skF_4','#skF_3')),k9_relat_1('#skF_4',k4_xboole_0('#skF_2','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_14,c_18])).

tff(c_60,plain,(
    ~ r1_tarski(k9_relat_1('#skF_4','#skF_2'),k2_xboole_0(k9_relat_1('#skF_4','#skF_3'),k9_relat_1('#skF_4',k4_xboole_0('#skF_2','#skF_3')))) ),
    inference(resolution,[status(thm)],[c_12,c_21])).

tff(c_116,plain,
    ( ~ r1_tarski(k9_relat_1('#skF_4','#skF_2'),k9_relat_1('#skF_4',k2_xboole_0('#skF_3',k4_xboole_0('#skF_2','#skF_3'))))
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_60])).

tff(c_121,plain,(
    ~ r1_tarski(k9_relat_1('#skF_4','#skF_2'),k9_relat_1('#skF_4',k2_xboole_0('#skF_3','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_10,c_116])).

tff(c_133,plain,
    ( ~ r1_tarski(k9_relat_1('#skF_4','#skF_2'),k9_relat_1('#skF_4','#skF_2'))
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_130,c_121])).

tff(c_143,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_37,c_133])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.20/0.34  % CPULimit   : 60
% 0.20/0.34  % DateTime   : Tue Dec  1 19:21:37 EST 2020
% 0.20/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.87/1.21  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.87/1.21  
% 1.87/1.21  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.87/1.22  %$ r2_hidden > r1_tarski > v1_relat_1 > k9_relat_1 > k6_subset_1 > k4_xboole_0 > k2_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 1.87/1.22  
% 1.87/1.22  %Foreground sorts:
% 1.87/1.22  
% 1.87/1.22  
% 1.87/1.22  %Background operators:
% 1.87/1.22  
% 1.87/1.22  
% 1.87/1.22  %Foreground operators:
% 1.87/1.22  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.87/1.22  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.87/1.22  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.87/1.22  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.87/1.22  tff('#skF_2', type, '#skF_2': $i).
% 1.87/1.22  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 1.87/1.22  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 1.87/1.22  tff('#skF_3', type, '#skF_3': $i).
% 1.87/1.22  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.87/1.22  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.87/1.22  tff('#skF_4', type, '#skF_4': $i).
% 1.87/1.22  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.87/1.22  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.87/1.22  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.87/1.22  
% 1.94/1.23  tff(f_53, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => r1_tarski(k6_subset_1(k9_relat_1(C, A), k9_relat_1(C, B)), k9_relat_1(C, k6_subset_1(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t155_relat_1)).
% 1.94/1.23  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 1.94/1.23  tff(f_48, axiom, (![A, B, C]: (v1_relat_1(C) => (k9_relat_1(C, k2_xboole_0(A, B)) = k2_xboole_0(k9_relat_1(C, A), k9_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t153_relat_1)).
% 1.94/1.23  tff(f_36, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(A, k2_xboole_0(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_xboole_1)).
% 1.94/1.23  tff(f_38, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 1.94/1.23  tff(f_42, axiom, (![A, B, C]: (r1_tarski(A, k2_xboole_0(B, C)) => r1_tarski(k4_xboole_0(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_xboole_1)).
% 1.94/1.23  tff(f_44, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 1.94/1.23  tff(c_20, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.94/1.23  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.94/1.23  tff(c_32, plain, (![A_23, B_24]: (~r2_hidden('#skF_1'(A_23, B_24), B_24) | r1_tarski(A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.94/1.23  tff(c_37, plain, (![A_1]: (r1_tarski(A_1, A_1))), inference(resolution, [status(thm)], [c_6, c_32])).
% 1.94/1.23  tff(c_93, plain, (![C_49, A_50, B_51]: (k2_xboole_0(k9_relat_1(C_49, A_50), k9_relat_1(C_49, B_51))=k9_relat_1(C_49, k2_xboole_0(A_50, B_51)) | ~v1_relat_1(C_49))), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.94/1.23  tff(c_8, plain, (![A_6, C_8, B_7]: (r1_tarski(A_6, k2_xboole_0(C_8, B_7)) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.96/1.23  tff(c_130, plain, (![A_54, C_55, A_56, B_57]: (r1_tarski(A_54, k9_relat_1(C_55, k2_xboole_0(A_56, B_57))) | ~r1_tarski(A_54, k9_relat_1(C_55, B_57)) | ~v1_relat_1(C_55))), inference(superposition, [status(thm), theory('equality')], [c_93, c_8])).
% 1.96/1.23  tff(c_10, plain, (![A_9, B_10]: (k2_xboole_0(A_9, k4_xboole_0(B_10, A_9))=k2_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.96/1.23  tff(c_16, plain, (![C_18, A_16, B_17]: (k2_xboole_0(k9_relat_1(C_18, A_16), k9_relat_1(C_18, B_17))=k9_relat_1(C_18, k2_xboole_0(A_16, B_17)) | ~v1_relat_1(C_18))), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.96/1.23  tff(c_12, plain, (![A_11, B_12, C_13]: (r1_tarski(k4_xboole_0(A_11, B_12), C_13) | ~r1_tarski(A_11, k2_xboole_0(B_12, C_13)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.96/1.23  tff(c_14, plain, (![A_14, B_15]: (k6_subset_1(A_14, B_15)=k4_xboole_0(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.96/1.23  tff(c_18, plain, (~r1_tarski(k6_subset_1(k9_relat_1('#skF_4', '#skF_2'), k9_relat_1('#skF_4', '#skF_3')), k9_relat_1('#skF_4', k6_subset_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.96/1.23  tff(c_21, plain, (~r1_tarski(k4_xboole_0(k9_relat_1('#skF_4', '#skF_2'), k9_relat_1('#skF_4', '#skF_3')), k9_relat_1('#skF_4', k4_xboole_0('#skF_2', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_14, c_18])).
% 1.96/1.23  tff(c_60, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_2'), k2_xboole_0(k9_relat_1('#skF_4', '#skF_3'), k9_relat_1('#skF_4', k4_xboole_0('#skF_2', '#skF_3'))))), inference(resolution, [status(thm)], [c_12, c_21])).
% 1.96/1.23  tff(c_116, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_2'), k9_relat_1('#skF_4', k2_xboole_0('#skF_3', k4_xboole_0('#skF_2', '#skF_3')))) | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_16, c_60])).
% 1.96/1.23  tff(c_121, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_2'), k9_relat_1('#skF_4', k2_xboole_0('#skF_3', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_10, c_116])).
% 1.96/1.23  tff(c_133, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_2'), k9_relat_1('#skF_4', '#skF_2')) | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_130, c_121])).
% 1.96/1.23  tff(c_143, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_20, c_37, c_133])).
% 1.96/1.23  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.96/1.23  
% 1.96/1.23  Inference rules
% 1.96/1.23  ----------------------
% 1.96/1.23  #Ref     : 0
% 1.96/1.23  #Sup     : 28
% 1.96/1.23  #Fact    : 0
% 1.96/1.23  #Define  : 0
% 1.96/1.23  #Split   : 0
% 1.96/1.23  #Chain   : 0
% 1.96/1.23  #Close   : 0
% 1.96/1.23  
% 1.96/1.23  Ordering : KBO
% 1.96/1.23  
% 1.96/1.23  Simplification rules
% 1.96/1.23  ----------------------
% 1.96/1.23  #Subsume      : 0
% 1.96/1.23  #Demod        : 6
% 1.96/1.23  #Tautology    : 7
% 1.96/1.23  #SimpNegUnit  : 0
% 1.96/1.23  #BackRed      : 0
% 1.96/1.23  
% 1.96/1.23  #Partial instantiations: 0
% 1.96/1.23  #Strategies tried      : 1
% 1.96/1.23  
% 1.96/1.23  Timing (in seconds)
% 1.96/1.23  ----------------------
% 1.96/1.23  Preprocessing        : 0.28
% 1.96/1.23  Parsing              : 0.15
% 1.96/1.23  CNF conversion       : 0.02
% 1.96/1.23  Main loop            : 0.19
% 1.96/1.23  Inferencing          : 0.09
% 1.96/1.23  Reduction            : 0.05
% 1.96/1.23  Demodulation         : 0.04
% 1.96/1.23  BG Simplification    : 0.01
% 1.96/1.23  Subsumption          : 0.03
% 1.96/1.23  Abstraction          : 0.01
% 1.96/1.23  MUC search           : 0.00
% 1.96/1.23  Cooper               : 0.00
% 1.96/1.23  Total                : 0.50
% 1.96/1.23  Index Insertion      : 0.00
% 1.96/1.23  Index Deletion       : 0.00
% 1.96/1.23  Index Matching       : 0.00
% 1.96/1.23  BG Taut test         : 0.00
%------------------------------------------------------------------------------

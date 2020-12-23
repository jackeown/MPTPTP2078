%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:01:50 EST 2020

% Result     : Theorem 1.86s
% Output     : CNFRefutation 1.86s
% Verified   : 
% Statistics : Number of formulae       :   41 (  49 expanded)
%              Number of leaves         :   22 (  27 expanded)
%              Depth                    :    7
%              Number of atoms          :   34 (  46 expanded)
%              Number of equality atoms :   13 (  18 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k6_subset_1 > k4_xboole_0 > k2_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k3_tarski > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

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

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_48,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => r1_tarski(k6_subset_1(k10_relat_1(C,A),k10_relat_1(C,B)),k10_relat_1(C,k6_subset_1(A,B))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t177_relat_1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k10_relat_1(C,k2_xboole_0(A,B)) = k2_xboole_0(k10_relat_1(C,A),k10_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t175_relat_1)).

tff(f_33,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_37,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k2_xboole_0(B,C))
     => r1_tarski(k4_xboole_0(A,B),C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(c_18,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_251,plain,(
    ! [C_50,A_51,B_52] :
      ( k2_xboole_0(k10_relat_1(C_50,A_51),k10_relat_1(C_50,B_52)) = k10_relat_1(C_50,k2_xboole_0(A_51,B_52))
      | ~ v1_relat_1(C_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_6,plain,(
    ! [A_6,B_7] : r1_tarski(A_6,k2_xboole_0(A_6,B_7)) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_304,plain,(
    ! [C_53,A_54,B_55] :
      ( r1_tarski(k10_relat_1(C_53,A_54),k10_relat_1(C_53,k2_xboole_0(A_54,B_55)))
      | ~ v1_relat_1(C_53) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_251,c_6])).

tff(c_8,plain,(
    ! [B_9,A_8] : k2_tarski(B_9,A_8) = k2_tarski(A_8,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_63,plain,(
    ! [A_23,B_24] : k3_tarski(k2_tarski(A_23,B_24)) = k2_xboole_0(A_23,B_24) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_91,plain,(
    ! [B_27,A_28] : k3_tarski(k2_tarski(B_27,A_28)) = k2_xboole_0(A_28,B_27) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_63])).

tff(c_10,plain,(
    ! [A_10,B_11] : k3_tarski(k2_tarski(A_10,B_11)) = k2_xboole_0(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_97,plain,(
    ! [B_27,A_28] : k2_xboole_0(B_27,A_28) = k2_xboole_0(A_28,B_27) ),
    inference(superposition,[status(thm),theory(equality)],[c_91,c_10])).

tff(c_2,plain,(
    ! [A_1,B_2] : k2_xboole_0(A_1,k4_xboole_0(B_2,A_1)) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_189,plain,(
    ! [A_37,B_38,C_39] :
      ( r1_tarski(k4_xboole_0(A_37,B_38),C_39)
      | ~ r1_tarski(A_37,k2_xboole_0(B_38,C_39)) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_12,plain,(
    ! [A_12,B_13] : k6_subset_1(A_12,B_13) = k4_xboole_0(A_12,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_16,plain,(
    ~ r1_tarski(k6_subset_1(k10_relat_1('#skF_3','#skF_1'),k10_relat_1('#skF_3','#skF_2')),k10_relat_1('#skF_3',k6_subset_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_19,plain,(
    ~ r1_tarski(k4_xboole_0(k10_relat_1('#skF_3','#skF_1'),k10_relat_1('#skF_3','#skF_2')),k10_relat_1('#skF_3',k4_xboole_0('#skF_1','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_12,c_16])).

tff(c_193,plain,(
    ~ r1_tarski(k10_relat_1('#skF_3','#skF_1'),k2_xboole_0(k10_relat_1('#skF_3','#skF_2'),k10_relat_1('#skF_3',k4_xboole_0('#skF_1','#skF_2')))) ),
    inference(resolution,[status(thm)],[c_189,c_19])).

tff(c_266,plain,
    ( ~ r1_tarski(k10_relat_1('#skF_3','#skF_1'),k10_relat_1('#skF_3',k2_xboole_0('#skF_2',k4_xboole_0('#skF_1','#skF_2'))))
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_251,c_193])).

tff(c_302,plain,(
    ~ r1_tarski(k10_relat_1('#skF_3','#skF_1'),k10_relat_1('#skF_3',k2_xboole_0('#skF_1','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_97,c_2,c_266])).

tff(c_307,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_304,c_302])).

tff(c_323,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_307])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n008.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 19:19:30 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.86/1.26  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.86/1.26  
% 1.86/1.26  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.86/1.27  %$ r1_tarski > v1_relat_1 > k6_subset_1 > k4_xboole_0 > k2_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k3_tarski > #skF_2 > #skF_3 > #skF_1
% 1.86/1.27  
% 1.86/1.27  %Foreground sorts:
% 1.86/1.27  
% 1.86/1.27  
% 1.86/1.27  %Background operators:
% 1.86/1.27  
% 1.86/1.27  
% 1.86/1.27  %Foreground operators:
% 1.86/1.27  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.86/1.27  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.86/1.27  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.86/1.27  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.86/1.27  tff('#skF_2', type, '#skF_2': $i).
% 1.86/1.27  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 1.86/1.27  tff('#skF_3', type, '#skF_3': $i).
% 1.86/1.27  tff('#skF_1', type, '#skF_1': $i).
% 1.86/1.27  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.86/1.27  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 1.86/1.27  tff(k3_tarski, type, k3_tarski: $i > $i).
% 1.86/1.27  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.86/1.27  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.86/1.27  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.86/1.27  
% 1.86/1.28  tff(f_48, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => r1_tarski(k6_subset_1(k10_relat_1(C, A), k10_relat_1(C, B)), k10_relat_1(C, k6_subset_1(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t177_relat_1)).
% 1.86/1.28  tff(f_43, axiom, (![A, B, C]: (v1_relat_1(C) => (k10_relat_1(C, k2_xboole_0(A, B)) = k2_xboole_0(k10_relat_1(C, A), k10_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t175_relat_1)).
% 1.86/1.28  tff(f_33, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 1.86/1.28  tff(f_35, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 1.86/1.28  tff(f_37, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 1.86/1.28  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 1.86/1.28  tff(f_31, axiom, (![A, B, C]: (r1_tarski(A, k2_xboole_0(B, C)) => r1_tarski(k4_xboole_0(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_xboole_1)).
% 1.86/1.28  tff(f_39, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 1.86/1.28  tff(c_18, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.86/1.28  tff(c_251, plain, (![C_50, A_51, B_52]: (k2_xboole_0(k10_relat_1(C_50, A_51), k10_relat_1(C_50, B_52))=k10_relat_1(C_50, k2_xboole_0(A_51, B_52)) | ~v1_relat_1(C_50))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.86/1.28  tff(c_6, plain, (![A_6, B_7]: (r1_tarski(A_6, k2_xboole_0(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.86/1.28  tff(c_304, plain, (![C_53, A_54, B_55]: (r1_tarski(k10_relat_1(C_53, A_54), k10_relat_1(C_53, k2_xboole_0(A_54, B_55))) | ~v1_relat_1(C_53))), inference(superposition, [status(thm), theory('equality')], [c_251, c_6])).
% 1.86/1.28  tff(c_8, plain, (![B_9, A_8]: (k2_tarski(B_9, A_8)=k2_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.86/1.28  tff(c_63, plain, (![A_23, B_24]: (k3_tarski(k2_tarski(A_23, B_24))=k2_xboole_0(A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.86/1.28  tff(c_91, plain, (![B_27, A_28]: (k3_tarski(k2_tarski(B_27, A_28))=k2_xboole_0(A_28, B_27))), inference(superposition, [status(thm), theory('equality')], [c_8, c_63])).
% 1.86/1.28  tff(c_10, plain, (![A_10, B_11]: (k3_tarski(k2_tarski(A_10, B_11))=k2_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.86/1.28  tff(c_97, plain, (![B_27, A_28]: (k2_xboole_0(B_27, A_28)=k2_xboole_0(A_28, B_27))), inference(superposition, [status(thm), theory('equality')], [c_91, c_10])).
% 1.86/1.28  tff(c_2, plain, (![A_1, B_2]: (k2_xboole_0(A_1, k4_xboole_0(B_2, A_1))=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.86/1.28  tff(c_189, plain, (![A_37, B_38, C_39]: (r1_tarski(k4_xboole_0(A_37, B_38), C_39) | ~r1_tarski(A_37, k2_xboole_0(B_38, C_39)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.86/1.28  tff(c_12, plain, (![A_12, B_13]: (k6_subset_1(A_12, B_13)=k4_xboole_0(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.86/1.28  tff(c_16, plain, (~r1_tarski(k6_subset_1(k10_relat_1('#skF_3', '#skF_1'), k10_relat_1('#skF_3', '#skF_2')), k10_relat_1('#skF_3', k6_subset_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.86/1.28  tff(c_19, plain, (~r1_tarski(k4_xboole_0(k10_relat_1('#skF_3', '#skF_1'), k10_relat_1('#skF_3', '#skF_2')), k10_relat_1('#skF_3', k4_xboole_0('#skF_1', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_12, c_16])).
% 1.86/1.28  tff(c_193, plain, (~r1_tarski(k10_relat_1('#skF_3', '#skF_1'), k2_xboole_0(k10_relat_1('#skF_3', '#skF_2'), k10_relat_1('#skF_3', k4_xboole_0('#skF_1', '#skF_2'))))), inference(resolution, [status(thm)], [c_189, c_19])).
% 1.86/1.28  tff(c_266, plain, (~r1_tarski(k10_relat_1('#skF_3', '#skF_1'), k10_relat_1('#skF_3', k2_xboole_0('#skF_2', k4_xboole_0('#skF_1', '#skF_2')))) | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_251, c_193])).
% 1.86/1.28  tff(c_302, plain, (~r1_tarski(k10_relat_1('#skF_3', '#skF_1'), k10_relat_1('#skF_3', k2_xboole_0('#skF_1', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_97, c_2, c_266])).
% 1.86/1.28  tff(c_307, plain, (~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_304, c_302])).
% 1.86/1.28  tff(c_323, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_18, c_307])).
% 1.86/1.28  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.86/1.28  
% 1.86/1.28  Inference rules
% 1.86/1.28  ----------------------
% 1.86/1.28  #Ref     : 0
% 1.86/1.28  #Sup     : 79
% 1.86/1.28  #Fact    : 0
% 1.86/1.28  #Define  : 0
% 1.86/1.28  #Split   : 0
% 1.86/1.28  #Chain   : 0
% 1.86/1.28  #Close   : 0
% 1.86/1.28  
% 1.86/1.28  Ordering : KBO
% 1.86/1.28  
% 1.86/1.28  Simplification rules
% 1.86/1.28  ----------------------
% 1.86/1.28  #Subsume      : 1
% 1.86/1.28  #Demod        : 22
% 1.86/1.28  #Tautology    : 42
% 1.86/1.28  #SimpNegUnit  : 0
% 1.86/1.28  #BackRed      : 0
% 1.86/1.28  
% 1.86/1.28  #Partial instantiations: 0
% 1.86/1.28  #Strategies tried      : 1
% 1.86/1.28  
% 1.86/1.28  Timing (in seconds)
% 1.86/1.28  ----------------------
% 2.18/1.28  Preprocessing        : 0.30
% 2.18/1.28  Parsing              : 0.16
% 2.18/1.28  CNF conversion       : 0.02
% 2.18/1.28  Main loop            : 0.20
% 2.18/1.28  Inferencing          : 0.07
% 2.18/1.28  Reduction            : 0.07
% 2.18/1.28  Demodulation         : 0.06
% 2.18/1.28  BG Simplification    : 0.01
% 2.18/1.28  Subsumption          : 0.03
% 2.18/1.28  Abstraction          : 0.01
% 2.18/1.28  MUC search           : 0.00
% 2.18/1.28  Cooper               : 0.00
% 2.18/1.28  Total                : 0.53
% 2.18/1.28  Index Insertion      : 0.00
% 2.18/1.28  Index Deletion       : 0.00
% 2.18/1.28  Index Matching       : 0.00
% 2.18/1.28  BG Taut test         : 0.00
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:58:16 EST 2020

% Result     : Theorem 2.00s
% Output     : CNFRefutation 2.10s
% Verified   : 
% Statistics : Number of formulae       :   40 (  70 expanded)
%              Number of leaves         :   19 (  33 expanded)
%              Depth                    :    8
%              Number of atoms          :   45 ( 100 expanded)
%              Number of equality atoms :    8 (  22 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k6_subset_1 > k4_xboole_0 > k2_xboole_0 > #nlpp > k1_relat_1 > #skF_2 > #skF_1

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_56,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ! [B] :
            ( v1_relat_1(B)
           => r1_tarski(k6_subset_1(k1_relat_1(A),k1_relat_1(B)),k1_relat_1(k6_subset_1(A,B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t15_relat_1)).

tff(f_48,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k1_relat_1(k2_xboole_0(A,B)) = k2_xboole_0(k1_relat_1(A),k1_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_relat_1)).

tff(f_35,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k4_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_relat_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_29,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_33,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k2_xboole_0(B,C))
     => r1_tarski(k4_xboole_0(A,B),C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(c_20,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_18,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_205,plain,(
    ! [A_51,B_52] :
      ( k2_xboole_0(k1_relat_1(A_51),k1_relat_1(B_52)) = k1_relat_1(k2_xboole_0(A_51,B_52))
      | ~ v1_relat_1(B_52)
      | ~ v1_relat_1(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_8,plain,(
    ! [A_8,B_9] : r1_tarski(A_8,k2_xboole_0(A_8,B_9)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_250,plain,(
    ! [A_51,B_52] :
      ( r1_tarski(k1_relat_1(A_51),k1_relat_1(k2_xboole_0(A_51,B_52)))
      | ~ v1_relat_1(B_52)
      | ~ v1_relat_1(A_51) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_205,c_8])).

tff(c_12,plain,(
    ! [A_12,B_13] :
      ( v1_relat_1(k4_xboole_0(A_12,B_13))
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4,plain,(
    ! [A_3,B_4] : k2_xboole_0(A_3,k4_xboole_0(B_4,A_3)) = k2_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_141,plain,(
    ! [A_38,B_39,C_40] :
      ( r1_tarski(k4_xboole_0(A_38,B_39),C_40)
      | ~ r1_tarski(A_38,k2_xboole_0(B_39,C_40)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_10,plain,(
    ! [A_10,B_11] : k6_subset_1(A_10,B_11) = k4_xboole_0(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_16,plain,(
    ~ r1_tarski(k6_subset_1(k1_relat_1('#skF_1'),k1_relat_1('#skF_2')),k1_relat_1(k6_subset_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_21,plain,(
    ~ r1_tarski(k4_xboole_0(k1_relat_1('#skF_1'),k1_relat_1('#skF_2')),k1_relat_1(k4_xboole_0('#skF_1','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_10,c_16])).

tff(c_145,plain,(
    ~ r1_tarski(k1_relat_1('#skF_1'),k2_xboole_0(k1_relat_1('#skF_2'),k1_relat_1(k4_xboole_0('#skF_1','#skF_2')))) ),
    inference(resolution,[status(thm)],[c_141,c_21])).

tff(c_220,plain,
    ( ~ r1_tarski(k1_relat_1('#skF_1'),k1_relat_1(k2_xboole_0('#skF_2',k4_xboole_0('#skF_1','#skF_2'))))
    | ~ v1_relat_1(k4_xboole_0('#skF_1','#skF_2'))
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_205,c_145])).

tff(c_262,plain,
    ( ~ r1_tarski(k1_relat_1('#skF_1'),k1_relat_1(k2_xboole_0('#skF_1','#skF_2')))
    | ~ v1_relat_1(k4_xboole_0('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_2,c_4,c_220])).

tff(c_277,plain,(
    ~ v1_relat_1(k4_xboole_0('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_262])).

tff(c_280,plain,(
    ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_12,c_277])).

tff(c_284,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_280])).

tff(c_285,plain,(
    ~ r1_tarski(k1_relat_1('#skF_1'),k1_relat_1(k2_xboole_0('#skF_1','#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_262])).

tff(c_289,plain,
    ( ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_250,c_285])).

tff(c_293,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_18,c_289])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:06:16 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.00/1.23  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.00/1.24  
% 2.00/1.24  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.00/1.24  %$ r1_tarski > v1_relat_1 > k6_subset_1 > k4_xboole_0 > k2_xboole_0 > #nlpp > k1_relat_1 > #skF_2 > #skF_1
% 2.00/1.24  
% 2.00/1.24  %Foreground sorts:
% 2.00/1.24  
% 2.00/1.24  
% 2.00/1.24  %Background operators:
% 2.00/1.24  
% 2.00/1.24  
% 2.00/1.24  %Foreground operators:
% 2.00/1.24  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.00/1.24  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.00/1.24  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.00/1.24  tff('#skF_2', type, '#skF_2': $i).
% 2.00/1.24  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 2.00/1.24  tff('#skF_1', type, '#skF_1': $i).
% 2.00/1.24  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.00/1.24  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.00/1.24  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.00/1.24  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.00/1.24  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.00/1.24  
% 2.10/1.25  tff(f_56, negated_conjecture, ~(![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k6_subset_1(k1_relat_1(A), k1_relat_1(B)), k1_relat_1(k6_subset_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t15_relat_1)).
% 2.10/1.25  tff(f_48, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k1_relat_1(k2_xboole_0(A, B)) = k2_xboole_0(k1_relat_1(A), k1_relat_1(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t13_relat_1)).
% 2.10/1.25  tff(f_35, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 2.10/1.25  tff(f_41, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_relat_1)).
% 2.10/1.25  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 2.10/1.25  tff(f_29, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 2.10/1.25  tff(f_33, axiom, (![A, B, C]: (r1_tarski(A, k2_xboole_0(B, C)) => r1_tarski(k4_xboole_0(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_xboole_1)).
% 2.10/1.25  tff(f_37, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 2.10/1.25  tff(c_20, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.10/1.25  tff(c_18, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.10/1.25  tff(c_205, plain, (![A_51, B_52]: (k2_xboole_0(k1_relat_1(A_51), k1_relat_1(B_52))=k1_relat_1(k2_xboole_0(A_51, B_52)) | ~v1_relat_1(B_52) | ~v1_relat_1(A_51))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.10/1.25  tff(c_8, plain, (![A_8, B_9]: (r1_tarski(A_8, k2_xboole_0(A_8, B_9)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.10/1.25  tff(c_250, plain, (![A_51, B_52]: (r1_tarski(k1_relat_1(A_51), k1_relat_1(k2_xboole_0(A_51, B_52))) | ~v1_relat_1(B_52) | ~v1_relat_1(A_51))), inference(superposition, [status(thm), theory('equality')], [c_205, c_8])).
% 2.10/1.25  tff(c_12, plain, (![A_12, B_13]: (v1_relat_1(k4_xboole_0(A_12, B_13)) | ~v1_relat_1(A_12))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.10/1.25  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.10/1.25  tff(c_4, plain, (![A_3, B_4]: (k2_xboole_0(A_3, k4_xboole_0(B_4, A_3))=k2_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.10/1.25  tff(c_141, plain, (![A_38, B_39, C_40]: (r1_tarski(k4_xboole_0(A_38, B_39), C_40) | ~r1_tarski(A_38, k2_xboole_0(B_39, C_40)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.10/1.25  tff(c_10, plain, (![A_10, B_11]: (k6_subset_1(A_10, B_11)=k4_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.10/1.25  tff(c_16, plain, (~r1_tarski(k6_subset_1(k1_relat_1('#skF_1'), k1_relat_1('#skF_2')), k1_relat_1(k6_subset_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.10/1.25  tff(c_21, plain, (~r1_tarski(k4_xboole_0(k1_relat_1('#skF_1'), k1_relat_1('#skF_2')), k1_relat_1(k4_xboole_0('#skF_1', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_10, c_16])).
% 2.10/1.25  tff(c_145, plain, (~r1_tarski(k1_relat_1('#skF_1'), k2_xboole_0(k1_relat_1('#skF_2'), k1_relat_1(k4_xboole_0('#skF_1', '#skF_2'))))), inference(resolution, [status(thm)], [c_141, c_21])).
% 2.10/1.25  tff(c_220, plain, (~r1_tarski(k1_relat_1('#skF_1'), k1_relat_1(k2_xboole_0('#skF_2', k4_xboole_0('#skF_1', '#skF_2')))) | ~v1_relat_1(k4_xboole_0('#skF_1', '#skF_2')) | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_205, c_145])).
% 2.10/1.25  tff(c_262, plain, (~r1_tarski(k1_relat_1('#skF_1'), k1_relat_1(k2_xboole_0('#skF_1', '#skF_2'))) | ~v1_relat_1(k4_xboole_0('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_2, c_4, c_220])).
% 2.10/1.25  tff(c_277, plain, (~v1_relat_1(k4_xboole_0('#skF_1', '#skF_2'))), inference(splitLeft, [status(thm)], [c_262])).
% 2.10/1.25  tff(c_280, plain, (~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_12, c_277])).
% 2.10/1.25  tff(c_284, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_20, c_280])).
% 2.10/1.25  tff(c_285, plain, (~r1_tarski(k1_relat_1('#skF_1'), k1_relat_1(k2_xboole_0('#skF_1', '#skF_2')))), inference(splitRight, [status(thm)], [c_262])).
% 2.10/1.25  tff(c_289, plain, (~v1_relat_1('#skF_2') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_250, c_285])).
% 2.10/1.25  tff(c_293, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_20, c_18, c_289])).
% 2.10/1.25  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.10/1.25  
% 2.10/1.25  Inference rules
% 2.10/1.25  ----------------------
% 2.10/1.25  #Ref     : 0
% 2.10/1.25  #Sup     : 70
% 2.10/1.25  #Fact    : 0
% 2.10/1.25  #Define  : 0
% 2.10/1.25  #Split   : 1
% 2.10/1.25  #Chain   : 0
% 2.10/1.25  #Close   : 0
% 2.10/1.25  
% 2.10/1.25  Ordering : KBO
% 2.10/1.25  
% 2.10/1.25  Simplification rules
% 2.10/1.25  ----------------------
% 2.10/1.25  #Subsume      : 0
% 2.10/1.25  #Demod        : 24
% 2.10/1.25  #Tautology    : 30
% 2.10/1.25  #SimpNegUnit  : 0
% 2.10/1.25  #BackRed      : 0
% 2.10/1.25  
% 2.10/1.25  #Partial instantiations: 0
% 2.10/1.25  #Strategies tried      : 1
% 2.10/1.25  
% 2.10/1.25  Timing (in seconds)
% 2.10/1.25  ----------------------
% 2.10/1.25  Preprocessing        : 0.28
% 2.10/1.25  Parsing              : 0.15
% 2.10/1.25  CNF conversion       : 0.02
% 2.10/1.25  Main loop            : 0.20
% 2.10/1.25  Inferencing          : 0.07
% 2.10/1.25  Reduction            : 0.07
% 2.10/1.25  Demodulation         : 0.06
% 2.10/1.25  BG Simplification    : 0.01
% 2.10/1.25  Subsumption          : 0.04
% 2.10/1.25  Abstraction          : 0.01
% 2.10/1.25  MUC search           : 0.00
% 2.10/1.25  Cooper               : 0.00
% 2.10/1.25  Total                : 0.50
% 2.10/1.25  Index Insertion      : 0.00
% 2.10/1.25  Index Deletion       : 0.00
% 2.10/1.26  Index Matching       : 0.00
% 2.10/1.26  BG Taut test         : 0.00
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:00:17 EST 2020

% Result     : Theorem 1.66s
% Output     : CNFRefutation 1.66s
% Verified   : 
% Statistics : Number of formulae       :   27 (  32 expanded)
%              Number of leaves         :   15 (  19 expanded)
%              Depth                    :    6
%              Number of atoms          :   43 (  59 expanded)
%              Number of equality atoms :    2 (   4 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k8_relat_1 > k5_relat_1 > #nlpp > k6_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k8_relat_1,type,(
    k8_relat_1: ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(f_53,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ! [C] :
            ( v1_relat_1(C)
           => ( r1_tarski(B,C)
             => r1_tarski(k8_relat_1(A,B),k8_relat_1(A,C)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t132_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k8_relat_1(A,B) = k5_relat_1(B,k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_relat_1)).

tff(f_27,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_43,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ! [C] :
              ( v1_relat_1(C)
             => ( r1_tarski(A,B)
               => r1_tarski(k5_relat_1(A,C),k5_relat_1(B,C)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_relat_1)).

tff(c_12,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_14,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_10,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_4,plain,(
    ! [B_3,A_2] :
      ( k5_relat_1(B_3,k6_relat_1(A_2)) = k8_relat_1(A_2,B_3)
      | ~ v1_relat_1(B_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_2,plain,(
    ! [A_1] : v1_relat_1(k6_relat_1(A_1)) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_25,plain,(
    ! [A_15,C_16,B_17] :
      ( r1_tarski(k5_relat_1(A_15,C_16),k5_relat_1(B_17,C_16))
      | ~ r1_tarski(A_15,B_17)
      | ~ v1_relat_1(C_16)
      | ~ v1_relat_1(B_17)
      | ~ v1_relat_1(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_28,plain,(
    ! [A_2,B_3,B_17] :
      ( r1_tarski(k8_relat_1(A_2,B_3),k5_relat_1(B_17,k6_relat_1(A_2)))
      | ~ r1_tarski(B_3,B_17)
      | ~ v1_relat_1(k6_relat_1(A_2))
      | ~ v1_relat_1(B_17)
      | ~ v1_relat_1(B_3)
      | ~ v1_relat_1(B_3) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_25])).

tff(c_36,plain,(
    ! [A_18,B_19,B_20] :
      ( r1_tarski(k8_relat_1(A_18,B_19),k5_relat_1(B_20,k6_relat_1(A_18)))
      | ~ r1_tarski(B_19,B_20)
      | ~ v1_relat_1(B_20)
      | ~ v1_relat_1(B_19) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_28])).

tff(c_44,plain,(
    ! [A_24,B_25,B_26] :
      ( r1_tarski(k8_relat_1(A_24,B_25),k8_relat_1(A_24,B_26))
      | ~ r1_tarski(B_25,B_26)
      | ~ v1_relat_1(B_26)
      | ~ v1_relat_1(B_25)
      | ~ v1_relat_1(B_26) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_36])).

tff(c_8,plain,(
    ~ r1_tarski(k8_relat_1('#skF_1','#skF_2'),k8_relat_1('#skF_1','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_47,plain,
    ( ~ r1_tarski('#skF_2','#skF_3')
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_8])).

tff(c_51,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_14,c_10,c_47])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:36:09 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.66/1.08  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.66/1.08  
% 1.66/1.08  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.66/1.09  %$ r1_tarski > v1_relat_1 > k8_relat_1 > k5_relat_1 > #nlpp > k6_relat_1 > #skF_2 > #skF_3 > #skF_1
% 1.66/1.09  
% 1.66/1.09  %Foreground sorts:
% 1.66/1.09  
% 1.66/1.09  
% 1.66/1.09  %Background operators:
% 1.66/1.09  
% 1.66/1.09  
% 1.66/1.09  %Foreground operators:
% 1.66/1.09  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 1.66/1.09  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.66/1.09  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 1.66/1.09  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.66/1.09  tff('#skF_2', type, '#skF_2': $i).
% 1.66/1.09  tff('#skF_3', type, '#skF_3': $i).
% 1.66/1.09  tff('#skF_1', type, '#skF_1': $i).
% 1.66/1.09  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.66/1.09  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.66/1.09  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 1.66/1.09  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.66/1.09  
% 1.66/1.10  tff(f_53, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (r1_tarski(B, C) => r1_tarski(k8_relat_1(A, B), k8_relat_1(A, C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t132_relat_1)).
% 1.66/1.10  tff(f_31, axiom, (![A, B]: (v1_relat_1(B) => (k8_relat_1(A, B) = k5_relat_1(B, k6_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t123_relat_1)).
% 1.66/1.10  tff(f_27, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 1.66/1.10  tff(f_43, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (r1_tarski(A, B) => r1_tarski(k5_relat_1(A, C), k5_relat_1(B, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_relat_1)).
% 1.66/1.10  tff(c_12, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.66/1.10  tff(c_14, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.66/1.10  tff(c_10, plain, (r1_tarski('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.66/1.10  tff(c_4, plain, (![B_3, A_2]: (k5_relat_1(B_3, k6_relat_1(A_2))=k8_relat_1(A_2, B_3) | ~v1_relat_1(B_3))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.66/1.10  tff(c_2, plain, (![A_1]: (v1_relat_1(k6_relat_1(A_1)))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.66/1.10  tff(c_25, plain, (![A_15, C_16, B_17]: (r1_tarski(k5_relat_1(A_15, C_16), k5_relat_1(B_17, C_16)) | ~r1_tarski(A_15, B_17) | ~v1_relat_1(C_16) | ~v1_relat_1(B_17) | ~v1_relat_1(A_15))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.66/1.10  tff(c_28, plain, (![A_2, B_3, B_17]: (r1_tarski(k8_relat_1(A_2, B_3), k5_relat_1(B_17, k6_relat_1(A_2))) | ~r1_tarski(B_3, B_17) | ~v1_relat_1(k6_relat_1(A_2)) | ~v1_relat_1(B_17) | ~v1_relat_1(B_3) | ~v1_relat_1(B_3))), inference(superposition, [status(thm), theory('equality')], [c_4, c_25])).
% 1.66/1.10  tff(c_36, plain, (![A_18, B_19, B_20]: (r1_tarski(k8_relat_1(A_18, B_19), k5_relat_1(B_20, k6_relat_1(A_18))) | ~r1_tarski(B_19, B_20) | ~v1_relat_1(B_20) | ~v1_relat_1(B_19))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_28])).
% 1.66/1.10  tff(c_44, plain, (![A_24, B_25, B_26]: (r1_tarski(k8_relat_1(A_24, B_25), k8_relat_1(A_24, B_26)) | ~r1_tarski(B_25, B_26) | ~v1_relat_1(B_26) | ~v1_relat_1(B_25) | ~v1_relat_1(B_26))), inference(superposition, [status(thm), theory('equality')], [c_4, c_36])).
% 1.66/1.10  tff(c_8, plain, (~r1_tarski(k8_relat_1('#skF_1', '#skF_2'), k8_relat_1('#skF_1', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.66/1.10  tff(c_47, plain, (~r1_tarski('#skF_2', '#skF_3') | ~v1_relat_1('#skF_2') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_44, c_8])).
% 1.66/1.10  tff(c_51, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12, c_14, c_10, c_47])).
% 1.66/1.10  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.66/1.10  
% 1.66/1.10  Inference rules
% 1.66/1.10  ----------------------
% 1.66/1.10  #Ref     : 0
% 1.66/1.10  #Sup     : 7
% 1.66/1.10  #Fact    : 0
% 1.66/1.10  #Define  : 0
% 1.66/1.10  #Split   : 0
% 1.66/1.10  #Chain   : 0
% 1.66/1.10  #Close   : 0
% 1.66/1.10  
% 1.66/1.10  Ordering : KBO
% 1.66/1.10  
% 1.66/1.10  Simplification rules
% 1.66/1.10  ----------------------
% 1.66/1.10  #Subsume      : 0
% 1.66/1.10  #Demod        : 5
% 1.66/1.10  #Tautology    : 2
% 1.66/1.10  #SimpNegUnit  : 0
% 1.66/1.10  #BackRed      : 0
% 1.66/1.10  
% 1.66/1.10  #Partial instantiations: 0
% 1.66/1.10  #Strategies tried      : 1
% 1.66/1.10  
% 1.66/1.10  Timing (in seconds)
% 1.66/1.10  ----------------------
% 1.66/1.11  Preprocessing        : 0.25
% 1.66/1.11  Parsing              : 0.14
% 1.66/1.11  CNF conversion       : 0.02
% 1.66/1.11  Main loop            : 0.10
% 1.66/1.11  Inferencing          : 0.05
% 1.66/1.11  Reduction            : 0.03
% 1.66/1.11  Demodulation         : 0.03
% 1.66/1.11  BG Simplification    : 0.01
% 1.66/1.11  Subsumption          : 0.01
% 1.66/1.11  Abstraction          : 0.00
% 1.66/1.11  MUC search           : 0.00
% 1.66/1.11  Cooper               : 0.00
% 1.66/1.11  Total                : 0.38
% 1.66/1.11  Index Insertion      : 0.00
% 1.66/1.11  Index Deletion       : 0.00
% 1.66/1.11  Index Matching       : 0.00
% 1.66/1.11  BG Taut test         : 0.00
%------------------------------------------------------------------------------

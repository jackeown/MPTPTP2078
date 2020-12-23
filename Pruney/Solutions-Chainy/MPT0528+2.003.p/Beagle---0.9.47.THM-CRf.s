%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:00:11 EST 2020

% Result     : Theorem 1.64s
% Output     : CNFRefutation 1.64s
% Verified   : 
% Statistics : Number of formulae       :   30 (  31 expanded)
%              Number of leaves         :   17 (  18 expanded)
%              Depth                    :    6
%              Number of atoms          :   39 (  41 expanded)
%              Number of equality atoms :    8 (   9 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k8_relat_1 > k5_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > #skF_2 > #skF_1

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

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

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

tff(f_52,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => k8_relat_1(A,k8_relat_1(A,B)) = k8_relat_1(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t128_relat_1)).

tff(f_33,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k8_relat_1(A,B) = k5_relat_1(B,k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_relat_1(B) )
     => v1_relat_1(k5_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k2_relat_1(k8_relat_1(A,B)),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t116_relat_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k2_relat_1(B),A)
       => k8_relat_1(A,B) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t125_relat_1)).

tff(c_14,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_4,plain,(
    ! [A_3] : v1_relat_1(k6_relat_1(A_3)) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_18,plain,(
    ! [B_15,A_16] :
      ( k5_relat_1(B_15,k6_relat_1(A_16)) = k8_relat_1(A_16,B_15)
      | ~ v1_relat_1(B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( v1_relat_1(k5_relat_1(A_1,B_2))
      | ~ v1_relat_1(B_2)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_24,plain,(
    ! [A_16,B_15] :
      ( v1_relat_1(k8_relat_1(A_16,B_15))
      | ~ v1_relat_1(k6_relat_1(A_16))
      | ~ v1_relat_1(B_15)
      | ~ v1_relat_1(B_15) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_2])).

tff(c_30,plain,(
    ! [A_16,B_15] :
      ( v1_relat_1(k8_relat_1(A_16,B_15))
      | ~ v1_relat_1(B_15) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_24])).

tff(c_6,plain,(
    ! [A_4,B_5] :
      ( r1_tarski(k2_relat_1(k8_relat_1(A_4,B_5)),A_4)
      | ~ v1_relat_1(B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_33,plain,(
    ! [A_19,B_20] :
      ( k8_relat_1(A_19,B_20) = B_20
      | ~ r1_tarski(k2_relat_1(B_20),A_19)
      | ~ v1_relat_1(B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_38,plain,(
    ! [A_21,B_22] :
      ( k8_relat_1(A_21,k8_relat_1(A_21,B_22)) = k8_relat_1(A_21,B_22)
      | ~ v1_relat_1(k8_relat_1(A_21,B_22))
      | ~ v1_relat_1(B_22) ) ),
    inference(resolution,[status(thm)],[c_6,c_33])).

tff(c_42,plain,(
    ! [A_23,B_24] :
      ( k8_relat_1(A_23,k8_relat_1(A_23,B_24)) = k8_relat_1(A_23,B_24)
      | ~ v1_relat_1(B_24) ) ),
    inference(resolution,[status(thm)],[c_30,c_38])).

tff(c_12,plain,(
    k8_relat_1('#skF_1',k8_relat_1('#skF_1','#skF_2')) != k8_relat_1('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_57,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_12])).

tff(c_69,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_57])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n010.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 12:57:29 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.64/1.09  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.64/1.09  
% 1.64/1.09  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.64/1.09  %$ r1_tarski > v1_relat_1 > k8_relat_1 > k5_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > #skF_2 > #skF_1
% 1.64/1.09  
% 1.64/1.09  %Foreground sorts:
% 1.64/1.09  
% 1.64/1.09  
% 1.64/1.09  %Background operators:
% 1.64/1.09  
% 1.64/1.09  
% 1.64/1.09  %Foreground operators:
% 1.64/1.09  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 1.64/1.09  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.64/1.09  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 1.64/1.09  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.64/1.09  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.64/1.09  tff('#skF_2', type, '#skF_2': $i).
% 1.64/1.09  tff('#skF_1', type, '#skF_1': $i).
% 1.64/1.09  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.64/1.09  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.64/1.09  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 1.64/1.09  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.64/1.09  
% 1.64/1.10  tff(f_52, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (k8_relat_1(A, k8_relat_1(A, B)) = k8_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t128_relat_1)).
% 1.64/1.10  tff(f_33, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 1.64/1.10  tff(f_41, axiom, (![A, B]: (v1_relat_1(B) => (k8_relat_1(A, B) = k5_relat_1(B, k6_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t123_relat_1)).
% 1.64/1.10  tff(f_31, axiom, (![A, B]: ((v1_relat_1(A) & v1_relat_1(B)) => v1_relat_1(k5_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k5_relat_1)).
% 1.64/1.10  tff(f_37, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k2_relat_1(k8_relat_1(A, B)), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t116_relat_1)).
% 1.64/1.10  tff(f_47, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k8_relat_1(A, B) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t125_relat_1)).
% 1.64/1.10  tff(c_14, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.64/1.10  tff(c_4, plain, (![A_3]: (v1_relat_1(k6_relat_1(A_3)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.64/1.10  tff(c_18, plain, (![B_15, A_16]: (k5_relat_1(B_15, k6_relat_1(A_16))=k8_relat_1(A_16, B_15) | ~v1_relat_1(B_15))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.64/1.10  tff(c_2, plain, (![A_1, B_2]: (v1_relat_1(k5_relat_1(A_1, B_2)) | ~v1_relat_1(B_2) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.64/1.10  tff(c_24, plain, (![A_16, B_15]: (v1_relat_1(k8_relat_1(A_16, B_15)) | ~v1_relat_1(k6_relat_1(A_16)) | ~v1_relat_1(B_15) | ~v1_relat_1(B_15))), inference(superposition, [status(thm), theory('equality')], [c_18, c_2])).
% 1.64/1.10  tff(c_30, plain, (![A_16, B_15]: (v1_relat_1(k8_relat_1(A_16, B_15)) | ~v1_relat_1(B_15))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_24])).
% 1.64/1.10  tff(c_6, plain, (![A_4, B_5]: (r1_tarski(k2_relat_1(k8_relat_1(A_4, B_5)), A_4) | ~v1_relat_1(B_5))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.64/1.10  tff(c_33, plain, (![A_19, B_20]: (k8_relat_1(A_19, B_20)=B_20 | ~r1_tarski(k2_relat_1(B_20), A_19) | ~v1_relat_1(B_20))), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.64/1.10  tff(c_38, plain, (![A_21, B_22]: (k8_relat_1(A_21, k8_relat_1(A_21, B_22))=k8_relat_1(A_21, B_22) | ~v1_relat_1(k8_relat_1(A_21, B_22)) | ~v1_relat_1(B_22))), inference(resolution, [status(thm)], [c_6, c_33])).
% 1.64/1.10  tff(c_42, plain, (![A_23, B_24]: (k8_relat_1(A_23, k8_relat_1(A_23, B_24))=k8_relat_1(A_23, B_24) | ~v1_relat_1(B_24))), inference(resolution, [status(thm)], [c_30, c_38])).
% 1.64/1.10  tff(c_12, plain, (k8_relat_1('#skF_1', k8_relat_1('#skF_1', '#skF_2'))!=k8_relat_1('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.64/1.10  tff(c_57, plain, (~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_42, c_12])).
% 1.64/1.10  tff(c_69, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_14, c_57])).
% 1.64/1.10  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.64/1.10  
% 1.64/1.10  Inference rules
% 1.64/1.10  ----------------------
% 1.64/1.10  #Ref     : 0
% 1.64/1.10  #Sup     : 12
% 1.64/1.10  #Fact    : 0
% 1.64/1.10  #Define  : 0
% 1.64/1.10  #Split   : 0
% 1.64/1.10  #Chain   : 0
% 1.64/1.10  #Close   : 0
% 1.64/1.10  
% 1.64/1.10  Ordering : KBO
% 1.64/1.10  
% 1.64/1.10  Simplification rules
% 1.64/1.10  ----------------------
% 1.64/1.10  #Subsume      : 3
% 1.64/1.10  #Demod        : 2
% 1.64/1.10  #Tautology    : 4
% 1.64/1.10  #SimpNegUnit  : 0
% 1.64/1.10  #BackRed      : 0
% 1.64/1.10  
% 1.64/1.10  #Partial instantiations: 0
% 1.64/1.10  #Strategies tried      : 1
% 1.64/1.10  
% 1.64/1.10  Timing (in seconds)
% 1.64/1.10  ----------------------
% 1.64/1.10  Preprocessing        : 0.26
% 1.64/1.10  Parsing              : 0.15
% 1.64/1.10  CNF conversion       : 0.01
% 1.64/1.11  Main loop            : 0.10
% 1.64/1.11  Inferencing          : 0.05
% 1.64/1.11  Reduction            : 0.02
% 1.64/1.11  Demodulation         : 0.02
% 1.64/1.11  BG Simplification    : 0.01
% 1.64/1.11  Subsumption          : 0.01
% 1.64/1.11  Abstraction          : 0.00
% 1.64/1.11  MUC search           : 0.00
% 1.64/1.11  Cooper               : 0.00
% 1.64/1.11  Total                : 0.38
% 1.64/1.11  Index Insertion      : 0.00
% 1.64/1.11  Index Deletion       : 0.00
% 1.64/1.11  Index Matching       : 0.00
% 1.64/1.11  BG Taut test         : 0.00
%------------------------------------------------------------------------------

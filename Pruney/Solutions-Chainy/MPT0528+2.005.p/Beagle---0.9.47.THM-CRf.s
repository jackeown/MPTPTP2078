%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:00:11 EST 2020

% Result     : Theorem 1.64s
% Output     : CNFRefutation 1.64s
% Verified   : 
% Statistics : Number of formulae       :   22 (  23 expanded)
%              Number of leaves         :   13 (  14 expanded)
%              Depth                    :    5
%              Number of atoms          :   25 (  27 expanded)
%              Number of equality atoms :    6 (   7 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k8_relat_1 > #nlpp > k2_relat_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k8_relat_1,type,(
    k8_relat_1: ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(f_44,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => k8_relat_1(A,k8_relat_1(A,B)) = k8_relat_1(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t128_relat_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => v1_relat_1(k8_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_relat_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k2_relat_1(k8_relat_1(A,B)),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t116_relat_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k2_relat_1(B),A)
       => k8_relat_1(A,B) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_relat_1)).

tff(c_10,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( v1_relat_1(k8_relat_1(A_1,B_2))
      | ~ v1_relat_1(B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_4,plain,(
    ! [A_3,B_4] :
      ( r1_tarski(k2_relat_1(k8_relat_1(A_3,B_4)),A_3)
      | ~ v1_relat_1(B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_13,plain,(
    ! [A_11,B_12] :
      ( k8_relat_1(A_11,B_12) = B_12
      | ~ r1_tarski(k2_relat_1(B_12),A_11)
      | ~ v1_relat_1(B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_18,plain,(
    ! [A_13,B_14] :
      ( k8_relat_1(A_13,k8_relat_1(A_13,B_14)) = k8_relat_1(A_13,B_14)
      | ~ v1_relat_1(k8_relat_1(A_13,B_14))
      | ~ v1_relat_1(B_14) ) ),
    inference(resolution,[status(thm)],[c_4,c_13])).

tff(c_22,plain,(
    ! [A_15,B_16] :
      ( k8_relat_1(A_15,k8_relat_1(A_15,B_16)) = k8_relat_1(A_15,B_16)
      | ~ v1_relat_1(B_16) ) ),
    inference(resolution,[status(thm)],[c_2,c_18])).

tff(c_8,plain,(
    k8_relat_1('#skF_1',k8_relat_1('#skF_1','#skF_2')) != k8_relat_1('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_31,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_8])).

tff(c_49,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_31])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n021.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 19:22:49 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.64/1.10  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.64/1.10  
% 1.64/1.10  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.64/1.10  %$ r1_tarski > v1_relat_1 > k8_relat_1 > #nlpp > k2_relat_1 > #skF_2 > #skF_1
% 1.64/1.10  
% 1.64/1.10  %Foreground sorts:
% 1.64/1.10  
% 1.64/1.10  
% 1.64/1.10  %Background operators:
% 1.64/1.10  
% 1.64/1.10  
% 1.64/1.10  %Foreground operators:
% 1.64/1.10  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 1.64/1.10  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.64/1.10  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.64/1.10  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.64/1.10  tff('#skF_2', type, '#skF_2': $i).
% 1.64/1.10  tff('#skF_1', type, '#skF_1': $i).
% 1.64/1.10  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.64/1.10  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.64/1.10  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.64/1.10  
% 1.64/1.11  tff(f_44, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (k8_relat_1(A, k8_relat_1(A, B)) = k8_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t128_relat_1)).
% 1.64/1.11  tff(f_29, axiom, (![A, B]: (v1_relat_1(B) => v1_relat_1(k8_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k8_relat_1)).
% 1.64/1.11  tff(f_33, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k2_relat_1(k8_relat_1(A, B)), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t116_relat_1)).
% 1.64/1.11  tff(f_39, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k8_relat_1(A, B) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t125_relat_1)).
% 1.64/1.11  tff(c_10, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.64/1.11  tff(c_2, plain, (![A_1, B_2]: (v1_relat_1(k8_relat_1(A_1, B_2)) | ~v1_relat_1(B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.64/1.11  tff(c_4, plain, (![A_3, B_4]: (r1_tarski(k2_relat_1(k8_relat_1(A_3, B_4)), A_3) | ~v1_relat_1(B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.64/1.11  tff(c_13, plain, (![A_11, B_12]: (k8_relat_1(A_11, B_12)=B_12 | ~r1_tarski(k2_relat_1(B_12), A_11) | ~v1_relat_1(B_12))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.64/1.11  tff(c_18, plain, (![A_13, B_14]: (k8_relat_1(A_13, k8_relat_1(A_13, B_14))=k8_relat_1(A_13, B_14) | ~v1_relat_1(k8_relat_1(A_13, B_14)) | ~v1_relat_1(B_14))), inference(resolution, [status(thm)], [c_4, c_13])).
% 1.64/1.11  tff(c_22, plain, (![A_15, B_16]: (k8_relat_1(A_15, k8_relat_1(A_15, B_16))=k8_relat_1(A_15, B_16) | ~v1_relat_1(B_16))), inference(resolution, [status(thm)], [c_2, c_18])).
% 1.64/1.11  tff(c_8, plain, (k8_relat_1('#skF_1', k8_relat_1('#skF_1', '#skF_2'))!=k8_relat_1('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.64/1.11  tff(c_31, plain, (~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_22, c_8])).
% 1.64/1.11  tff(c_49, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_10, c_31])).
% 1.64/1.11  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.64/1.11  
% 1.64/1.11  Inference rules
% 1.64/1.11  ----------------------
% 1.64/1.11  #Ref     : 0
% 1.64/1.11  #Sup     : 9
% 1.64/1.11  #Fact    : 0
% 1.64/1.11  #Define  : 0
% 1.64/1.11  #Split   : 0
% 1.64/1.11  #Chain   : 0
% 1.64/1.11  #Close   : 0
% 1.64/1.11  
% 1.64/1.11  Ordering : KBO
% 1.64/1.11  
% 1.64/1.11  Simplification rules
% 1.64/1.11  ----------------------
% 1.64/1.11  #Subsume      : 1
% 1.64/1.11  #Demod        : 1
% 1.64/1.11  #Tautology    : 2
% 1.64/1.11  #SimpNegUnit  : 0
% 1.64/1.11  #BackRed      : 0
% 1.64/1.11  
% 1.64/1.11  #Partial instantiations: 0
% 1.64/1.11  #Strategies tried      : 1
% 1.64/1.11  
% 1.64/1.11  Timing (in seconds)
% 1.64/1.11  ----------------------
% 1.64/1.11  Preprocessing        : 0.26
% 1.64/1.11  Parsing              : 0.15
% 1.64/1.11  CNF conversion       : 0.02
% 1.64/1.11  Main loop            : 0.09
% 1.64/1.11  Inferencing          : 0.05
% 1.64/1.11  Reduction            : 0.02
% 1.64/1.11  Demodulation         : 0.01
% 1.64/1.11  BG Simplification    : 0.01
% 1.64/1.11  Subsumption          : 0.01
% 1.64/1.11  Abstraction          : 0.00
% 1.64/1.11  MUC search           : 0.00
% 1.64/1.11  Cooper               : 0.00
% 1.64/1.11  Total                : 0.37
% 1.64/1.11  Index Insertion      : 0.00
% 1.64/1.11  Index Deletion       : 0.00
% 1.64/1.11  Index Matching       : 0.00
% 1.64/1.11  BG Taut test         : 0.00
%------------------------------------------------------------------------------

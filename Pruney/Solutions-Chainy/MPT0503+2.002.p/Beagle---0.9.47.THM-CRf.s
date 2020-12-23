%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:59:48 EST 2020

% Result     : Theorem 1.55s
% Output     : CNFRefutation 1.55s
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
%$ r1_tarski > v1_relat_1 > k7_relat_1 > #nlpp > k1_relat_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_44,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => k7_relat_1(k7_relat_1(B,A),A) = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t101_relat_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k1_relat_1(k7_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_relat_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k7_relat_1(B,A) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_relat_1)).

tff(c_10,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( v1_relat_1(k7_relat_1(A_1,B_2))
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_4,plain,(
    ! [B_4,A_3] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_4,A_3)),A_3)
      | ~ v1_relat_1(B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_13,plain,(
    ! [B_11,A_12] :
      ( k7_relat_1(B_11,A_12) = B_11
      | ~ r1_tarski(k1_relat_1(B_11),A_12)
      | ~ v1_relat_1(B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_18,plain,(
    ! [B_13,A_14] :
      ( k7_relat_1(k7_relat_1(B_13,A_14),A_14) = k7_relat_1(B_13,A_14)
      | ~ v1_relat_1(k7_relat_1(B_13,A_14))
      | ~ v1_relat_1(B_13) ) ),
    inference(resolution,[status(thm)],[c_4,c_13])).

tff(c_22,plain,(
    ! [A_15,B_16] :
      ( k7_relat_1(k7_relat_1(A_15,B_16),B_16) = k7_relat_1(A_15,B_16)
      | ~ v1_relat_1(A_15) ) ),
    inference(resolution,[status(thm)],[c_2,c_18])).

tff(c_8,plain,(
    k7_relat_1(k7_relat_1('#skF_2','#skF_1'),'#skF_1') != k7_relat_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_31,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_8])).

tff(c_49,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_31])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:57:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.55/1.11  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.55/1.11  
% 1.55/1.11  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.55/1.11  %$ r1_tarski > v1_relat_1 > k7_relat_1 > #nlpp > k1_relat_1 > #skF_2 > #skF_1
% 1.55/1.11  
% 1.55/1.11  %Foreground sorts:
% 1.55/1.11  
% 1.55/1.11  
% 1.55/1.11  %Background operators:
% 1.55/1.11  
% 1.55/1.11  
% 1.55/1.11  %Foreground operators:
% 1.55/1.11  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.55/1.11  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 1.55/1.11  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.55/1.11  tff('#skF_2', type, '#skF_2': $i).
% 1.55/1.11  tff('#skF_1', type, '#skF_1': $i).
% 1.55/1.11  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.55/1.11  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.55/1.11  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.55/1.11  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.55/1.11  
% 1.55/1.12  tff(f_44, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (k7_relat_1(k7_relat_1(B, A), A) = k7_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t101_relat_1)).
% 1.55/1.12  tff(f_29, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 1.55/1.12  tff(f_33, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k7_relat_1(B, A)), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t87_relat_1)).
% 1.55/1.12  tff(f_39, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k7_relat_1(B, A) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t97_relat_1)).
% 1.55/1.12  tff(c_10, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.55/1.12  tff(c_2, plain, (![A_1, B_2]: (v1_relat_1(k7_relat_1(A_1, B_2)) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.55/1.12  tff(c_4, plain, (![B_4, A_3]: (r1_tarski(k1_relat_1(k7_relat_1(B_4, A_3)), A_3) | ~v1_relat_1(B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.55/1.12  tff(c_13, plain, (![B_11, A_12]: (k7_relat_1(B_11, A_12)=B_11 | ~r1_tarski(k1_relat_1(B_11), A_12) | ~v1_relat_1(B_11))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.55/1.12  tff(c_18, plain, (![B_13, A_14]: (k7_relat_1(k7_relat_1(B_13, A_14), A_14)=k7_relat_1(B_13, A_14) | ~v1_relat_1(k7_relat_1(B_13, A_14)) | ~v1_relat_1(B_13))), inference(resolution, [status(thm)], [c_4, c_13])).
% 1.55/1.12  tff(c_22, plain, (![A_15, B_16]: (k7_relat_1(k7_relat_1(A_15, B_16), B_16)=k7_relat_1(A_15, B_16) | ~v1_relat_1(A_15))), inference(resolution, [status(thm)], [c_2, c_18])).
% 1.55/1.12  tff(c_8, plain, (k7_relat_1(k7_relat_1('#skF_2', '#skF_1'), '#skF_1')!=k7_relat_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.55/1.12  tff(c_31, plain, (~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_22, c_8])).
% 1.55/1.12  tff(c_49, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_10, c_31])).
% 1.55/1.12  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.55/1.12  
% 1.55/1.12  Inference rules
% 1.55/1.12  ----------------------
% 1.55/1.12  #Ref     : 0
% 1.55/1.12  #Sup     : 9
% 1.55/1.12  #Fact    : 0
% 1.55/1.12  #Define  : 0
% 1.55/1.12  #Split   : 0
% 1.55/1.12  #Chain   : 0
% 1.55/1.12  #Close   : 0
% 1.55/1.12  
% 1.55/1.12  Ordering : KBO
% 1.55/1.12  
% 1.55/1.12  Simplification rules
% 1.55/1.12  ----------------------
% 1.55/1.12  #Subsume      : 1
% 1.55/1.12  #Demod        : 1
% 1.55/1.12  #Tautology    : 2
% 1.55/1.12  #SimpNegUnit  : 0
% 1.55/1.12  #BackRed      : 0
% 1.55/1.12  
% 1.55/1.12  #Partial instantiations: 0
% 1.55/1.12  #Strategies tried      : 1
% 1.55/1.12  
% 1.55/1.12  Timing (in seconds)
% 1.55/1.12  ----------------------
% 1.65/1.12  Preprocessing        : 0.25
% 1.65/1.12  Parsing              : 0.14
% 1.65/1.12  CNF conversion       : 0.01
% 1.65/1.12  Main loop            : 0.09
% 1.65/1.12  Inferencing          : 0.04
% 1.65/1.12  Reduction            : 0.02
% 1.65/1.12  Demodulation         : 0.01
% 1.65/1.12  BG Simplification    : 0.01
% 1.65/1.12  Subsumption          : 0.01
% 1.65/1.12  Abstraction          : 0.00
% 1.65/1.12  MUC search           : 0.00
% 1.65/1.12  Cooper               : 0.00
% 1.65/1.12  Total                : 0.35
% 1.65/1.12  Index Insertion      : 0.00
% 1.65/1.12  Index Deletion       : 0.00
% 1.65/1.12  Index Matching       : 0.00
% 1.65/1.12  BG Taut test         : 0.00
%------------------------------------------------------------------------------

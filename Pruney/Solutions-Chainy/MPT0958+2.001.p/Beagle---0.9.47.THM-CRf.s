%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:10:36 EST 2020

% Result     : Theorem 2.03s
% Output     : CNFRefutation 2.03s
% Verified   : 
% Statistics : Number of formulae       :   28 (  30 expanded)
%              Number of leaves         :   19 (  20 expanded)
%              Depth                    :    5
%              Number of atoms          :   27 (  29 expanded)
%              Number of equality atoms :    4 (   4 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r4_relat_2 > r2_hidden > r1_tarski > v4_relat_2 > v1_relat_1 > k4_tarski > #nlpp > k3_relat_1 > k1_wellord2 > #skF_3 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(r4_relat_2,type,(
    r4_relat_2: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k3_relat_1,type,(
    k3_relat_1: $i > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(v4_relat_2,type,(
    v4_relat_2: $i > $o )).

tff(k1_wellord2,type,(
    k1_wellord2: $i > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_48,axiom,(
    ! [A] : v1_relat_1(k1_wellord2(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_wellord2)).

tff(f_50,axiom,(
    ! [A] : v4_relat_2(k1_wellord2(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_wellord2)).

tff(f_46,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( B = k1_wellord2(A)
      <=> ( k3_relat_1(B) = A
          & ! [C,D] :
              ( ( r2_hidden(C,A)
                & r2_hidden(D,A) )
             => ( r2_hidden(k4_tarski(C,D),B)
              <=> r1_tarski(C,D) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_wellord2)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( v4_relat_2(A)
      <=> r4_relat_2(A,k3_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d12_relat_2)).

tff(f_53,negated_conjecture,(
    ~ ! [A] : r4_relat_2(k1_wellord2(A),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_wellord2)).

tff(c_24,plain,(
    ! [A_10] : v1_relat_1(k1_wellord2(A_10)) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_26,plain,(
    ! [A_11] : v4_relat_2(k1_wellord2(A_11)) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_18,plain,(
    ! [A_2] :
      ( k3_relat_1(k1_wellord2(A_2)) = A_2
      | ~ v1_relat_1(k1_wellord2(A_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_34,plain,(
    ! [A_2] : k3_relat_1(k1_wellord2(A_2)) = A_2 ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_18])).

tff(c_46,plain,(
    ! [A_15] :
      ( r4_relat_2(A_15,k3_relat_1(A_15))
      | ~ v4_relat_2(A_15)
      | ~ v1_relat_1(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_49,plain,(
    ! [A_2] :
      ( r4_relat_2(k1_wellord2(A_2),A_2)
      | ~ v4_relat_2(k1_wellord2(A_2))
      | ~ v1_relat_1(k1_wellord2(A_2)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_46])).

tff(c_51,plain,(
    ! [A_2] : r4_relat_2(k1_wellord2(A_2),A_2) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_26,c_49])).

tff(c_28,plain,(
    ~ r4_relat_2(k1_wellord2('#skF_3'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_64,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_51,c_28])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:06:26 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.03/1.49  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.03/1.49  
% 2.03/1.49  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.03/1.50  %$ r4_relat_2 > r2_hidden > r1_tarski > v4_relat_2 > v1_relat_1 > k4_tarski > #nlpp > k3_relat_1 > k1_wellord2 > #skF_3 > #skF_2 > #skF_1
% 2.03/1.50  
% 2.03/1.50  %Foreground sorts:
% 2.03/1.50  
% 2.03/1.50  
% 2.03/1.50  %Background operators:
% 2.03/1.50  
% 2.03/1.50  
% 2.03/1.50  %Foreground operators:
% 2.03/1.50  tff(r4_relat_2, type, r4_relat_2: ($i * $i) > $o).
% 2.03/1.50  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.03/1.50  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.03/1.50  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.03/1.50  tff(k3_relat_1, type, k3_relat_1: $i > $i).
% 2.03/1.50  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.03/1.50  tff(v4_relat_2, type, v4_relat_2: $i > $o).
% 2.03/1.50  tff(k1_wellord2, type, k1_wellord2: $i > $i).
% 2.03/1.50  tff('#skF_3', type, '#skF_3': $i).
% 2.03/1.50  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.03/1.50  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.03/1.50  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.03/1.50  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.03/1.50  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.03/1.50  
% 2.03/1.51  tff(f_48, axiom, (![A]: v1_relat_1(k1_wellord2(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_wellord2)).
% 2.03/1.51  tff(f_50, axiom, (![A]: v4_relat_2(k1_wellord2(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_wellord2)).
% 2.03/1.51  tff(f_46, axiom, (![A, B]: (v1_relat_1(B) => ((B = k1_wellord2(A)) <=> ((k3_relat_1(B) = A) & (![C, D]: ((r2_hidden(C, A) & r2_hidden(D, A)) => (r2_hidden(k4_tarski(C, D), B) <=> r1_tarski(C, D)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_wellord2)).
% 2.03/1.51  tff(f_31, axiom, (![A]: (v1_relat_1(A) => (v4_relat_2(A) <=> r4_relat_2(A, k3_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d12_relat_2)).
% 2.03/1.51  tff(f_53, negated_conjecture, ~(![A]: r4_relat_2(k1_wellord2(A), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_wellord2)).
% 2.03/1.51  tff(c_24, plain, (![A_10]: (v1_relat_1(k1_wellord2(A_10)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.03/1.51  tff(c_26, plain, (![A_11]: (v4_relat_2(k1_wellord2(A_11)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.03/1.51  tff(c_18, plain, (![A_2]: (k3_relat_1(k1_wellord2(A_2))=A_2 | ~v1_relat_1(k1_wellord2(A_2)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.03/1.51  tff(c_34, plain, (![A_2]: (k3_relat_1(k1_wellord2(A_2))=A_2)), inference(demodulation, [status(thm), theory('equality')], [c_24, c_18])).
% 2.03/1.51  tff(c_46, plain, (![A_15]: (r4_relat_2(A_15, k3_relat_1(A_15)) | ~v4_relat_2(A_15) | ~v1_relat_1(A_15))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.03/1.51  tff(c_49, plain, (![A_2]: (r4_relat_2(k1_wellord2(A_2), A_2) | ~v4_relat_2(k1_wellord2(A_2)) | ~v1_relat_1(k1_wellord2(A_2)))), inference(superposition, [status(thm), theory('equality')], [c_34, c_46])).
% 2.03/1.51  tff(c_51, plain, (![A_2]: (r4_relat_2(k1_wellord2(A_2), A_2))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_26, c_49])).
% 2.03/1.51  tff(c_28, plain, (~r4_relat_2(k1_wellord2('#skF_3'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.03/1.51  tff(c_64, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_51, c_28])).
% 2.03/1.51  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.03/1.51  
% 2.03/1.51  Inference rules
% 2.03/1.51  ----------------------
% 2.03/1.51  #Ref     : 0
% 2.03/1.51  #Sup     : 5
% 2.03/1.51  #Fact    : 0
% 2.03/1.51  #Define  : 0
% 2.03/1.51  #Split   : 0
% 2.03/1.51  #Chain   : 0
% 2.03/1.51  #Close   : 0
% 2.03/1.51  
% 2.03/1.51  Ordering : KBO
% 2.03/1.51  
% 2.03/1.51  Simplification rules
% 2.03/1.51  ----------------------
% 2.03/1.51  #Subsume      : 0
% 2.03/1.51  #Demod        : 8
% 2.03/1.51  #Tautology    : 6
% 2.03/1.51  #SimpNegUnit  : 0
% 2.03/1.51  #BackRed      : 1
% 2.03/1.51  
% 2.03/1.51  #Partial instantiations: 0
% 2.03/1.51  #Strategies tried      : 1
% 2.03/1.51  
% 2.03/1.51  Timing (in seconds)
% 2.03/1.51  ----------------------
% 2.03/1.52  Preprocessing        : 0.44
% 2.03/1.52  Parsing              : 0.22
% 2.03/1.52  CNF conversion       : 0.03
% 2.03/1.52  Main loop            : 0.15
% 2.03/1.52  Inferencing          : 0.05
% 2.03/1.52  Reduction            : 0.05
% 2.03/1.52  Demodulation         : 0.04
% 2.03/1.52  BG Simplification    : 0.02
% 2.03/1.52  Subsumption          : 0.02
% 2.03/1.52  Abstraction          : 0.01
% 2.03/1.52  MUC search           : 0.00
% 2.03/1.52  Cooper               : 0.00
% 2.03/1.52  Total                : 0.62
% 2.03/1.52  Index Insertion      : 0.00
% 2.03/1.52  Index Deletion       : 0.00
% 2.03/1.52  Index Matching       : 0.00
% 2.03/1.52  BG Taut test         : 0.00
%------------------------------------------------------------------------------

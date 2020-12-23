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
% DateTime   : Thu Dec  3 10:10:35 EST 2020

% Result     : Theorem 1.58s
% Output     : CNFRefutation 1.58s
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
%$ r2_hidden > r1_tarski > r1_relat_2 > v1_relat_2 > v1_relat_1 > k4_tarski > #nlpp > k3_relat_1 > k1_wellord2 > #skF_3 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(v1_relat_2,type,(
    v1_relat_2: $i > $o )).

tff(k3_relat_1,type,(
    k3_relat_1: $i > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(r1_relat_2,type,(
    r1_relat_2: ( $i * $i ) > $o )).

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
    ! [A] : v1_relat_2(k1_wellord2(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_wellord2)).

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
     => ( v1_relat_2(A)
      <=> r1_relat_2(A,k3_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_relat_2)).

tff(f_53,negated_conjecture,(
    ~ ! [A] : r1_relat_2(k1_wellord2(A),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_wellord2)).

tff(c_24,plain,(
    ! [A_10] : v1_relat_1(k1_wellord2(A_10)) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_26,plain,(
    ! [A_11] : v1_relat_2(k1_wellord2(A_11)) ),
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
      ( r1_relat_2(A_15,k3_relat_1(A_15))
      | ~ v1_relat_2(A_15)
      | ~ v1_relat_1(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_49,plain,(
    ! [A_2] :
      ( r1_relat_2(k1_wellord2(A_2),A_2)
      | ~ v1_relat_2(k1_wellord2(A_2))
      | ~ v1_relat_1(k1_wellord2(A_2)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_46])).

tff(c_51,plain,(
    ! [A_2] : r1_relat_2(k1_wellord2(A_2),A_2) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_26,c_49])).

tff(c_28,plain,(
    ~ r1_relat_2(k1_wellord2('#skF_3'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_64,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_51,c_28])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:53:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.58/1.11  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.58/1.11  
% 1.58/1.11  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.58/1.11  %$ r2_hidden > r1_tarski > r1_relat_2 > v1_relat_2 > v1_relat_1 > k4_tarski > #nlpp > k3_relat_1 > k1_wellord2 > #skF_3 > #skF_2 > #skF_1
% 1.58/1.11  
% 1.58/1.11  %Foreground sorts:
% 1.58/1.11  
% 1.58/1.11  
% 1.58/1.11  %Background operators:
% 1.58/1.11  
% 1.58/1.11  
% 1.58/1.11  %Foreground operators:
% 1.58/1.11  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.58/1.11  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.58/1.11  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 1.58/1.11  tff(v1_relat_2, type, v1_relat_2: $i > $o).
% 1.58/1.11  tff(k3_relat_1, type, k3_relat_1: $i > $i).
% 1.58/1.11  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.58/1.11  tff(r1_relat_2, type, r1_relat_2: ($i * $i) > $o).
% 1.58/1.11  tff(k1_wellord2, type, k1_wellord2: $i > $i).
% 1.58/1.11  tff('#skF_3', type, '#skF_3': $i).
% 1.58/1.11  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.58/1.11  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.58/1.11  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.58/1.11  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 1.58/1.11  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.58/1.11  
% 1.58/1.12  tff(f_48, axiom, (![A]: v1_relat_1(k1_wellord2(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_wellord2)).
% 1.58/1.12  tff(f_50, axiom, (![A]: v1_relat_2(k1_wellord2(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_wellord2)).
% 1.58/1.12  tff(f_46, axiom, (![A, B]: (v1_relat_1(B) => ((B = k1_wellord2(A)) <=> ((k3_relat_1(B) = A) & (![C, D]: ((r2_hidden(C, A) & r2_hidden(D, A)) => (r2_hidden(k4_tarski(C, D), B) <=> r1_tarski(C, D)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_wellord2)).
% 1.58/1.12  tff(f_31, axiom, (![A]: (v1_relat_1(A) => (v1_relat_2(A) <=> r1_relat_2(A, k3_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d9_relat_2)).
% 1.58/1.12  tff(f_53, negated_conjecture, ~(![A]: r1_relat_2(k1_wellord2(A), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_wellord2)).
% 1.58/1.12  tff(c_24, plain, (![A_10]: (v1_relat_1(k1_wellord2(A_10)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.58/1.12  tff(c_26, plain, (![A_11]: (v1_relat_2(k1_wellord2(A_11)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.58/1.12  tff(c_18, plain, (![A_2]: (k3_relat_1(k1_wellord2(A_2))=A_2 | ~v1_relat_1(k1_wellord2(A_2)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.58/1.12  tff(c_34, plain, (![A_2]: (k3_relat_1(k1_wellord2(A_2))=A_2)), inference(demodulation, [status(thm), theory('equality')], [c_24, c_18])).
% 1.58/1.12  tff(c_46, plain, (![A_15]: (r1_relat_2(A_15, k3_relat_1(A_15)) | ~v1_relat_2(A_15) | ~v1_relat_1(A_15))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.58/1.12  tff(c_49, plain, (![A_2]: (r1_relat_2(k1_wellord2(A_2), A_2) | ~v1_relat_2(k1_wellord2(A_2)) | ~v1_relat_1(k1_wellord2(A_2)))), inference(superposition, [status(thm), theory('equality')], [c_34, c_46])).
% 1.58/1.12  tff(c_51, plain, (![A_2]: (r1_relat_2(k1_wellord2(A_2), A_2))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_26, c_49])).
% 1.58/1.12  tff(c_28, plain, (~r1_relat_2(k1_wellord2('#skF_3'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.58/1.12  tff(c_64, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_51, c_28])).
% 1.58/1.12  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.58/1.12  
% 1.58/1.12  Inference rules
% 1.58/1.12  ----------------------
% 1.58/1.12  #Ref     : 0
% 1.58/1.12  #Sup     : 5
% 1.58/1.12  #Fact    : 0
% 1.58/1.12  #Define  : 0
% 1.58/1.12  #Split   : 0
% 1.58/1.12  #Chain   : 0
% 1.58/1.12  #Close   : 0
% 1.58/1.12  
% 1.58/1.12  Ordering : KBO
% 1.58/1.12  
% 1.58/1.12  Simplification rules
% 1.58/1.12  ----------------------
% 1.58/1.12  #Subsume      : 0
% 1.58/1.12  #Demod        : 8
% 1.58/1.12  #Tautology    : 6
% 1.58/1.12  #SimpNegUnit  : 0
% 1.58/1.12  #BackRed      : 1
% 1.58/1.12  
% 1.58/1.12  #Partial instantiations: 0
% 1.58/1.12  #Strategies tried      : 1
% 1.58/1.12  
% 1.58/1.12  Timing (in seconds)
% 1.58/1.12  ----------------------
% 1.58/1.12  Preprocessing        : 0.27
% 1.58/1.12  Parsing              : 0.14
% 1.58/1.12  CNF conversion       : 0.02
% 1.58/1.12  Main loop            : 0.08
% 1.58/1.12  Inferencing          : 0.03
% 1.58/1.12  Reduction            : 0.03
% 1.58/1.12  Demodulation         : 0.02
% 1.58/1.12  BG Simplification    : 0.01
% 1.58/1.12  Subsumption          : 0.01
% 1.58/1.12  Abstraction          : 0.00
% 1.58/1.12  MUC search           : 0.00
% 1.58/1.12  Cooper               : 0.00
% 1.58/1.12  Total                : 0.37
% 1.58/1.12  Index Insertion      : 0.00
% 1.58/1.12  Index Deletion       : 0.00
% 1.58/1.12  Index Matching       : 0.00
% 1.58/1.12  BG Taut test         : 0.00
%------------------------------------------------------------------------------

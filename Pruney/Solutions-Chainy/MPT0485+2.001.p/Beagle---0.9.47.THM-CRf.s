%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:59:33 EST 2020

% Result     : Theorem 1.69s
% Output     : CNFRefutation 1.69s
% Verified   : 
% Statistics : Number of formulae       :   19 (  20 expanded)
%              Number of leaves         :   12 (  13 expanded)
%              Depth                    :    4
%              Number of atoms          :   18 (  20 expanded)
%              Number of equality atoms :    6 (   7 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k5_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

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

tff(f_42,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => k5_relat_1(A,k6_relat_1(k2_relat_1(A))) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_37,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k2_relat_1(B),A)
       => k5_relat_1(B,k6_relat_1(A)) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_relat_1)).

tff(c_12,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_22,plain,(
    ! [B_8,A_9] :
      ( k5_relat_1(B_8,k6_relat_1(A_9)) = B_8
      | ~ r1_tarski(k2_relat_1(B_8),A_9)
      | ~ v1_relat_1(B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_28,plain,(
    ! [B_10] :
      ( k5_relat_1(B_10,k6_relat_1(k2_relat_1(B_10))) = B_10
      | ~ v1_relat_1(B_10) ) ),
    inference(resolution,[status(thm)],[c_6,c_22])).

tff(c_10,plain,(
    k5_relat_1('#skF_1',k6_relat_1(k2_relat_1('#skF_1'))) != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_34,plain,(
    ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_10])).

tff(c_42,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_34])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n013.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 15:20:24 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.69/1.14  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.69/1.15  
% 1.69/1.15  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.69/1.15  %$ r1_tarski > v1_relat_1 > k5_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > #skF_1
% 1.69/1.15  
% 1.69/1.15  %Foreground sorts:
% 1.69/1.15  
% 1.69/1.15  
% 1.69/1.15  %Background operators:
% 1.69/1.15  
% 1.69/1.15  
% 1.69/1.15  %Foreground operators:
% 1.69/1.15  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.69/1.15  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 1.69/1.15  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.69/1.15  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.69/1.15  tff('#skF_1', type, '#skF_1': $i).
% 1.69/1.15  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.69/1.15  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.69/1.15  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 1.69/1.15  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.69/1.15  
% 1.69/1.15  tff(f_42, negated_conjecture, ~(![A]: (v1_relat_1(A) => (k5_relat_1(A, k6_relat_1(k2_relat_1(A))) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t80_relat_1)).
% 1.69/1.15  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 1.69/1.15  tff(f_37, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k5_relat_1(B, k6_relat_1(A)) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_relat_1)).
% 1.69/1.15  tff(c_12, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.69/1.15  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.69/1.15  tff(c_22, plain, (![B_8, A_9]: (k5_relat_1(B_8, k6_relat_1(A_9))=B_8 | ~r1_tarski(k2_relat_1(B_8), A_9) | ~v1_relat_1(B_8))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.69/1.15  tff(c_28, plain, (![B_10]: (k5_relat_1(B_10, k6_relat_1(k2_relat_1(B_10)))=B_10 | ~v1_relat_1(B_10))), inference(resolution, [status(thm)], [c_6, c_22])).
% 1.69/1.15  tff(c_10, plain, (k5_relat_1('#skF_1', k6_relat_1(k2_relat_1('#skF_1')))!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.69/1.15  tff(c_34, plain, (~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_28, c_10])).
% 1.69/1.15  tff(c_42, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12, c_34])).
% 1.69/1.15  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.69/1.15  
% 1.69/1.15  Inference rules
% 1.69/1.15  ----------------------
% 1.69/1.15  #Ref     : 0
% 1.69/1.15  #Sup     : 5
% 1.69/1.15  #Fact    : 0
% 1.69/1.15  #Define  : 0
% 1.69/1.15  #Split   : 0
% 1.69/1.15  #Chain   : 0
% 1.69/1.15  #Close   : 0
% 1.69/1.15  
% 1.69/1.15  Ordering : KBO
% 1.69/1.15  
% 1.69/1.15  Simplification rules
% 1.69/1.15  ----------------------
% 1.69/1.15  #Subsume      : 0
% 1.69/1.15  #Demod        : 3
% 1.69/1.15  #Tautology    : 3
% 1.69/1.15  #SimpNegUnit  : 0
% 1.69/1.15  #BackRed      : 0
% 1.69/1.15  
% 1.69/1.15  #Partial instantiations: 0
% 1.69/1.15  #Strategies tried      : 1
% 1.69/1.15  
% 1.69/1.16  Timing (in seconds)
% 1.69/1.16  ----------------------
% 1.69/1.16  Preprocessing        : 0.26
% 1.69/1.16  Parsing              : 0.15
% 1.69/1.16  CNF conversion       : 0.01
% 1.69/1.16  Main loop            : 0.07
% 1.69/1.16  Inferencing          : 0.03
% 1.69/1.16  Reduction            : 0.02
% 1.69/1.16  Demodulation         : 0.01
% 1.69/1.16  BG Simplification    : 0.01
% 1.69/1.16  Subsumption          : 0.01
% 1.69/1.16  Abstraction          : 0.00
% 1.69/1.16  MUC search           : 0.00
% 1.69/1.16  Cooper               : 0.00
% 1.69/1.16  Total                : 0.35
% 1.69/1.16  Index Insertion      : 0.00
% 1.69/1.16  Index Deletion       : 0.00
% 1.69/1.16  Index Matching       : 0.00
% 1.69/1.16  BG Taut test         : 0.00
%------------------------------------------------------------------------------

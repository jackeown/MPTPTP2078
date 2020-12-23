%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:59:47 EST 2020

% Result     : Theorem 1.46s
% Output     : CNFRefutation 1.57s
% Verified   : 
% Statistics : Number of formulae       :   18 (  19 expanded)
%              Number of leaves         :   11 (  12 expanded)
%              Depth                    :    4
%              Number of atoms          :   18 (  20 expanded)
%              Number of equality atoms :    6 (   7 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k7_relat_1 > #nlpp > k1_relat_1 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(f_42,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => k7_relat_1(A,k1_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_37,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k7_relat_1(B,A) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_relat_1)).

tff(c_12,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_22,plain,(
    ! [B_8,A_9] :
      ( k7_relat_1(B_8,A_9) = B_8
      | ~ r1_tarski(k1_relat_1(B_8),A_9)
      | ~ v1_relat_1(B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_28,plain,(
    ! [B_10] :
      ( k7_relat_1(B_10,k1_relat_1(B_10)) = B_10
      | ~ v1_relat_1(B_10) ) ),
    inference(resolution,[status(thm)],[c_6,c_22])).

tff(c_10,plain,(
    k7_relat_1('#skF_1',k1_relat_1('#skF_1')) != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_34,plain,(
    ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_10])).

tff(c_42,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_34])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:13:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.46/1.05  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.46/1.05  
% 1.46/1.05  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.57/1.05  %$ r1_tarski > v1_relat_1 > k7_relat_1 > #nlpp > k1_relat_1 > #skF_1
% 1.57/1.05  
% 1.57/1.05  %Foreground sorts:
% 1.57/1.05  
% 1.57/1.05  
% 1.57/1.05  %Background operators:
% 1.57/1.05  
% 1.57/1.05  
% 1.57/1.05  %Foreground operators:
% 1.57/1.05  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.57/1.05  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 1.57/1.05  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.57/1.05  tff('#skF_1', type, '#skF_1': $i).
% 1.57/1.05  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.57/1.05  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.57/1.05  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.57/1.05  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.57/1.05  
% 1.57/1.06  tff(f_42, negated_conjecture, ~(![A]: (v1_relat_1(A) => (k7_relat_1(A, k1_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_relat_1)).
% 1.57/1.06  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 1.57/1.06  tff(f_37, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k7_relat_1(B, A) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t97_relat_1)).
% 1.57/1.06  tff(c_12, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.57/1.06  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.57/1.06  tff(c_22, plain, (![B_8, A_9]: (k7_relat_1(B_8, A_9)=B_8 | ~r1_tarski(k1_relat_1(B_8), A_9) | ~v1_relat_1(B_8))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.57/1.06  tff(c_28, plain, (![B_10]: (k7_relat_1(B_10, k1_relat_1(B_10))=B_10 | ~v1_relat_1(B_10))), inference(resolution, [status(thm)], [c_6, c_22])).
% 1.57/1.06  tff(c_10, plain, (k7_relat_1('#skF_1', k1_relat_1('#skF_1'))!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.57/1.06  tff(c_34, plain, (~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_28, c_10])).
% 1.57/1.06  tff(c_42, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12, c_34])).
% 1.57/1.06  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.57/1.06  
% 1.57/1.06  Inference rules
% 1.57/1.06  ----------------------
% 1.57/1.06  #Ref     : 0
% 1.57/1.06  #Sup     : 5
% 1.57/1.06  #Fact    : 0
% 1.57/1.06  #Define  : 0
% 1.57/1.06  #Split   : 0
% 1.57/1.06  #Chain   : 0
% 1.57/1.06  #Close   : 0
% 1.57/1.06  
% 1.57/1.06  Ordering : KBO
% 1.57/1.06  
% 1.57/1.06  Simplification rules
% 1.57/1.06  ----------------------
% 1.57/1.06  #Subsume      : 0
% 1.57/1.06  #Demod        : 3
% 1.57/1.06  #Tautology    : 3
% 1.57/1.06  #SimpNegUnit  : 0
% 1.57/1.06  #BackRed      : 0
% 1.57/1.06  
% 1.57/1.06  #Partial instantiations: 0
% 1.57/1.06  #Strategies tried      : 1
% 1.57/1.06  
% 1.57/1.06  Timing (in seconds)
% 1.57/1.06  ----------------------
% 1.57/1.06  Preprocessing        : 0.24
% 1.57/1.06  Parsing              : 0.13
% 1.57/1.06  CNF conversion       : 0.01
% 1.57/1.06  Main loop            : 0.07
% 1.57/1.06  Inferencing          : 0.03
% 1.57/1.06  Reduction            : 0.02
% 1.57/1.06  Demodulation         : 0.02
% 1.57/1.06  BG Simplification    : 0.01
% 1.57/1.06  Subsumption          : 0.01
% 1.57/1.06  Abstraction          : 0.00
% 1.57/1.06  MUC search           : 0.00
% 1.57/1.06  Cooper               : 0.00
% 1.57/1.06  Total                : 0.34
% 1.57/1.06  Index Insertion      : 0.00
% 1.57/1.06  Index Deletion       : 0.00
% 1.57/1.06  Index Matching       : 0.00
% 1.57/1.06  BG Taut test         : 0.00
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:06:47 EST 2020

% Result     : Theorem 1.59s
% Output     : CNFRefutation 1.59s
% Verified   : 
% Statistics : Number of formulae       :   22 (  24 expanded)
%              Number of leaves         :   14 (  16 expanded)
%              Depth                    :    4
%              Number of atoms          :   24 (  30 expanded)
%              Number of equality atoms :    5 (   7 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v2_wellord1 > v1_relat_1 > k2_wellord1 > k1_wellord1 > #nlpp > k3_relat_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k3_relat_1,type,(
    k3_relat_1: $i > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(v2_wellord1,type,(
    v2_wellord1: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k1_wellord1,type,(
    k1_wellord1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_wellord1,type,(
    k2_wellord1: ( $i * $i ) > $i )).

tff(f_44,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( v2_wellord1(B)
         => k3_relat_1(k2_wellord1(B,k1_wellord1(B,A))) = k1_wellord1(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_wellord1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k1_wellord1(B,A),k3_relat_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_wellord1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( ( v2_wellord1(B)
          & r1_tarski(A,k3_relat_1(B)) )
       => k3_relat_1(k2_wellord1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_wellord1)).

tff(c_10,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_8,plain,(
    v2_wellord1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( r1_tarski(k1_wellord1(B_2,A_1),k3_relat_1(B_2))
      | ~ v1_relat_1(B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_12,plain,(
    ! [B_7,A_8] :
      ( k3_relat_1(k2_wellord1(B_7,A_8)) = A_8
      | ~ r1_tarski(A_8,k3_relat_1(B_7))
      | ~ v2_wellord1(B_7)
      | ~ v1_relat_1(B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_17,plain,(
    ! [B_9,A_10] :
      ( k3_relat_1(k2_wellord1(B_9,k1_wellord1(B_9,A_10))) = k1_wellord1(B_9,A_10)
      | ~ v2_wellord1(B_9)
      | ~ v1_relat_1(B_9) ) ),
    inference(resolution,[status(thm)],[c_2,c_12])).

tff(c_6,plain,(
    k3_relat_1(k2_wellord1('#skF_2',k1_wellord1('#skF_2','#skF_1'))) != k1_wellord1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_26,plain,
    ( ~ v2_wellord1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_17,c_6])).

tff(c_37,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_8,c_26])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:02:06 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.59/1.09  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.59/1.09  
% 1.59/1.09  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.59/1.09  %$ r1_tarski > v2_wellord1 > v1_relat_1 > k2_wellord1 > k1_wellord1 > #nlpp > k3_relat_1 > #skF_2 > #skF_1
% 1.59/1.09  
% 1.59/1.09  %Foreground sorts:
% 1.59/1.09  
% 1.59/1.09  
% 1.59/1.09  %Background operators:
% 1.59/1.09  
% 1.59/1.09  
% 1.59/1.09  %Foreground operators:
% 1.59/1.09  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.59/1.09  tff(k3_relat_1, type, k3_relat_1: $i > $i).
% 1.59/1.09  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.59/1.09  tff(v2_wellord1, type, v2_wellord1: $i > $o).
% 1.59/1.09  tff('#skF_2', type, '#skF_2': $i).
% 1.59/1.09  tff('#skF_1', type, '#skF_1': $i).
% 1.59/1.09  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.59/1.09  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.59/1.09  tff(k1_wellord1, type, k1_wellord1: ($i * $i) > $i).
% 1.59/1.09  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.59/1.09  tff(k2_wellord1, type, k2_wellord1: ($i * $i) > $i).
% 1.59/1.09  
% 1.59/1.10  tff(f_44, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (v2_wellord1(B) => (k3_relat_1(k2_wellord1(B, k1_wellord1(B, A))) = k1_wellord1(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t40_wellord1)).
% 1.59/1.10  tff(f_29, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k1_wellord1(B, A), k3_relat_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t13_wellord1)).
% 1.59/1.10  tff(f_37, axiom, (![A, B]: (v1_relat_1(B) => ((v2_wellord1(B) & r1_tarski(A, k3_relat_1(B))) => (k3_relat_1(k2_wellord1(B, A)) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_wellord1)).
% 1.59/1.10  tff(c_10, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.59/1.10  tff(c_8, plain, (v2_wellord1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.59/1.10  tff(c_2, plain, (![B_2, A_1]: (r1_tarski(k1_wellord1(B_2, A_1), k3_relat_1(B_2)) | ~v1_relat_1(B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.59/1.10  tff(c_12, plain, (![B_7, A_8]: (k3_relat_1(k2_wellord1(B_7, A_8))=A_8 | ~r1_tarski(A_8, k3_relat_1(B_7)) | ~v2_wellord1(B_7) | ~v1_relat_1(B_7))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.59/1.10  tff(c_17, plain, (![B_9, A_10]: (k3_relat_1(k2_wellord1(B_9, k1_wellord1(B_9, A_10)))=k1_wellord1(B_9, A_10) | ~v2_wellord1(B_9) | ~v1_relat_1(B_9))), inference(resolution, [status(thm)], [c_2, c_12])).
% 1.59/1.10  tff(c_6, plain, (k3_relat_1(k2_wellord1('#skF_2', k1_wellord1('#skF_2', '#skF_1')))!=k1_wellord1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.59/1.10  tff(c_26, plain, (~v2_wellord1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_17, c_6])).
% 1.59/1.10  tff(c_37, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_10, c_8, c_26])).
% 1.59/1.10  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.59/1.10  
% 1.59/1.10  Inference rules
% 1.59/1.10  ----------------------
% 1.59/1.10  #Ref     : 0
% 1.59/1.10  #Sup     : 6
% 1.59/1.10  #Fact    : 0
% 1.59/1.10  #Define  : 0
% 1.59/1.10  #Split   : 0
% 1.59/1.10  #Chain   : 0
% 1.59/1.10  #Close   : 0
% 1.59/1.10  
% 1.59/1.10  Ordering : KBO
% 1.59/1.10  
% 1.59/1.10  Simplification rules
% 1.59/1.10  ----------------------
% 1.59/1.10  #Subsume      : 0
% 1.59/1.10  #Demod        : 2
% 1.59/1.10  #Tautology    : 1
% 1.59/1.10  #SimpNegUnit  : 0
% 1.59/1.10  #BackRed      : 0
% 1.59/1.10  
% 1.59/1.10  #Partial instantiations: 0
% 1.59/1.10  #Strategies tried      : 1
% 1.59/1.10  
% 1.59/1.10  Timing (in seconds)
% 1.59/1.10  ----------------------
% 1.59/1.10  Preprocessing        : 0.25
% 1.59/1.10  Parsing              : 0.13
% 1.59/1.10  CNF conversion       : 0.01
% 1.59/1.10  Main loop            : 0.08
% 1.59/1.10  Inferencing          : 0.04
% 1.59/1.10  Reduction            : 0.02
% 1.59/1.10  Demodulation         : 0.02
% 1.59/1.10  BG Simplification    : 0.01
% 1.59/1.10  Subsumption          : 0.01
% 1.59/1.10  Abstraction          : 0.00
% 1.59/1.10  MUC search           : 0.00
% 1.59/1.11  Cooper               : 0.00
% 1.59/1.11  Total                : 0.35
% 1.59/1.11  Index Insertion      : 0.00
% 1.59/1.11  Index Deletion       : 0.00
% 1.59/1.11  Index Matching       : 0.00
% 1.59/1.11  BG Taut test         : 0.00
%------------------------------------------------------------------------------

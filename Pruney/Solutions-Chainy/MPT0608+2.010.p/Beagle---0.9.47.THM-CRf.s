%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:30 EST 2020

% Result     : Theorem 1.65s
% Output     : CNFRefutation 1.90s
% Verified   : 
% Statistics : Number of formulae       :   26 (  27 expanded)
%              Number of leaves         :   15 (  16 expanded)
%              Depth                    :    6
%              Number of atoms          :   33 (  35 expanded)
%              Number of equality atoms :   12 (  13 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k7_relat_1 > k6_subset_1 > #nlpp > k1_relat_1 > #skF_2 > #skF_1

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_50,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => k1_relat_1(k6_subset_1(B,k7_relat_1(B,A))) = k6_subset_1(k1_relat_1(B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t212_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_45,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k7_relat_1(B,A) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_relat_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k7_relat_1(C,k6_subset_1(A,B)) = k6_subset_1(k7_relat_1(C,A),k7_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t109_relat_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k1_relat_1(k7_relat_1(B,k6_subset_1(k1_relat_1(B),A))) = k6_subset_1(k1_relat_1(B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t191_relat_1)).

tff(c_16,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_26,plain,(
    ! [B_13,A_14] :
      ( k7_relat_1(B_13,A_14) = B_13
      | ~ r1_tarski(k1_relat_1(B_13),A_14)
      | ~ v1_relat_1(B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_31,plain,(
    ! [B_13] :
      ( k7_relat_1(B_13,k1_relat_1(B_13)) = B_13
      | ~ v1_relat_1(B_13) ) ),
    inference(resolution,[status(thm)],[c_6,c_26])).

tff(c_62,plain,(
    ! [C_18,A_19,B_20] :
      ( k6_subset_1(k7_relat_1(C_18,A_19),k7_relat_1(C_18,B_20)) = k7_relat_1(C_18,k6_subset_1(A_19,B_20))
      | ~ v1_relat_1(C_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_77,plain,(
    ! [B_21,B_22] :
      ( k7_relat_1(B_21,k6_subset_1(k1_relat_1(B_21),B_22)) = k6_subset_1(B_21,k7_relat_1(B_21,B_22))
      | ~ v1_relat_1(B_21)
      | ~ v1_relat_1(B_21) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_31,c_62])).

tff(c_10,plain,(
    ! [B_7,A_6] :
      ( k1_relat_1(k7_relat_1(B_7,k6_subset_1(k1_relat_1(B_7),A_6))) = k6_subset_1(k1_relat_1(B_7),A_6)
      | ~ v1_relat_1(B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_128,plain,(
    ! [B_25,B_26] :
      ( k1_relat_1(k6_subset_1(B_25,k7_relat_1(B_25,B_26))) = k6_subset_1(k1_relat_1(B_25),B_26)
      | ~ v1_relat_1(B_25)
      | ~ v1_relat_1(B_25)
      | ~ v1_relat_1(B_25) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_77,c_10])).

tff(c_14,plain,(
    k1_relat_1(k6_subset_1('#skF_2',k7_relat_1('#skF_2','#skF_1'))) != k6_subset_1(k1_relat_1('#skF_2'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_149,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_128,c_14])).

tff(c_166,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_149])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:46:53 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.65/1.17  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.65/1.17  
% 1.65/1.17  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.65/1.17  %$ r1_tarski > v1_relat_1 > k7_relat_1 > k6_subset_1 > #nlpp > k1_relat_1 > #skF_2 > #skF_1
% 1.65/1.17  
% 1.65/1.17  %Foreground sorts:
% 1.65/1.17  
% 1.65/1.17  
% 1.65/1.17  %Background operators:
% 1.65/1.17  
% 1.65/1.17  
% 1.65/1.17  %Foreground operators:
% 1.65/1.17  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.65/1.17  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 1.65/1.17  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.65/1.17  tff('#skF_2', type, '#skF_2': $i).
% 1.65/1.17  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 1.65/1.17  tff('#skF_1', type, '#skF_1': $i).
% 1.65/1.17  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.65/1.17  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.65/1.17  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.65/1.17  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.65/1.17  
% 1.90/1.18  tff(f_50, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (k1_relat_1(k6_subset_1(B, k7_relat_1(B, A))) = k6_subset_1(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t212_relat_1)).
% 1.90/1.18  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 1.90/1.18  tff(f_45, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k7_relat_1(B, A) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t97_relat_1)).
% 1.90/1.18  tff(f_35, axiom, (![A, B, C]: (v1_relat_1(C) => (k7_relat_1(C, k6_subset_1(A, B)) = k6_subset_1(k7_relat_1(C, A), k7_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t109_relat_1)).
% 1.90/1.18  tff(f_39, axiom, (![A, B]: (v1_relat_1(B) => (k1_relat_1(k7_relat_1(B, k6_subset_1(k1_relat_1(B), A))) = k6_subset_1(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t191_relat_1)).
% 1.90/1.18  tff(c_16, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.90/1.18  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.90/1.18  tff(c_26, plain, (![B_13, A_14]: (k7_relat_1(B_13, A_14)=B_13 | ~r1_tarski(k1_relat_1(B_13), A_14) | ~v1_relat_1(B_13))), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.90/1.18  tff(c_31, plain, (![B_13]: (k7_relat_1(B_13, k1_relat_1(B_13))=B_13 | ~v1_relat_1(B_13))), inference(resolution, [status(thm)], [c_6, c_26])).
% 1.90/1.18  tff(c_62, plain, (![C_18, A_19, B_20]: (k6_subset_1(k7_relat_1(C_18, A_19), k7_relat_1(C_18, B_20))=k7_relat_1(C_18, k6_subset_1(A_19, B_20)) | ~v1_relat_1(C_18))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.90/1.18  tff(c_77, plain, (![B_21, B_22]: (k7_relat_1(B_21, k6_subset_1(k1_relat_1(B_21), B_22))=k6_subset_1(B_21, k7_relat_1(B_21, B_22)) | ~v1_relat_1(B_21) | ~v1_relat_1(B_21))), inference(superposition, [status(thm), theory('equality')], [c_31, c_62])).
% 1.90/1.18  tff(c_10, plain, (![B_7, A_6]: (k1_relat_1(k7_relat_1(B_7, k6_subset_1(k1_relat_1(B_7), A_6)))=k6_subset_1(k1_relat_1(B_7), A_6) | ~v1_relat_1(B_7))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.90/1.18  tff(c_128, plain, (![B_25, B_26]: (k1_relat_1(k6_subset_1(B_25, k7_relat_1(B_25, B_26)))=k6_subset_1(k1_relat_1(B_25), B_26) | ~v1_relat_1(B_25) | ~v1_relat_1(B_25) | ~v1_relat_1(B_25))), inference(superposition, [status(thm), theory('equality')], [c_77, c_10])).
% 1.90/1.18  tff(c_14, plain, (k1_relat_1(k6_subset_1('#skF_2', k7_relat_1('#skF_2', '#skF_1')))!=k6_subset_1(k1_relat_1('#skF_2'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.90/1.18  tff(c_149, plain, (~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_128, c_14])).
% 1.90/1.18  tff(c_166, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_16, c_149])).
% 1.90/1.18  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.90/1.18  
% 1.90/1.18  Inference rules
% 1.90/1.18  ----------------------
% 1.90/1.18  #Ref     : 0
% 1.90/1.18  #Sup     : 39
% 1.90/1.18  #Fact    : 0
% 1.90/1.18  #Define  : 0
% 1.90/1.18  #Split   : 0
% 1.90/1.18  #Chain   : 0
% 1.90/1.18  #Close   : 0
% 1.90/1.18  
% 1.90/1.18  Ordering : KBO
% 1.90/1.18  
% 1.90/1.18  Simplification rules
% 1.90/1.18  ----------------------
% 1.90/1.18  #Subsume      : 0
% 1.90/1.18  #Demod        : 3
% 1.90/1.18  #Tautology    : 13
% 1.90/1.18  #SimpNegUnit  : 0
% 1.90/1.18  #BackRed      : 0
% 1.90/1.18  
% 1.90/1.18  #Partial instantiations: 0
% 1.90/1.18  #Strategies tried      : 1
% 1.90/1.18  
% 1.90/1.18  Timing (in seconds)
% 1.90/1.18  ----------------------
% 1.90/1.19  Preprocessing        : 0.26
% 1.90/1.19  Parsing              : 0.14
% 1.90/1.19  CNF conversion       : 0.02
% 1.90/1.19  Main loop            : 0.15
% 1.90/1.19  Inferencing          : 0.07
% 1.90/1.19  Reduction            : 0.04
% 1.90/1.19  Demodulation         : 0.03
% 1.90/1.19  BG Simplification    : 0.01
% 1.90/1.19  Subsumption          : 0.03
% 1.90/1.19  Abstraction          : 0.01
% 1.90/1.19  MUC search           : 0.00
% 1.90/1.19  Cooper               : 0.00
% 1.90/1.19  Total                : 0.43
% 1.90/1.19  Index Insertion      : 0.00
% 1.90/1.19  Index Deletion       : 0.00
% 1.90/1.19  Index Matching       : 0.00
% 1.90/1.19  BG Taut test         : 0.00
%------------------------------------------------------------------------------

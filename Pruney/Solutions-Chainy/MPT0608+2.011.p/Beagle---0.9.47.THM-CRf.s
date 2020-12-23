%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:30 EST 2020

% Result     : Theorem 1.82s
% Output     : CNFRefutation 1.82s
% Verified   : 
% Statistics : Number of formulae       :   23 (  24 expanded)
%              Number of leaves         :   14 (  15 expanded)
%              Depth                    :    5
%              Number of atoms          :   25 (  27 expanded)
%              Number of equality atoms :    9 (  10 expanded)
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

tff(f_46,negated_conjecture,(
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

tff(f_41,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_tarski(k1_relat_1(C),A)
       => k6_subset_1(C,k7_relat_1(C,B)) = k7_relat_1(C,k6_subset_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t211_relat_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k1_relat_1(k7_relat_1(B,k6_subset_1(k1_relat_1(B),A))) = k6_subset_1(k1_relat_1(B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t191_relat_1)).

tff(c_14,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_39,plain,(
    ! [C_13,A_14,B_15] :
      ( k7_relat_1(C_13,k6_subset_1(A_14,B_15)) = k6_subset_1(C_13,k7_relat_1(C_13,B_15))
      | ~ r1_tarski(k1_relat_1(C_13),A_14)
      | ~ v1_relat_1(C_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_46,plain,(
    ! [C_16,B_17] :
      ( k7_relat_1(C_16,k6_subset_1(k1_relat_1(C_16),B_17)) = k6_subset_1(C_16,k7_relat_1(C_16,B_17))
      | ~ v1_relat_1(C_16) ) ),
    inference(resolution,[status(thm)],[c_6,c_39])).

tff(c_8,plain,(
    ! [B_4,A_3] :
      ( k1_relat_1(k7_relat_1(B_4,k6_subset_1(k1_relat_1(B_4),A_3))) = k6_subset_1(k1_relat_1(B_4),A_3)
      | ~ v1_relat_1(B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_61,plain,(
    ! [C_18,B_19] :
      ( k1_relat_1(k6_subset_1(C_18,k7_relat_1(C_18,B_19))) = k6_subset_1(k1_relat_1(C_18),B_19)
      | ~ v1_relat_1(C_18)
      | ~ v1_relat_1(C_18) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_8])).

tff(c_12,plain,(
    k1_relat_1(k6_subset_1('#skF_2',k7_relat_1('#skF_2','#skF_1'))) != k6_subset_1(k1_relat_1('#skF_2'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_75,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_61,c_12])).

tff(c_86,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_75])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:53:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.82/1.21  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.82/1.22  
% 1.82/1.22  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.82/1.22  %$ r1_tarski > v1_relat_1 > k7_relat_1 > k6_subset_1 > #nlpp > k1_relat_1 > #skF_2 > #skF_1
% 1.82/1.22  
% 1.82/1.22  %Foreground sorts:
% 1.82/1.22  
% 1.82/1.22  
% 1.82/1.22  %Background operators:
% 1.82/1.22  
% 1.82/1.22  
% 1.82/1.22  %Foreground operators:
% 1.82/1.22  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.82/1.22  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 1.82/1.22  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.82/1.22  tff('#skF_2', type, '#skF_2': $i).
% 1.82/1.22  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 1.82/1.22  tff('#skF_1', type, '#skF_1': $i).
% 1.82/1.22  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.82/1.22  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.82/1.22  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.82/1.22  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.82/1.22  
% 1.82/1.23  tff(f_46, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (k1_relat_1(k6_subset_1(B, k7_relat_1(B, A))) = k6_subset_1(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t212_relat_1)).
% 1.82/1.23  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 1.82/1.23  tff(f_41, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_tarski(k1_relat_1(C), A) => (k6_subset_1(C, k7_relat_1(C, B)) = k7_relat_1(C, k6_subset_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t211_relat_1)).
% 1.82/1.23  tff(f_35, axiom, (![A, B]: (v1_relat_1(B) => (k1_relat_1(k7_relat_1(B, k6_subset_1(k1_relat_1(B), A))) = k6_subset_1(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t191_relat_1)).
% 1.82/1.23  tff(c_14, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.82/1.23  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.82/1.23  tff(c_39, plain, (![C_13, A_14, B_15]: (k7_relat_1(C_13, k6_subset_1(A_14, B_15))=k6_subset_1(C_13, k7_relat_1(C_13, B_15)) | ~r1_tarski(k1_relat_1(C_13), A_14) | ~v1_relat_1(C_13))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.82/1.23  tff(c_46, plain, (![C_16, B_17]: (k7_relat_1(C_16, k6_subset_1(k1_relat_1(C_16), B_17))=k6_subset_1(C_16, k7_relat_1(C_16, B_17)) | ~v1_relat_1(C_16))), inference(resolution, [status(thm)], [c_6, c_39])).
% 1.82/1.23  tff(c_8, plain, (![B_4, A_3]: (k1_relat_1(k7_relat_1(B_4, k6_subset_1(k1_relat_1(B_4), A_3)))=k6_subset_1(k1_relat_1(B_4), A_3) | ~v1_relat_1(B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.82/1.23  tff(c_61, plain, (![C_18, B_19]: (k1_relat_1(k6_subset_1(C_18, k7_relat_1(C_18, B_19)))=k6_subset_1(k1_relat_1(C_18), B_19) | ~v1_relat_1(C_18) | ~v1_relat_1(C_18))), inference(superposition, [status(thm), theory('equality')], [c_46, c_8])).
% 1.82/1.23  tff(c_12, plain, (k1_relat_1(k6_subset_1('#skF_2', k7_relat_1('#skF_2', '#skF_1')))!=k6_subset_1(k1_relat_1('#skF_2'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.82/1.23  tff(c_75, plain, (~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_61, c_12])).
% 1.82/1.23  tff(c_86, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_14, c_75])).
% 1.82/1.23  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.82/1.23  
% 1.82/1.23  Inference rules
% 1.82/1.23  ----------------------
% 1.82/1.23  #Ref     : 0
% 1.82/1.23  #Sup     : 18
% 1.82/1.23  #Fact    : 0
% 1.82/1.23  #Define  : 0
% 1.82/1.23  #Split   : 0
% 1.82/1.23  #Chain   : 0
% 1.82/1.23  #Close   : 0
% 1.82/1.23  
% 1.82/1.23  Ordering : KBO
% 1.82/1.23  
% 1.82/1.23  Simplification rules
% 1.82/1.23  ----------------------
% 1.82/1.23  #Subsume      : 0
% 1.82/1.23  #Demod        : 3
% 1.82/1.23  #Tautology    : 7
% 1.82/1.23  #SimpNegUnit  : 0
% 1.82/1.23  #BackRed      : 0
% 1.82/1.23  
% 1.82/1.23  #Partial instantiations: 0
% 1.82/1.23  #Strategies tried      : 1
% 1.82/1.23  
% 1.82/1.23  Timing (in seconds)
% 1.82/1.23  ----------------------
% 1.82/1.23  Preprocessing        : 0.29
% 1.82/1.23  Parsing              : 0.16
% 1.82/1.23  CNF conversion       : 0.02
% 1.82/1.23  Main loop            : 0.11
% 1.82/1.23  Inferencing          : 0.05
% 1.82/1.23  Reduction            : 0.03
% 1.82/1.23  Demodulation         : 0.02
% 1.82/1.23  BG Simplification    : 0.01
% 1.82/1.23  Subsumption          : 0.02
% 1.82/1.23  Abstraction          : 0.01
% 1.82/1.23  MUC search           : 0.00
% 1.82/1.23  Cooper               : 0.00
% 1.82/1.23  Total                : 0.43
% 1.82/1.23  Index Insertion      : 0.00
% 1.82/1.23  Index Deletion       : 0.00
% 1.82/1.23  Index Matching       : 0.00
% 1.82/1.23  BG Taut test         : 0.00
%------------------------------------------------------------------------------

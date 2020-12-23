%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:12 EST 2020

% Result     : Theorem 1.49s
% Output     : CNFRefutation 1.60s
% Verified   : 
% Statistics : Number of formulae       :   23 (  27 expanded)
%              Number of leaves         :   12 (  16 expanded)
%              Depth                    :    6
%              Number of atoms          :   21 (  35 expanded)
%              Number of equality atoms :   11 (  18 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_relat_1 > k9_relat_1 > k7_relat_1 > #nlpp > k2_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(f_39,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ! [C] :
            ( v1_relat_1(C)
           => ( k7_relat_1(B,A) = k7_relat_1(C,A)
             => k9_relat_1(B,A) = k9_relat_1(C,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t201_relat_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

tff(c_4,plain,(
    k9_relat_1('#skF_2','#skF_1') != k9_relat_1('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_8,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_10,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_6,plain,(
    k7_relat_1('#skF_2','#skF_1') = k7_relat_1('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_15,plain,(
    ! [B_4,A_5] :
      ( k2_relat_1(k7_relat_1(B_4,A_5)) = k9_relat_1(B_4,A_5)
      | ~ v1_relat_1(B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_24,plain,
    ( k2_relat_1(k7_relat_1('#skF_3','#skF_1')) = k9_relat_1('#skF_2','#skF_1')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_15])).

tff(c_28,plain,(
    k2_relat_1(k7_relat_1('#skF_3','#skF_1')) = k9_relat_1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_24])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( k2_relat_1(k7_relat_1(B_2,A_1)) = k9_relat_1(B_2,A_1)
      | ~ v1_relat_1(B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_32,plain,
    ( k9_relat_1('#skF_2','#skF_1') = k9_relat_1('#skF_3','#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_2])).

tff(c_39,plain,(
    k9_relat_1('#skF_2','#skF_1') = k9_relat_1('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_32])).

tff(c_41,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4,c_39])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:17:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.49/1.09  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.49/1.09  
% 1.49/1.09  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.49/1.09  %$ v1_relat_1 > k9_relat_1 > k7_relat_1 > #nlpp > k2_relat_1 > #skF_2 > #skF_3 > #skF_1
% 1.49/1.09  
% 1.49/1.09  %Foreground sorts:
% 1.49/1.09  
% 1.49/1.09  
% 1.49/1.09  %Background operators:
% 1.49/1.09  
% 1.49/1.09  
% 1.49/1.09  %Foreground operators:
% 1.49/1.09  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.49/1.09  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 1.49/1.09  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.49/1.09  tff('#skF_2', type, '#skF_2': $i).
% 1.49/1.09  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 1.49/1.09  tff('#skF_3', type, '#skF_3': $i).
% 1.49/1.09  tff('#skF_1', type, '#skF_1': $i).
% 1.49/1.09  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.49/1.09  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.49/1.09  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.49/1.09  
% 1.60/1.10  tff(f_39, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => ((k7_relat_1(B, A) = k7_relat_1(C, A)) => (k9_relat_1(B, A) = k9_relat_1(C, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t201_relat_1)).
% 1.60/1.10  tff(f_29, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 1.60/1.10  tff(c_4, plain, (k9_relat_1('#skF_2', '#skF_1')!=k9_relat_1('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.60/1.10  tff(c_8, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.60/1.10  tff(c_10, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.60/1.10  tff(c_6, plain, (k7_relat_1('#skF_2', '#skF_1')=k7_relat_1('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.60/1.10  tff(c_15, plain, (![B_4, A_5]: (k2_relat_1(k7_relat_1(B_4, A_5))=k9_relat_1(B_4, A_5) | ~v1_relat_1(B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.60/1.10  tff(c_24, plain, (k2_relat_1(k7_relat_1('#skF_3', '#skF_1'))=k9_relat_1('#skF_2', '#skF_1') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_6, c_15])).
% 1.60/1.10  tff(c_28, plain, (k2_relat_1(k7_relat_1('#skF_3', '#skF_1'))=k9_relat_1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_10, c_24])).
% 1.60/1.10  tff(c_2, plain, (![B_2, A_1]: (k2_relat_1(k7_relat_1(B_2, A_1))=k9_relat_1(B_2, A_1) | ~v1_relat_1(B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.60/1.10  tff(c_32, plain, (k9_relat_1('#skF_2', '#skF_1')=k9_relat_1('#skF_3', '#skF_1') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_28, c_2])).
% 1.60/1.10  tff(c_39, plain, (k9_relat_1('#skF_2', '#skF_1')=k9_relat_1('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_8, c_32])).
% 1.60/1.10  tff(c_41, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4, c_39])).
% 1.60/1.10  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.60/1.10  
% 1.60/1.10  Inference rules
% 1.60/1.10  ----------------------
% 1.60/1.10  #Ref     : 0
% 1.60/1.10  #Sup     : 9
% 1.60/1.10  #Fact    : 0
% 1.60/1.10  #Define  : 0
% 1.60/1.10  #Split   : 0
% 1.60/1.10  #Chain   : 0
% 1.60/1.10  #Close   : 0
% 1.60/1.10  
% 1.60/1.10  Ordering : KBO
% 1.60/1.10  
% 1.60/1.10  Simplification rules
% 1.60/1.10  ----------------------
% 1.60/1.10  #Subsume      : 0
% 1.60/1.10  #Demod        : 2
% 1.60/1.10  #Tautology    : 5
% 1.60/1.10  #SimpNegUnit  : 1
% 1.60/1.10  #BackRed      : 0
% 1.60/1.10  
% 1.60/1.10  #Partial instantiations: 0
% 1.60/1.10  #Strategies tried      : 1
% 1.60/1.10  
% 1.60/1.10  Timing (in seconds)
% 1.60/1.10  ----------------------
% 1.60/1.10  Preprocessing        : 0.25
% 1.60/1.11  Parsing              : 0.13
% 1.60/1.11  CNF conversion       : 0.01
% 1.60/1.11  Main loop            : 0.06
% 1.60/1.11  Inferencing          : 0.03
% 1.60/1.11  Reduction            : 0.02
% 1.60/1.11  Demodulation         : 0.01
% 1.60/1.11  BG Simplification    : 0.01
% 1.60/1.11  Subsumption          : 0.01
% 1.60/1.11  Abstraction          : 0.00
% 1.60/1.11  MUC search           : 0.00
% 1.60/1.11  Cooper               : 0.00
% 1.60/1.11  Total                : 0.34
% 1.60/1.11  Index Insertion      : 0.00
% 1.60/1.11  Index Deletion       : 0.00
% 1.60/1.11  Index Matching       : 0.00
% 1.60/1.11  BG Taut test         : 0.00
%------------------------------------------------------------------------------

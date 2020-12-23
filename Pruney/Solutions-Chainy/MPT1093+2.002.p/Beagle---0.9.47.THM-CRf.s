%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:18:26 EST 2020

% Result     : Theorem 1.61s
% Output     : CNFRefutation 1.61s
% Verified   : 
% Statistics : Number of formulae       :   27 (  35 expanded)
%              Number of leaves         :   15 (  21 expanded)
%              Depth                    :    6
%              Number of atoms          :   36 (  68 expanded)
%              Number of equality atoms :    4 (   4 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > v1_funct_1 > v1_finset_1 > k9_relat_1 > k10_relat_1 > #nlpp > k2_relat_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_finset_1,type,(
    v1_finset_1: $i > $o )).

tff(f_52,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_relat_1(B)
          & v1_funct_1(B) )
       => ( ( r1_tarski(A,k2_relat_1(B))
            & v1_finset_1(k10_relat_1(B,A)) )
         => v1_finset_1(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_finset_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r1_tarski(A,k2_relat_1(B))
       => k9_relat_1(B,k10_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t147_funct_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A)
        & v1_finset_1(B) )
     => v1_finset_1(k9_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc13_finset_1)).

tff(c_6,plain,(
    ~ v1_finset_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_14,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_12,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_8,plain,(
    v1_finset_1(k10_relat_1('#skF_2','#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_10,plain,(
    r1_tarski('#skF_1',k2_relat_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_16,plain,(
    ! [B_7,A_8] :
      ( k9_relat_1(B_7,k10_relat_1(B_7,A_8)) = A_8
      | ~ r1_tarski(A_8,k2_relat_1(B_7))
      | ~ v1_funct_1(B_7)
      | ~ v1_relat_1(B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_18,plain,
    ( k9_relat_1('#skF_2',k10_relat_1('#skF_2','#skF_1')) = '#skF_1'
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_10,c_16])).

tff(c_21,plain,(
    k9_relat_1('#skF_2',k10_relat_1('#skF_2','#skF_1')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_12,c_18])).

tff(c_4,plain,(
    ! [A_3,B_4] :
      ( v1_finset_1(k9_relat_1(A_3,B_4))
      | ~ v1_finset_1(B_4)
      | ~ v1_funct_1(A_3)
      | ~ v1_relat_1(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_25,plain,
    ( v1_finset_1('#skF_1')
    | ~ v1_finset_1(k10_relat_1('#skF_2','#skF_1'))
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_21,c_4])).

tff(c_29,plain,(
    v1_finset_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_12,c_8,c_25])).

tff(c_31,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_6,c_29])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:51:24 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.61/1.10  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.61/1.11  
% 1.61/1.11  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.61/1.11  %$ r1_tarski > v1_relat_1 > v1_funct_1 > v1_finset_1 > k9_relat_1 > k10_relat_1 > #nlpp > k2_relat_1 > #skF_2 > #skF_1
% 1.61/1.11  
% 1.61/1.11  %Foreground sorts:
% 1.61/1.11  
% 1.61/1.11  
% 1.61/1.11  %Background operators:
% 1.61/1.11  
% 1.61/1.11  
% 1.61/1.11  %Foreground operators:
% 1.61/1.11  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.61/1.11  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.61/1.11  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.61/1.11  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.61/1.11  tff('#skF_2', type, '#skF_2': $i).
% 1.61/1.11  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 1.61/1.11  tff('#skF_1', type, '#skF_1': $i).
% 1.61/1.11  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.61/1.11  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 1.61/1.11  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.61/1.11  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.61/1.11  tff(v1_finset_1, type, v1_finset_1: $i > $o).
% 1.61/1.11  
% 1.61/1.12  tff(f_52, negated_conjecture, ~(![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((r1_tarski(A, k2_relat_1(B)) & v1_finset_1(k10_relat_1(B, A))) => v1_finset_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t27_finset_1)).
% 1.61/1.12  tff(f_33, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(A, k2_relat_1(B)) => (k9_relat_1(B, k10_relat_1(B, A)) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t147_funct_1)).
% 1.61/1.12  tff(f_41, axiom, (![A, B]: (((v1_relat_1(A) & v1_funct_1(A)) & v1_finset_1(B)) => v1_finset_1(k9_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc13_finset_1)).
% 1.61/1.12  tff(c_6, plain, (~v1_finset_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.61/1.12  tff(c_14, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.61/1.12  tff(c_12, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.61/1.12  tff(c_8, plain, (v1_finset_1(k10_relat_1('#skF_2', '#skF_1'))), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.61/1.12  tff(c_10, plain, (r1_tarski('#skF_1', k2_relat_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.61/1.12  tff(c_16, plain, (![B_7, A_8]: (k9_relat_1(B_7, k10_relat_1(B_7, A_8))=A_8 | ~r1_tarski(A_8, k2_relat_1(B_7)) | ~v1_funct_1(B_7) | ~v1_relat_1(B_7))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.61/1.12  tff(c_18, plain, (k9_relat_1('#skF_2', k10_relat_1('#skF_2', '#skF_1'))='#skF_1' | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_10, c_16])).
% 1.61/1.12  tff(c_21, plain, (k9_relat_1('#skF_2', k10_relat_1('#skF_2', '#skF_1'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_14, c_12, c_18])).
% 1.61/1.12  tff(c_4, plain, (![A_3, B_4]: (v1_finset_1(k9_relat_1(A_3, B_4)) | ~v1_finset_1(B_4) | ~v1_funct_1(A_3) | ~v1_relat_1(A_3))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.61/1.12  tff(c_25, plain, (v1_finset_1('#skF_1') | ~v1_finset_1(k10_relat_1('#skF_2', '#skF_1')) | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_21, c_4])).
% 1.61/1.12  tff(c_29, plain, (v1_finset_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_14, c_12, c_8, c_25])).
% 1.61/1.12  tff(c_31, plain, $false, inference(negUnitSimplification, [status(thm)], [c_6, c_29])).
% 1.61/1.12  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.61/1.12  
% 1.61/1.12  Inference rules
% 1.61/1.12  ----------------------
% 1.61/1.12  #Ref     : 0
% 1.61/1.12  #Sup     : 4
% 1.61/1.12  #Fact    : 0
% 1.61/1.12  #Define  : 0
% 1.61/1.12  #Split   : 0
% 1.61/1.12  #Chain   : 0
% 1.61/1.12  #Close   : 0
% 1.61/1.12  
% 1.61/1.12  Ordering : KBO
% 1.61/1.12  
% 1.61/1.12  Simplification rules
% 1.61/1.12  ----------------------
% 1.61/1.12  #Subsume      : 0
% 1.61/1.12  #Demod        : 5
% 1.61/1.12  #Tautology    : 1
% 1.61/1.12  #SimpNegUnit  : 1
% 1.61/1.12  #BackRed      : 0
% 1.61/1.12  
% 1.61/1.12  #Partial instantiations: 0
% 1.61/1.12  #Strategies tried      : 1
% 1.61/1.12  
% 1.61/1.12  Timing (in seconds)
% 1.61/1.12  ----------------------
% 1.61/1.12  Preprocessing        : 0.27
% 1.61/1.12  Parsing              : 0.15
% 1.61/1.12  CNF conversion       : 0.02
% 1.61/1.12  Main loop            : 0.09
% 1.61/1.12  Inferencing          : 0.05
% 1.61/1.12  Reduction            : 0.02
% 1.61/1.12  Demodulation         : 0.02
% 1.61/1.12  BG Simplification    : 0.01
% 1.61/1.12  Subsumption          : 0.01
% 1.61/1.12  Abstraction          : 0.00
% 1.61/1.12  MUC search           : 0.00
% 1.61/1.12  Cooper               : 0.00
% 1.61/1.12  Total                : 0.38
% 1.61/1.12  Index Insertion      : 0.00
% 1.61/1.12  Index Deletion       : 0.00
% 1.61/1.12  Index Matching       : 0.00
% 1.61/1.12  BG Taut test         : 0.00
%------------------------------------------------------------------------------

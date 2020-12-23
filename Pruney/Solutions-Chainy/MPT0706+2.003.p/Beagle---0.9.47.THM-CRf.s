%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:16 EST 2020

% Result     : Theorem 1.53s
% Output     : CNFRefutation 1.64s
% Verified   : 
% Statistics : Number of formulae       :   27 (  38 expanded)
%              Number of leaves         :   14 (  22 expanded)
%              Depth                    :    5
%              Number of atoms          :   30 (  82 expanded)
%              Number of equality atoms :   11 (  27 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > v1_funct_1 > k9_relat_1 > k10_relat_1 > #nlpp > k2_relat_1 > #skF_2 > #skF_3 > #skF_1

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

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff(f_46,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_relat_1(C)
          & v1_funct_1(C) )
       => ( ( k10_relat_1(C,A) = k10_relat_1(C,B)
            & r1_tarski(A,k2_relat_1(C))
            & r1_tarski(B,k2_relat_1(C)) )
         => A = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t161_funct_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r1_tarski(A,k2_relat_1(B))
       => k9_relat_1(B,k10_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t147_funct_1)).

tff(c_4,plain,(
    '#skF_2' != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_14,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_12,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_8,plain,(
    r1_tarski('#skF_1',k2_relat_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_19,plain,(
    ! [B_3,A_4] :
      ( k9_relat_1(B_3,k10_relat_1(B_3,A_4)) = A_4
      | ~ r1_tarski(A_4,k2_relat_1(B_3))
      | ~ v1_funct_1(B_3)
      | ~ v1_relat_1(B_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_21,plain,
    ( k9_relat_1('#skF_3',k10_relat_1('#skF_3','#skF_1')) = '#skF_1'
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_8,c_19])).

tff(c_26,plain,(
    k9_relat_1('#skF_3',k10_relat_1('#skF_3','#skF_1')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_12,c_21])).

tff(c_10,plain,(
    k10_relat_1('#skF_3','#skF_2') = k10_relat_1('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_6,plain,(
    r1_tarski('#skF_2',k2_relat_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_23,plain,
    ( k9_relat_1('#skF_3',k10_relat_1('#skF_3','#skF_2')) = '#skF_2'
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_6,c_19])).

tff(c_29,plain,(
    k9_relat_1('#skF_3',k10_relat_1('#skF_3','#skF_1')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_12,c_10,c_23])).

tff(c_34,plain,(
    '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_29])).

tff(c_35,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4,c_34])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:49:23 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.53/1.08  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.53/1.09  
% 1.53/1.09  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.53/1.09  %$ r1_tarski > v1_relat_1 > v1_funct_1 > k9_relat_1 > k10_relat_1 > #nlpp > k2_relat_1 > #skF_2 > #skF_3 > #skF_1
% 1.53/1.09  
% 1.53/1.09  %Foreground sorts:
% 1.53/1.09  
% 1.53/1.09  
% 1.53/1.09  %Background operators:
% 1.53/1.09  
% 1.53/1.09  
% 1.53/1.09  %Foreground operators:
% 1.53/1.09  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.53/1.09  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.53/1.09  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.53/1.09  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.53/1.09  tff('#skF_2', type, '#skF_2': $i).
% 1.53/1.09  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 1.53/1.09  tff('#skF_3', type, '#skF_3': $i).
% 1.53/1.09  tff('#skF_1', type, '#skF_1': $i).
% 1.53/1.09  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.53/1.09  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 1.53/1.09  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.53/1.09  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.53/1.09  
% 1.64/1.10  tff(f_46, negated_conjecture, ~(![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => ((((k10_relat_1(C, A) = k10_relat_1(C, B)) & r1_tarski(A, k2_relat_1(C))) & r1_tarski(B, k2_relat_1(C))) => (A = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t161_funct_1)).
% 1.64/1.10  tff(f_33, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(A, k2_relat_1(B)) => (k9_relat_1(B, k10_relat_1(B, A)) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t147_funct_1)).
% 1.64/1.10  tff(c_4, plain, ('#skF_2'!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.64/1.10  tff(c_14, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.64/1.10  tff(c_12, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.64/1.10  tff(c_8, plain, (r1_tarski('#skF_1', k2_relat_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.64/1.10  tff(c_19, plain, (![B_3, A_4]: (k9_relat_1(B_3, k10_relat_1(B_3, A_4))=A_4 | ~r1_tarski(A_4, k2_relat_1(B_3)) | ~v1_funct_1(B_3) | ~v1_relat_1(B_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.64/1.10  tff(c_21, plain, (k9_relat_1('#skF_3', k10_relat_1('#skF_3', '#skF_1'))='#skF_1' | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_8, c_19])).
% 1.64/1.10  tff(c_26, plain, (k9_relat_1('#skF_3', k10_relat_1('#skF_3', '#skF_1'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_14, c_12, c_21])).
% 1.64/1.10  tff(c_10, plain, (k10_relat_1('#skF_3', '#skF_2')=k10_relat_1('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.64/1.10  tff(c_6, plain, (r1_tarski('#skF_2', k2_relat_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.64/1.10  tff(c_23, plain, (k9_relat_1('#skF_3', k10_relat_1('#skF_3', '#skF_2'))='#skF_2' | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_6, c_19])).
% 1.64/1.10  tff(c_29, plain, (k9_relat_1('#skF_3', k10_relat_1('#skF_3', '#skF_1'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_14, c_12, c_10, c_23])).
% 1.64/1.10  tff(c_34, plain, ('#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_26, c_29])).
% 1.64/1.10  tff(c_35, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4, c_34])).
% 1.64/1.10  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.64/1.10  
% 1.64/1.10  Inference rules
% 1.64/1.10  ----------------------
% 1.64/1.10  #Ref     : 0
% 1.64/1.10  #Sup     : 6
% 1.64/1.10  #Fact    : 0
% 1.64/1.10  #Define  : 0
% 1.64/1.10  #Split   : 0
% 1.64/1.10  #Chain   : 0
% 1.64/1.10  #Close   : 0
% 1.64/1.10  
% 1.64/1.10  Ordering : KBO
% 1.64/1.10  
% 1.64/1.10  Simplification rules
% 1.64/1.10  ----------------------
% 1.64/1.10  #Subsume      : 0
% 1.64/1.10  #Demod        : 6
% 1.64/1.10  #Tautology    : 4
% 1.64/1.10  #SimpNegUnit  : 1
% 1.64/1.10  #BackRed      : 0
% 1.64/1.10  
% 1.64/1.10  #Partial instantiations: 0
% 1.64/1.10  #Strategies tried      : 1
% 1.64/1.10  
% 1.64/1.10  Timing (in seconds)
% 1.64/1.10  ----------------------
% 1.64/1.10  Preprocessing        : 0.25
% 1.64/1.10  Parsing              : 0.13
% 1.64/1.10  CNF conversion       : 0.01
% 1.64/1.10  Main loop            : 0.07
% 1.64/1.10  Inferencing          : 0.03
% 1.64/1.10  Reduction            : 0.02
% 1.64/1.10  Demodulation         : 0.02
% 1.64/1.10  BG Simplification    : 0.01
% 1.64/1.10  Subsumption          : 0.01
% 1.64/1.10  Abstraction          : 0.00
% 1.64/1.10  MUC search           : 0.00
% 1.64/1.10  Cooper               : 0.00
% 1.64/1.10  Total                : 0.34
% 1.64/1.10  Index Insertion      : 0.00
% 1.64/1.10  Index Deletion       : 0.00
% 1.64/1.10  Index Matching       : 0.00
% 1.64/1.10  BG Taut test         : 0.00
%------------------------------------------------------------------------------

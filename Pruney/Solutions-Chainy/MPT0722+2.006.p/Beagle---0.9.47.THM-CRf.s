%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:54 EST 2020

% Result     : Theorem 1.57s
% Output     : CNFRefutation 1.57s
% Verified   : 
% Statistics : Number of formulae       :   28 (  38 expanded)
%              Number of leaves         :   16 (  23 expanded)
%              Depth                    :    4
%              Number of atoms          :   39 (  77 expanded)
%              Number of equality atoms :   10 (  17 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k9_relat_1 > k10_relat_1 > #nlpp > k2_funct_1 > k1_relat_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(k2_funct_1,type,(
    k2_funct_1: $i > $i )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_55,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ! [B] :
            ( ( v2_funct_1(A)
              & r1_tarski(B,k1_relat_1(A)) )
           => k9_relat_1(k2_funct_1(A),k9_relat_1(A,B)) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t177_funct_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( v2_funct_1(B)
       => k10_relat_1(B,A) = k9_relat_1(k2_funct_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t155_funct_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( ( r1_tarski(A,k1_relat_1(B))
          & v2_funct_1(B) )
       => k10_relat_1(B,k9_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t164_funct_1)).

tff(c_14,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_12,plain,(
    v1_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_10,plain,(
    v2_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_15,plain,(
    ! [B_6,A_7] :
      ( k9_relat_1(k2_funct_1(B_6),A_7) = k10_relat_1(B_6,A_7)
      | ~ v2_funct_1(B_6)
      | ~ v1_funct_1(B_6)
      | ~ v1_relat_1(B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_6,plain,(
    k9_relat_1(k2_funct_1('#skF_1'),k9_relat_1('#skF_1','#skF_2')) != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_21,plain,
    ( k10_relat_1('#skF_1',k9_relat_1('#skF_1','#skF_2')) != '#skF_2'
    | ~ v2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_15,c_6])).

tff(c_27,plain,(
    k10_relat_1('#skF_1',k9_relat_1('#skF_1','#skF_2')) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_12,c_10,c_21])).

tff(c_8,plain,(
    r1_tarski('#skF_2',k1_relat_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_29,plain,(
    ! [B_8,A_9] :
      ( k10_relat_1(B_8,k9_relat_1(B_8,A_9)) = A_9
      | ~ v2_funct_1(B_8)
      | ~ r1_tarski(A_9,k1_relat_1(B_8))
      | ~ v1_funct_1(B_8)
      | ~ v1_relat_1(B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_31,plain,
    ( k10_relat_1('#skF_1',k9_relat_1('#skF_1','#skF_2')) = '#skF_2'
    | ~ v2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_8,c_29])).

tff(c_34,plain,(
    k10_relat_1('#skF_1',k9_relat_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_12,c_10,c_31])).

tff(c_36,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_27,c_34])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:02:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.57/1.17  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.57/1.18  
% 1.57/1.18  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.57/1.18  %$ r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k9_relat_1 > k10_relat_1 > #nlpp > k2_funct_1 > k1_relat_1 > #skF_2 > #skF_1
% 1.57/1.18  
% 1.57/1.18  %Foreground sorts:
% 1.57/1.18  
% 1.57/1.18  
% 1.57/1.18  %Background operators:
% 1.57/1.18  
% 1.57/1.18  
% 1.57/1.18  %Foreground operators:
% 1.57/1.18  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.57/1.18  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 1.57/1.18  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 1.57/1.18  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.57/1.18  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.57/1.18  tff('#skF_2', type, '#skF_2': $i).
% 1.57/1.18  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 1.57/1.18  tff('#skF_1', type, '#skF_1': $i).
% 1.57/1.18  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.57/1.18  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 1.57/1.18  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.57/1.18  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.57/1.18  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.57/1.18  
% 1.57/1.18  tff(f_55, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v2_funct_1(A) & r1_tarski(B, k1_relat_1(A))) => (k9_relat_1(k2_funct_1(A), k9_relat_1(A, B)) = B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t177_funct_1)).
% 1.57/1.18  tff(f_33, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (v2_funct_1(B) => (k10_relat_1(B, A) = k9_relat_1(k2_funct_1(B), A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t155_funct_1)).
% 1.57/1.18  tff(f_43, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((r1_tarski(A, k1_relat_1(B)) & v2_funct_1(B)) => (k10_relat_1(B, k9_relat_1(B, A)) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t164_funct_1)).
% 1.57/1.18  tff(c_14, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_55])).
% 1.57/1.18  tff(c_12, plain, (v1_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_55])).
% 1.57/1.18  tff(c_10, plain, (v2_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_55])).
% 1.57/1.18  tff(c_15, plain, (![B_6, A_7]: (k9_relat_1(k2_funct_1(B_6), A_7)=k10_relat_1(B_6, A_7) | ~v2_funct_1(B_6) | ~v1_funct_1(B_6) | ~v1_relat_1(B_6))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.57/1.18  tff(c_6, plain, (k9_relat_1(k2_funct_1('#skF_1'), k9_relat_1('#skF_1', '#skF_2'))!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_55])).
% 1.57/1.18  tff(c_21, plain, (k10_relat_1('#skF_1', k9_relat_1('#skF_1', '#skF_2'))!='#skF_2' | ~v2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_15, c_6])).
% 1.57/1.18  tff(c_27, plain, (k10_relat_1('#skF_1', k9_relat_1('#skF_1', '#skF_2'))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_14, c_12, c_10, c_21])).
% 1.57/1.18  tff(c_8, plain, (r1_tarski('#skF_2', k1_relat_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_55])).
% 1.57/1.18  tff(c_29, plain, (![B_8, A_9]: (k10_relat_1(B_8, k9_relat_1(B_8, A_9))=A_9 | ~v2_funct_1(B_8) | ~r1_tarski(A_9, k1_relat_1(B_8)) | ~v1_funct_1(B_8) | ~v1_relat_1(B_8))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.57/1.18  tff(c_31, plain, (k10_relat_1('#skF_1', k9_relat_1('#skF_1', '#skF_2'))='#skF_2' | ~v2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_8, c_29])).
% 1.57/1.18  tff(c_34, plain, (k10_relat_1('#skF_1', k9_relat_1('#skF_1', '#skF_2'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_14, c_12, c_10, c_31])).
% 1.57/1.18  tff(c_36, plain, $false, inference(negUnitSimplification, [status(thm)], [c_27, c_34])).
% 1.57/1.18  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.57/1.18  
% 1.57/1.18  Inference rules
% 1.57/1.18  ----------------------
% 1.57/1.18  #Ref     : 0
% 1.57/1.18  #Sup     : 4
% 1.57/1.19  #Fact    : 0
% 1.57/1.19  #Define  : 0
% 1.57/1.19  #Split   : 0
% 1.57/1.19  #Chain   : 0
% 1.57/1.19  #Close   : 0
% 1.57/1.19  
% 1.57/1.19  Ordering : KBO
% 1.57/1.19  
% 1.57/1.19  Simplification rules
% 1.57/1.19  ----------------------
% 1.57/1.19  #Subsume      : 0
% 1.57/1.19  #Demod        : 6
% 1.57/1.19  #Tautology    : 2
% 1.57/1.19  #SimpNegUnit  : 1
% 1.57/1.19  #BackRed      : 0
% 1.57/1.19  
% 1.57/1.19  #Partial instantiations: 0
% 1.57/1.19  #Strategies tried      : 1
% 1.57/1.19  
% 1.57/1.19  Timing (in seconds)
% 1.57/1.19  ----------------------
% 1.75/1.19  Preprocessing        : 0.27
% 1.75/1.19  Parsing              : 0.16
% 1.75/1.19  CNF conversion       : 0.02
% 1.75/1.19  Main loop            : 0.08
% 1.75/1.19  Inferencing          : 0.04
% 1.75/1.19  Reduction            : 0.02
% 1.75/1.19  Demodulation         : 0.02
% 1.75/1.19  BG Simplification    : 0.01
% 1.75/1.19  Subsumption          : 0.01
% 1.75/1.19  Abstraction          : 0.00
% 1.75/1.19  MUC search           : 0.00
% 1.75/1.19  Cooper               : 0.00
% 1.75/1.19  Total                : 0.37
% 1.75/1.19  Index Insertion      : 0.00
% 1.75/1.19  Index Deletion       : 0.00
% 1.75/1.19  Index Matching       : 0.00
% 1.75/1.19  BG Taut test         : 0.00
%------------------------------------------------------------------------------

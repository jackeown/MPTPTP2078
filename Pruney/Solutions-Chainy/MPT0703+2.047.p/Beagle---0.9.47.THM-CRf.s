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
% DateTime   : Thu Dec  3 10:05:15 EST 2020

% Result     : Theorem 2.02s
% Output     : CNFRefutation 2.02s
% Verified   : 
% Statistics : Number of formulae       :   35 (  45 expanded)
%              Number of leaves         :   17 (  24 expanded)
%              Depth                    :    9
%              Number of atoms          :   55 (  93 expanded)
%              Number of equality atoms :    4 (   4 expanded)
%              Maximal formula depth    :    8 (   4 average)
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

tff(f_62,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_relat_1(C)
          & v1_funct_1(C) )
       => ( ( r1_tarski(k10_relat_1(C,A),k10_relat_1(C,B))
            & r1_tarski(A,k2_relat_1(C)) )
         => r1_tarski(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t158_funct_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r1_tarski(A,k2_relat_1(B))
       => k9_relat_1(B,k10_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t147_funct_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_tarski(A,B)
       => r1_tarski(k9_relat_1(C,A),k9_relat_1(C,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t156_relat_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => r1_tarski(k9_relat_1(B,k10_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t145_funct_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(c_10,plain,(
    ~ r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_18,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_16,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_14,plain,(
    r1_tarski(k10_relat_1('#skF_3','#skF_1'),k10_relat_1('#skF_3','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_12,plain,(
    r1_tarski('#skF_1',k2_relat_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_84,plain,(
    ! [B_25,A_26] :
      ( k9_relat_1(B_25,k10_relat_1(B_25,A_26)) = A_26
      | ~ r1_tarski(A_26,k2_relat_1(B_25))
      | ~ v1_funct_1(B_25)
      | ~ v1_relat_1(B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_91,plain,
    ( k9_relat_1('#skF_3',k10_relat_1('#skF_3','#skF_1')) = '#skF_1'
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_12,c_84])).

tff(c_98,plain,(
    k9_relat_1('#skF_3',k10_relat_1('#skF_3','#skF_1')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_16,c_91])).

tff(c_4,plain,(
    ! [C_6,A_4,B_5] :
      ( r1_tarski(k9_relat_1(C_6,A_4),k9_relat_1(C_6,B_5))
      | ~ r1_tarski(A_4,B_5)
      | ~ v1_relat_1(C_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_102,plain,(
    ! [B_5] :
      ( r1_tarski('#skF_1',k9_relat_1('#skF_3',B_5))
      | ~ r1_tarski(k10_relat_1('#skF_3','#skF_1'),B_5)
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_98,c_4])).

tff(c_196,plain,(
    ! [B_30] :
      ( r1_tarski('#skF_1',k9_relat_1('#skF_3',B_30))
      | ~ r1_tarski(k10_relat_1('#skF_3','#skF_1'),B_30) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_102])).

tff(c_210,plain,(
    r1_tarski('#skF_1',k9_relat_1('#skF_3',k10_relat_1('#skF_3','#skF_2'))) ),
    inference(resolution,[status(thm)],[c_14,c_196])).

tff(c_49,plain,(
    ! [B_18,A_19] :
      ( r1_tarski(k9_relat_1(B_18,k10_relat_1(B_18,A_19)),A_19)
      | ~ v1_funct_1(B_18)
      | ~ v1_relat_1(B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_2,plain,(
    ! [A_1,C_3,B_2] :
      ( r1_tarski(A_1,C_3)
      | ~ r1_tarski(B_2,C_3)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_225,plain,(
    ! [A_31,A_32,B_33] :
      ( r1_tarski(A_31,A_32)
      | ~ r1_tarski(A_31,k9_relat_1(B_33,k10_relat_1(B_33,A_32)))
      | ~ v1_funct_1(B_33)
      | ~ v1_relat_1(B_33) ) ),
    inference(resolution,[status(thm)],[c_49,c_2])).

tff(c_228,plain,
    ( r1_tarski('#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_210,c_225])).

tff(c_245,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_16,c_228])).

tff(c_247,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_10,c_245])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:53:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.02/1.26  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.02/1.26  
% 2.02/1.26  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.02/1.26  %$ r1_tarski > v1_relat_1 > v1_funct_1 > k9_relat_1 > k10_relat_1 > #nlpp > k2_relat_1 > #skF_2 > #skF_3 > #skF_1
% 2.02/1.26  
% 2.02/1.26  %Foreground sorts:
% 2.02/1.26  
% 2.02/1.26  
% 2.02/1.26  %Background operators:
% 2.02/1.26  
% 2.02/1.26  
% 2.02/1.26  %Foreground operators:
% 2.02/1.26  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.02/1.26  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.02/1.26  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.02/1.26  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.02/1.26  tff('#skF_2', type, '#skF_2': $i).
% 2.02/1.26  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.02/1.26  tff('#skF_3', type, '#skF_3': $i).
% 2.02/1.26  tff('#skF_1', type, '#skF_1': $i).
% 2.02/1.26  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.02/1.26  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.02/1.26  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.02/1.26  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.02/1.26  
% 2.02/1.27  tff(f_62, negated_conjecture, ~(![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => ((r1_tarski(k10_relat_1(C, A), k10_relat_1(C, B)) & r1_tarski(A, k2_relat_1(C))) => r1_tarski(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t158_funct_1)).
% 2.02/1.27  tff(f_51, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(A, k2_relat_1(B)) => (k9_relat_1(B, k10_relat_1(B, A)) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t147_funct_1)).
% 2.02/1.27  tff(f_37, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => r1_tarski(k9_relat_1(C, A), k9_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t156_relat_1)).
% 2.02/1.27  tff(f_43, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => r1_tarski(k9_relat_1(B, k10_relat_1(B, A)), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t145_funct_1)).
% 2.02/1.27  tff(f_31, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 2.02/1.27  tff(c_10, plain, (~r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.02/1.27  tff(c_18, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.02/1.27  tff(c_16, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.02/1.27  tff(c_14, plain, (r1_tarski(k10_relat_1('#skF_3', '#skF_1'), k10_relat_1('#skF_3', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.02/1.27  tff(c_12, plain, (r1_tarski('#skF_1', k2_relat_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.02/1.27  tff(c_84, plain, (![B_25, A_26]: (k9_relat_1(B_25, k10_relat_1(B_25, A_26))=A_26 | ~r1_tarski(A_26, k2_relat_1(B_25)) | ~v1_funct_1(B_25) | ~v1_relat_1(B_25))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.02/1.27  tff(c_91, plain, (k9_relat_1('#skF_3', k10_relat_1('#skF_3', '#skF_1'))='#skF_1' | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_12, c_84])).
% 2.02/1.27  tff(c_98, plain, (k9_relat_1('#skF_3', k10_relat_1('#skF_3', '#skF_1'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_18, c_16, c_91])).
% 2.02/1.27  tff(c_4, plain, (![C_6, A_4, B_5]: (r1_tarski(k9_relat_1(C_6, A_4), k9_relat_1(C_6, B_5)) | ~r1_tarski(A_4, B_5) | ~v1_relat_1(C_6))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.02/1.27  tff(c_102, plain, (![B_5]: (r1_tarski('#skF_1', k9_relat_1('#skF_3', B_5)) | ~r1_tarski(k10_relat_1('#skF_3', '#skF_1'), B_5) | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_98, c_4])).
% 2.02/1.27  tff(c_196, plain, (![B_30]: (r1_tarski('#skF_1', k9_relat_1('#skF_3', B_30)) | ~r1_tarski(k10_relat_1('#skF_3', '#skF_1'), B_30))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_102])).
% 2.02/1.27  tff(c_210, plain, (r1_tarski('#skF_1', k9_relat_1('#skF_3', k10_relat_1('#skF_3', '#skF_2')))), inference(resolution, [status(thm)], [c_14, c_196])).
% 2.02/1.27  tff(c_49, plain, (![B_18, A_19]: (r1_tarski(k9_relat_1(B_18, k10_relat_1(B_18, A_19)), A_19) | ~v1_funct_1(B_18) | ~v1_relat_1(B_18))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.02/1.27  tff(c_2, plain, (![A_1, C_3, B_2]: (r1_tarski(A_1, C_3) | ~r1_tarski(B_2, C_3) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.02/1.27  tff(c_225, plain, (![A_31, A_32, B_33]: (r1_tarski(A_31, A_32) | ~r1_tarski(A_31, k9_relat_1(B_33, k10_relat_1(B_33, A_32))) | ~v1_funct_1(B_33) | ~v1_relat_1(B_33))), inference(resolution, [status(thm)], [c_49, c_2])).
% 2.02/1.27  tff(c_228, plain, (r1_tarski('#skF_1', '#skF_2') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_210, c_225])).
% 2.02/1.27  tff(c_245, plain, (r1_tarski('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_18, c_16, c_228])).
% 2.02/1.27  tff(c_247, plain, $false, inference(negUnitSimplification, [status(thm)], [c_10, c_245])).
% 2.02/1.27  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.02/1.27  
% 2.02/1.27  Inference rules
% 2.02/1.27  ----------------------
% 2.02/1.27  #Ref     : 0
% 2.02/1.27  #Sup     : 56
% 2.02/1.27  #Fact    : 0
% 2.02/1.27  #Define  : 0
% 2.02/1.27  #Split   : 2
% 2.02/1.27  #Chain   : 0
% 2.02/1.27  #Close   : 0
% 2.02/1.27  
% 2.02/1.27  Ordering : KBO
% 2.02/1.27  
% 2.02/1.27  Simplification rules
% 2.02/1.27  ----------------------
% 2.02/1.27  #Subsume      : 4
% 2.02/1.27  #Demod        : 24
% 2.02/1.27  #Tautology    : 14
% 2.02/1.27  #SimpNegUnit  : 2
% 2.02/1.27  #BackRed      : 0
% 2.02/1.27  
% 2.02/1.27  #Partial instantiations: 0
% 2.02/1.27  #Strategies tried      : 1
% 2.02/1.27  
% 2.02/1.27  Timing (in seconds)
% 2.02/1.27  ----------------------
% 2.02/1.28  Preprocessing        : 0.28
% 2.02/1.28  Parsing              : 0.16
% 2.02/1.28  CNF conversion       : 0.02
% 2.02/1.28  Main loop            : 0.21
% 2.02/1.28  Inferencing          : 0.08
% 2.02/1.28  Reduction            : 0.06
% 2.02/1.28  Demodulation         : 0.04
% 2.02/1.28  BG Simplification    : 0.01
% 2.02/1.28  Subsumption          : 0.05
% 2.02/1.28  Abstraction          : 0.01
% 2.02/1.28  MUC search           : 0.00
% 2.02/1.28  Cooper               : 0.00
% 2.02/1.28  Total                : 0.51
% 2.02/1.28  Index Insertion      : 0.00
% 2.02/1.28  Index Deletion       : 0.00
% 2.02/1.28  Index Matching       : 0.00
% 2.02/1.28  BG Taut test         : 0.00
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:03:17 EST 2020

% Result     : Theorem 1.66s
% Output     : CNFRefutation 1.66s
% Verified   : 
% Statistics : Number of formulae       :   36 (  53 expanded)
%              Number of leaves         :   18 (  27 expanded)
%              Depth                    :    6
%              Number of atoms          :   56 ( 124 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > r2_hidden > r1_tarski > v1_relat_1 > v1_funct_1 > k5_relat_1 > #nlpp > k2_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(f_67,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_relat_1(B)
          & v1_funct_1(B) )
       => ! [C] :
            ( ( v1_relat_1(C)
              & v1_funct_1(C) )
           => ( r2_hidden(A,k2_relat_1(k5_relat_1(C,B)))
             => r2_hidden(A,k2_relat_1(B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_funct_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_relat_1(B) )
     => v1_relat_1(k5_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ! [C] :
          ( r2_hidden(C,k2_relat_1(B))
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t202_relat_1)).

tff(f_53,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => r1_tarski(k2_relat_1(k5_relat_1(A,B)),k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(c_12,plain,(
    ~ r2_hidden('#skF_1',k2_relat_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_18,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_22,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( v1_relat_1(k5_relat_1(A_3,B_4))
      | ~ v1_relat_1(B_4)
      | ~ v1_relat_1(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_14,plain,(
    r2_hidden('#skF_1',k2_relat_1(k5_relat_1('#skF_3','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_35,plain,(
    ! [C_21,A_22,B_23] :
      ( r2_hidden(C_21,A_22)
      | ~ r2_hidden(C_21,k2_relat_1(B_23))
      | ~ v5_relat_1(B_23,A_22)
      | ~ v1_relat_1(B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_38,plain,(
    ! [A_22] :
      ( r2_hidden('#skF_1',A_22)
      | ~ v5_relat_1(k5_relat_1('#skF_3','#skF_2'),A_22)
      | ~ v1_relat_1(k5_relat_1('#skF_3','#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_14,c_35])).

tff(c_39,plain,(
    ~ v1_relat_1(k5_relat_1('#skF_3','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_38])).

tff(c_42,plain,
    ( ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_6,c_39])).

tff(c_46,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_22,c_42])).

tff(c_48,plain,(
    v1_relat_1(k5_relat_1('#skF_3','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_30,plain,(
    ! [A_19,B_20] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_19,B_20)),k2_relat_1(B_20))
      | ~ v1_relat_1(B_20)
      | ~ v1_relat_1(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( v5_relat_1(B_2,A_1)
      | ~ r1_tarski(k2_relat_1(B_2),A_1)
      | ~ v1_relat_1(B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_50,plain,(
    ! [A_25,B_26] :
      ( v5_relat_1(k5_relat_1(A_25,B_26),k2_relat_1(B_26))
      | ~ v1_relat_1(k5_relat_1(A_25,B_26))
      | ~ v1_relat_1(B_26)
      | ~ v1_relat_1(A_25) ) ),
    inference(resolution,[status(thm)],[c_30,c_2])).

tff(c_47,plain,(
    ! [A_22] :
      ( r2_hidden('#skF_1',A_22)
      | ~ v5_relat_1(k5_relat_1('#skF_3','#skF_2'),A_22) ) ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_54,plain,
    ( r2_hidden('#skF_1',k2_relat_1('#skF_2'))
    | ~ v1_relat_1(k5_relat_1('#skF_3','#skF_2'))
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_47])).

tff(c_57,plain,(
    r2_hidden('#skF_1',k2_relat_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_22,c_48,c_54])).

tff(c_59,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_12,c_57])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n022.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:58:41 EST 2020
% 0.21/0.35  % CPUTime    : 
% 0.21/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.66/1.11  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.66/1.11  
% 1.66/1.11  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.66/1.11  %$ v5_relat_1 > r2_hidden > r1_tarski > v1_relat_1 > v1_funct_1 > k5_relat_1 > #nlpp > k2_relat_1 > #skF_2 > #skF_3 > #skF_1
% 1.66/1.11  
% 1.66/1.11  %Foreground sorts:
% 1.66/1.11  
% 1.66/1.11  
% 1.66/1.11  %Background operators:
% 1.66/1.11  
% 1.66/1.11  
% 1.66/1.11  %Foreground operators:
% 1.66/1.11  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.66/1.11  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.66/1.11  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.66/1.11  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 1.66/1.11  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.66/1.11  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.66/1.11  tff('#skF_2', type, '#skF_2': $i).
% 1.66/1.11  tff('#skF_3', type, '#skF_3': $i).
% 1.66/1.11  tff('#skF_1', type, '#skF_1': $i).
% 1.66/1.11  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 1.66/1.11  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.66/1.11  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.66/1.11  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.66/1.11  
% 1.66/1.12  tff(f_67, negated_conjecture, ~(![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(A, k2_relat_1(k5_relat_1(C, B))) => r2_hidden(A, k2_relat_1(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_funct_1)).
% 1.66/1.12  tff(f_37, axiom, (![A, B]: ((v1_relat_1(A) & v1_relat_1(B)) => v1_relat_1(k5_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k5_relat_1)).
% 1.66/1.12  tff(f_46, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (![C]: (r2_hidden(C, k2_relat_1(B)) => r2_hidden(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t202_relat_1)).
% 1.66/1.12  tff(f_53, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k2_relat_1(k5_relat_1(A, B)), k2_relat_1(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t45_relat_1)).
% 1.66/1.12  tff(f_31, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 1.66/1.12  tff(c_12, plain, (~r2_hidden('#skF_1', k2_relat_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_67])).
% 1.66/1.12  tff(c_18, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_67])).
% 1.66/1.12  tff(c_22, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_67])).
% 1.66/1.12  tff(c_6, plain, (![A_3, B_4]: (v1_relat_1(k5_relat_1(A_3, B_4)) | ~v1_relat_1(B_4) | ~v1_relat_1(A_3))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.66/1.12  tff(c_14, plain, (r2_hidden('#skF_1', k2_relat_1(k5_relat_1('#skF_3', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_67])).
% 1.66/1.12  tff(c_35, plain, (![C_21, A_22, B_23]: (r2_hidden(C_21, A_22) | ~r2_hidden(C_21, k2_relat_1(B_23)) | ~v5_relat_1(B_23, A_22) | ~v1_relat_1(B_23))), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.66/1.12  tff(c_38, plain, (![A_22]: (r2_hidden('#skF_1', A_22) | ~v5_relat_1(k5_relat_1('#skF_3', '#skF_2'), A_22) | ~v1_relat_1(k5_relat_1('#skF_3', '#skF_2')))), inference(resolution, [status(thm)], [c_14, c_35])).
% 1.66/1.12  tff(c_39, plain, (~v1_relat_1(k5_relat_1('#skF_3', '#skF_2'))), inference(splitLeft, [status(thm)], [c_38])).
% 1.66/1.12  tff(c_42, plain, (~v1_relat_1('#skF_2') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_6, c_39])).
% 1.66/1.12  tff(c_46, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_18, c_22, c_42])).
% 1.66/1.12  tff(c_48, plain, (v1_relat_1(k5_relat_1('#skF_3', '#skF_2'))), inference(splitRight, [status(thm)], [c_38])).
% 1.66/1.12  tff(c_30, plain, (![A_19, B_20]: (r1_tarski(k2_relat_1(k5_relat_1(A_19, B_20)), k2_relat_1(B_20)) | ~v1_relat_1(B_20) | ~v1_relat_1(A_19))), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.66/1.12  tff(c_2, plain, (![B_2, A_1]: (v5_relat_1(B_2, A_1) | ~r1_tarski(k2_relat_1(B_2), A_1) | ~v1_relat_1(B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.66/1.12  tff(c_50, plain, (![A_25, B_26]: (v5_relat_1(k5_relat_1(A_25, B_26), k2_relat_1(B_26)) | ~v1_relat_1(k5_relat_1(A_25, B_26)) | ~v1_relat_1(B_26) | ~v1_relat_1(A_25))), inference(resolution, [status(thm)], [c_30, c_2])).
% 1.66/1.12  tff(c_47, plain, (![A_22]: (r2_hidden('#skF_1', A_22) | ~v5_relat_1(k5_relat_1('#skF_3', '#skF_2'), A_22))), inference(splitRight, [status(thm)], [c_38])).
% 1.66/1.12  tff(c_54, plain, (r2_hidden('#skF_1', k2_relat_1('#skF_2')) | ~v1_relat_1(k5_relat_1('#skF_3', '#skF_2')) | ~v1_relat_1('#skF_2') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_50, c_47])).
% 1.66/1.12  tff(c_57, plain, (r2_hidden('#skF_1', k2_relat_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_22, c_48, c_54])).
% 1.66/1.12  tff(c_59, plain, $false, inference(negUnitSimplification, [status(thm)], [c_12, c_57])).
% 1.66/1.12  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.66/1.12  
% 1.66/1.12  Inference rules
% 1.66/1.12  ----------------------
% 1.66/1.12  #Ref     : 0
% 1.66/1.12  #Sup     : 5
% 1.66/1.12  #Fact    : 0
% 1.66/1.12  #Define  : 0
% 1.66/1.12  #Split   : 1
% 1.66/1.12  #Chain   : 0
% 1.66/1.12  #Close   : 0
% 1.66/1.12  
% 1.66/1.12  Ordering : KBO
% 1.66/1.12  
% 1.66/1.12  Simplification rules
% 1.66/1.12  ----------------------
% 1.66/1.12  #Subsume      : 0
% 1.66/1.12  #Demod        : 5
% 1.66/1.12  #Tautology    : 1
% 1.66/1.12  #SimpNegUnit  : 1
% 1.66/1.12  #BackRed      : 0
% 1.66/1.12  
% 1.66/1.12  #Partial instantiations: 0
% 1.66/1.12  #Strategies tried      : 1
% 1.66/1.12  
% 1.66/1.12  Timing (in seconds)
% 1.66/1.12  ----------------------
% 1.66/1.13  Preprocessing        : 0.26
% 1.66/1.13  Parsing              : 0.15
% 1.66/1.13  CNF conversion       : 0.02
% 1.66/1.13  Main loop            : 0.11
% 1.66/1.13  Inferencing          : 0.05
% 1.66/1.13  Reduction            : 0.03
% 1.66/1.13  Demodulation         : 0.02
% 1.66/1.13  BG Simplification    : 0.01
% 1.66/1.13  Subsumption          : 0.02
% 1.66/1.13  Abstraction          : 0.00
% 1.66/1.13  MUC search           : 0.00
% 1.66/1.13  Cooper               : 0.00
% 1.66/1.13  Total                : 0.39
% 1.66/1.13  Index Insertion      : 0.00
% 1.66/1.13  Index Deletion       : 0.00
% 1.66/1.13  Index Matching       : 0.00
% 1.66/1.13  BG Taut test         : 0.00
%------------------------------------------------------------------------------

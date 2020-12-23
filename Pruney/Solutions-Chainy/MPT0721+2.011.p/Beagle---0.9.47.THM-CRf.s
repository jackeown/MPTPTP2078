%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:53 EST 2020

% Result     : Theorem 2.01s
% Output     : CNFRefutation 2.01s
% Verified   : 
% Statistics : Number of formulae       :   28 (  32 expanded)
%              Number of leaves         :   16 (  20 expanded)
%              Depth                    :    6
%              Number of atoms          :   37 (  57 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > r2_hidden > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_funct_1 > #nlpp > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_51,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_relat_1(C)
          & v5_relat_1(C,A)
          & v1_funct_1(C) )
       => ( r2_hidden(B,k1_relat_1(C))
         => m1_subset_1(k1_funct_1(C,B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t176_funct_1)).

tff(f_40,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A)
        & v1_funct_1(B) )
     => ! [C] :
          ( r2_hidden(C,k1_relat_1(B))
         => r2_hidden(k1_funct_1(B,C),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t172_funct_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

tff(c_12,plain,(
    v5_relat_1('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_14,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_10,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_8,plain,(
    r2_hidden('#skF_2',k1_relat_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_20,plain,(
    ! [B_9,C_10,A_11] :
      ( r2_hidden(k1_funct_1(B_9,C_10),A_11)
      | ~ r2_hidden(C_10,k1_relat_1(B_9))
      | ~ v1_funct_1(B_9)
      | ~ v5_relat_1(B_9,A_11)
      | ~ v1_relat_1(B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( m1_subset_1(A_1,B_2)
      | ~ r2_hidden(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_25,plain,(
    ! [B_12,C_13,A_14] :
      ( m1_subset_1(k1_funct_1(B_12,C_13),A_14)
      | ~ r2_hidden(C_13,k1_relat_1(B_12))
      | ~ v1_funct_1(B_12)
      | ~ v5_relat_1(B_12,A_14)
      | ~ v1_relat_1(B_12) ) ),
    inference(resolution,[status(thm)],[c_20,c_2])).

tff(c_30,plain,(
    ! [A_14] :
      ( m1_subset_1(k1_funct_1('#skF_3','#skF_2'),A_14)
      | ~ v1_funct_1('#skF_3')
      | ~ v5_relat_1('#skF_3',A_14)
      | ~ v1_relat_1('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_8,c_25])).

tff(c_35,plain,(
    ! [A_15] :
      ( m1_subset_1(k1_funct_1('#skF_3','#skF_2'),A_15)
      | ~ v5_relat_1('#skF_3',A_15) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_10,c_30])).

tff(c_6,plain,(
    ~ m1_subset_1(k1_funct_1('#skF_3','#skF_2'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_38,plain,(
    ~ v5_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_35,c_6])).

tff(c_42,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_38])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n025.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:40:21 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.01/1.46  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.01/1.47  
% 2.01/1.47  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.01/1.47  %$ v5_relat_1 > r2_hidden > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_funct_1 > #nlpp > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 2.01/1.47  
% 2.01/1.47  %Foreground sorts:
% 2.01/1.47  
% 2.01/1.47  
% 2.01/1.47  %Background operators:
% 2.01/1.47  
% 2.01/1.47  
% 2.01/1.47  %Foreground operators:
% 2.01/1.47  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.01/1.47  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.01/1.47  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.01/1.47  tff('#skF_2', type, '#skF_2': $i).
% 2.01/1.47  tff('#skF_3', type, '#skF_3': $i).
% 2.01/1.47  tff('#skF_1', type, '#skF_1': $i).
% 2.01/1.47  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.01/1.47  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.01/1.47  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.01/1.47  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.01/1.47  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.01/1.47  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.01/1.47  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.01/1.47  
% 2.01/1.48  tff(f_51, negated_conjecture, ~(![A, B, C]: (((v1_relat_1(C) & v5_relat_1(C, A)) & v1_funct_1(C)) => (r2_hidden(B, k1_relat_1(C)) => m1_subset_1(k1_funct_1(C, B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t176_funct_1)).
% 2.01/1.48  tff(f_40, axiom, (![A, B]: (((v1_relat_1(B) & v5_relat_1(B, A)) & v1_funct_1(B)) => (![C]: (r2_hidden(C, k1_relat_1(B)) => r2_hidden(k1_funct_1(B, C), A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t172_funct_1)).
% 2.01/1.48  tff(f_29, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_subset)).
% 2.01/1.48  tff(c_12, plain, (v5_relat_1('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.01/1.48  tff(c_14, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.01/1.48  tff(c_10, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.01/1.48  tff(c_8, plain, (r2_hidden('#skF_2', k1_relat_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.01/1.48  tff(c_20, plain, (![B_9, C_10, A_11]: (r2_hidden(k1_funct_1(B_9, C_10), A_11) | ~r2_hidden(C_10, k1_relat_1(B_9)) | ~v1_funct_1(B_9) | ~v5_relat_1(B_9, A_11) | ~v1_relat_1(B_9))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.01/1.48  tff(c_2, plain, (![A_1, B_2]: (m1_subset_1(A_1, B_2) | ~r2_hidden(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.01/1.48  tff(c_25, plain, (![B_12, C_13, A_14]: (m1_subset_1(k1_funct_1(B_12, C_13), A_14) | ~r2_hidden(C_13, k1_relat_1(B_12)) | ~v1_funct_1(B_12) | ~v5_relat_1(B_12, A_14) | ~v1_relat_1(B_12))), inference(resolution, [status(thm)], [c_20, c_2])).
% 2.01/1.48  tff(c_30, plain, (![A_14]: (m1_subset_1(k1_funct_1('#skF_3', '#skF_2'), A_14) | ~v1_funct_1('#skF_3') | ~v5_relat_1('#skF_3', A_14) | ~v1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_8, c_25])).
% 2.01/1.48  tff(c_35, plain, (![A_15]: (m1_subset_1(k1_funct_1('#skF_3', '#skF_2'), A_15) | ~v5_relat_1('#skF_3', A_15))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_10, c_30])).
% 2.01/1.48  tff(c_6, plain, (~m1_subset_1(k1_funct_1('#skF_3', '#skF_2'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.01/1.48  tff(c_38, plain, (~v5_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_35, c_6])).
% 2.01/1.48  tff(c_42, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12, c_38])).
% 2.01/1.48  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.01/1.48  
% 2.01/1.48  Inference rules
% 2.01/1.48  ----------------------
% 2.01/1.48  #Ref     : 0
% 2.01/1.48  #Sup     : 5
% 2.01/1.48  #Fact    : 0
% 2.01/1.48  #Define  : 0
% 2.01/1.48  #Split   : 0
% 2.01/1.48  #Chain   : 0
% 2.01/1.48  #Close   : 0
% 2.01/1.48  
% 2.01/1.48  Ordering : KBO
% 2.01/1.48  
% 2.01/1.48  Simplification rules
% 2.01/1.48  ----------------------
% 2.01/1.48  #Subsume      : 0
% 2.01/1.48  #Demod        : 3
% 2.01/1.48  #Tautology    : 0
% 2.01/1.48  #SimpNegUnit  : 0
% 2.01/1.48  #BackRed      : 0
% 2.01/1.48  
% 2.01/1.48  #Partial instantiations: 0
% 2.01/1.48  #Strategies tried      : 1
% 2.01/1.48  
% 2.01/1.48  Timing (in seconds)
% 2.01/1.48  ----------------------
% 2.01/1.49  Preprocessing        : 0.38
% 2.01/1.49  Parsing              : 0.21
% 2.01/1.49  CNF conversion       : 0.03
% 2.01/1.49  Main loop            : 0.16
% 2.01/1.49  Inferencing          : 0.08
% 2.01/1.49  Reduction            : 0.04
% 2.01/1.49  Demodulation         : 0.03
% 2.01/1.49  BG Simplification    : 0.02
% 2.01/1.49  Subsumption          : 0.02
% 2.01/1.49  Abstraction          : 0.01
% 2.01/1.49  MUC search           : 0.00
% 2.01/1.49  Cooper               : 0.00
% 2.01/1.49  Total                : 0.58
% 2.01/1.49  Index Insertion      : 0.00
% 2.01/1.49  Index Deletion       : 0.00
% 2.01/1.49  Index Matching       : 0.00
% 2.01/1.49  BG Taut test         : 0.00
%------------------------------------------------------------------------------

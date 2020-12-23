%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:53 EST 2020

% Result     : Theorem 1.78s
% Output     : CNFRefutation 1.81s
% Verified   : 
% Statistics : Number of formulae       :   32 (  36 expanded)
%              Number of leaves         :   18 (  22 expanded)
%              Depth                    :    7
%              Number of atoms          :   48 (  68 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > r2_hidden > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

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

tff(f_57,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_relat_1(C)
          & v5_relat_1(C,A)
          & v1_funct_1(C) )
       => ( r2_hidden(B,k1_relat_1(C))
         => m1_subset_1(k1_funct_1(C,B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t176_funct_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r2_hidden(A,k1_relat_1(B))
       => r2_hidden(k1_funct_1(B,A),k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_funct_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ! [C] :
          ( r2_hidden(C,k2_relat_1(B))
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t202_relat_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

tff(c_14,plain,(
    v5_relat_1('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_16,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_12,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_10,plain,(
    r2_hidden('#skF_2',k1_relat_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_23,plain,(
    ! [B_14,A_15] :
      ( r2_hidden(k1_funct_1(B_14,A_15),k2_relat_1(B_14))
      | ~ r2_hidden(A_15,k1_relat_1(B_14))
      | ~ v1_funct_1(B_14)
      | ~ v1_relat_1(B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_4,plain,(
    ! [C_6,A_3,B_4] :
      ( r2_hidden(C_6,A_3)
      | ~ r2_hidden(C_6,k2_relat_1(B_4))
      | ~ v5_relat_1(B_4,A_3)
      | ~ v1_relat_1(B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_32,plain,(
    ! [B_18,A_19,A_20] :
      ( r2_hidden(k1_funct_1(B_18,A_19),A_20)
      | ~ v5_relat_1(B_18,A_20)
      | ~ r2_hidden(A_19,k1_relat_1(B_18))
      | ~ v1_funct_1(B_18)
      | ~ v1_relat_1(B_18) ) ),
    inference(resolution,[status(thm)],[c_23,c_4])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( m1_subset_1(A_1,B_2)
      | ~ r2_hidden(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_41,plain,(
    ! [B_21,A_22,A_23] :
      ( m1_subset_1(k1_funct_1(B_21,A_22),A_23)
      | ~ v5_relat_1(B_21,A_23)
      | ~ r2_hidden(A_22,k1_relat_1(B_21))
      | ~ v1_funct_1(B_21)
      | ~ v1_relat_1(B_21) ) ),
    inference(resolution,[status(thm)],[c_32,c_2])).

tff(c_46,plain,(
    ! [A_23] :
      ( m1_subset_1(k1_funct_1('#skF_3','#skF_2'),A_23)
      | ~ v5_relat_1('#skF_3',A_23)
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_10,c_41])).

tff(c_51,plain,(
    ! [A_24] :
      ( m1_subset_1(k1_funct_1('#skF_3','#skF_2'),A_24)
      | ~ v5_relat_1('#skF_3',A_24) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_12,c_46])).

tff(c_8,plain,(
    ~ m1_subset_1(k1_funct_1('#skF_3','#skF_2'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_54,plain,(
    ~ v5_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_51,c_8])).

tff(c_58,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_54])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:04:26 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.78/1.17  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.78/1.17  
% 1.78/1.17  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.81/1.18  %$ v5_relat_1 > r2_hidden > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 1.81/1.18  
% 1.81/1.18  %Foreground sorts:
% 1.81/1.18  
% 1.81/1.18  
% 1.81/1.18  %Background operators:
% 1.81/1.18  
% 1.81/1.18  
% 1.81/1.18  %Foreground operators:
% 1.81/1.18  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.81/1.18  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.81/1.18  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.81/1.18  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.81/1.18  tff('#skF_2', type, '#skF_2': $i).
% 1.81/1.18  tff('#skF_3', type, '#skF_3': $i).
% 1.81/1.18  tff('#skF_1', type, '#skF_1': $i).
% 1.81/1.18  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 1.81/1.18  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 1.81/1.18  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.81/1.18  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.81/1.18  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.81/1.18  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.81/1.18  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.81/1.18  
% 1.81/1.19  tff(f_57, negated_conjecture, ~(![A, B, C]: (((v1_relat_1(C) & v5_relat_1(C, A)) & v1_funct_1(C)) => (r2_hidden(B, k1_relat_1(C)) => m1_subset_1(k1_funct_1(C, B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t176_funct_1)).
% 1.81/1.19  tff(f_46, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r2_hidden(A, k1_relat_1(B)) => r2_hidden(k1_funct_1(B, A), k2_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_funct_1)).
% 1.81/1.19  tff(f_38, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (![C]: (r2_hidden(C, k2_relat_1(B)) => r2_hidden(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t202_relat_1)).
% 1.81/1.19  tff(f_29, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_subset)).
% 1.81/1.19  tff(c_14, plain, (v5_relat_1('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.81/1.19  tff(c_16, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.81/1.19  tff(c_12, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.81/1.19  tff(c_10, plain, (r2_hidden('#skF_2', k1_relat_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.81/1.19  tff(c_23, plain, (![B_14, A_15]: (r2_hidden(k1_funct_1(B_14, A_15), k2_relat_1(B_14)) | ~r2_hidden(A_15, k1_relat_1(B_14)) | ~v1_funct_1(B_14) | ~v1_relat_1(B_14))), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.81/1.19  tff(c_4, plain, (![C_6, A_3, B_4]: (r2_hidden(C_6, A_3) | ~r2_hidden(C_6, k2_relat_1(B_4)) | ~v5_relat_1(B_4, A_3) | ~v1_relat_1(B_4))), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.81/1.19  tff(c_32, plain, (![B_18, A_19, A_20]: (r2_hidden(k1_funct_1(B_18, A_19), A_20) | ~v5_relat_1(B_18, A_20) | ~r2_hidden(A_19, k1_relat_1(B_18)) | ~v1_funct_1(B_18) | ~v1_relat_1(B_18))), inference(resolution, [status(thm)], [c_23, c_4])).
% 1.81/1.19  tff(c_2, plain, (![A_1, B_2]: (m1_subset_1(A_1, B_2) | ~r2_hidden(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.81/1.19  tff(c_41, plain, (![B_21, A_22, A_23]: (m1_subset_1(k1_funct_1(B_21, A_22), A_23) | ~v5_relat_1(B_21, A_23) | ~r2_hidden(A_22, k1_relat_1(B_21)) | ~v1_funct_1(B_21) | ~v1_relat_1(B_21))), inference(resolution, [status(thm)], [c_32, c_2])).
% 1.81/1.19  tff(c_46, plain, (![A_23]: (m1_subset_1(k1_funct_1('#skF_3', '#skF_2'), A_23) | ~v5_relat_1('#skF_3', A_23) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_10, c_41])).
% 1.81/1.19  tff(c_51, plain, (![A_24]: (m1_subset_1(k1_funct_1('#skF_3', '#skF_2'), A_24) | ~v5_relat_1('#skF_3', A_24))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_12, c_46])).
% 1.81/1.19  tff(c_8, plain, (~m1_subset_1(k1_funct_1('#skF_3', '#skF_2'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.81/1.19  tff(c_54, plain, (~v5_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_51, c_8])).
% 1.81/1.19  tff(c_58, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_14, c_54])).
% 1.81/1.19  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.81/1.19  
% 1.81/1.19  Inference rules
% 1.81/1.19  ----------------------
% 1.81/1.19  #Ref     : 0
% 1.81/1.19  #Sup     : 8
% 1.81/1.19  #Fact    : 0
% 1.81/1.19  #Define  : 0
% 1.81/1.19  #Split   : 0
% 1.81/1.19  #Chain   : 0
% 1.81/1.19  #Close   : 0
% 1.81/1.19  
% 1.81/1.19  Ordering : KBO
% 1.81/1.19  
% 1.81/1.19  Simplification rules
% 1.81/1.19  ----------------------
% 1.81/1.19  #Subsume      : 0
% 1.81/1.19  #Demod        : 3
% 1.81/1.19  #Tautology    : 0
% 1.81/1.19  #SimpNegUnit  : 0
% 1.81/1.19  #BackRed      : 0
% 1.81/1.19  
% 1.81/1.19  #Partial instantiations: 0
% 1.81/1.19  #Strategies tried      : 1
% 1.81/1.19  
% 1.81/1.19  Timing (in seconds)
% 1.81/1.19  ----------------------
% 1.81/1.19  Preprocessing        : 0.26
% 1.81/1.19  Parsing              : 0.15
% 1.81/1.19  CNF conversion       : 0.02
% 1.81/1.19  Main loop            : 0.16
% 1.81/1.19  Inferencing          : 0.08
% 1.81/1.19  Reduction            : 0.04
% 1.81/1.19  Demodulation         : 0.03
% 1.81/1.19  BG Simplification    : 0.01
% 1.81/1.19  Subsumption          : 0.02
% 1.81/1.19  Abstraction          : 0.01
% 1.81/1.19  MUC search           : 0.00
% 1.81/1.19  Cooper               : 0.00
% 1.81/1.19  Total                : 0.44
% 1.81/1.19  Index Insertion      : 0.00
% 1.81/1.19  Index Deletion       : 0.00
% 1.81/1.19  Index Matching       : 0.00
% 1.81/1.19  BG Taut test         : 0.00
%------------------------------------------------------------------------------

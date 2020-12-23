%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:52 EST 2020

% Result     : Theorem 1.83s
% Output     : CNFRefutation 1.83s
% Verified   : 
% Statistics : Number of formulae       :   37 (  41 expanded)
%              Number of leaves         :   21 (  25 expanded)
%              Depth                    :    8
%              Number of atoms          :   57 (  77 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_61,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_relat_1(C)
          & v5_relat_1(C,A)
          & v1_funct_1(C) )
       => ( r2_hidden(B,k1_relat_1(C))
         => m1_subset_1(k1_funct_1(C,B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t176_funct_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r2_hidden(A,k1_relat_1(B))
       => r2_hidden(k1_funct_1(B,A),k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_funct_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_36,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

tff(c_22,plain,(
    v5_relat_1('#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_24,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_20,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_18,plain,(
    r2_hidden('#skF_3',k1_relat_1('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_12,plain,(
    ! [B_9,A_8] :
      ( r1_tarski(k2_relat_1(B_9),A_8)
      | ~ v5_relat_1(B_9,A_8)
      | ~ v1_relat_1(B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_83,plain,(
    ! [B_36,A_37] :
      ( r2_hidden(k1_funct_1(B_36,A_37),k2_relat_1(B_36))
      | ~ r2_hidden(A_37,k1_relat_1(B_36))
      | ~ v1_funct_1(B_36)
      | ~ v1_relat_1(B_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_99,plain,(
    ! [B_44,A_45,B_46] :
      ( r2_hidden(k1_funct_1(B_44,A_45),B_46)
      | ~ r1_tarski(k2_relat_1(B_44),B_46)
      | ~ r2_hidden(A_45,k1_relat_1(B_44))
      | ~ v1_funct_1(B_44)
      | ~ v1_relat_1(B_44) ) ),
    inference(resolution,[status(thm)],[c_83,c_2])).

tff(c_8,plain,(
    ! [A_6,B_7] :
      ( m1_subset_1(A_6,B_7)
      | ~ r2_hidden(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_107,plain,(
    ! [B_47,A_48,B_49] :
      ( m1_subset_1(k1_funct_1(B_47,A_48),B_49)
      | ~ r1_tarski(k2_relat_1(B_47),B_49)
      | ~ r2_hidden(A_48,k1_relat_1(B_47))
      | ~ v1_funct_1(B_47)
      | ~ v1_relat_1(B_47) ) ),
    inference(resolution,[status(thm)],[c_99,c_8])).

tff(c_115,plain,(
    ! [B_50,A_51,A_52] :
      ( m1_subset_1(k1_funct_1(B_50,A_51),A_52)
      | ~ r2_hidden(A_51,k1_relat_1(B_50))
      | ~ v1_funct_1(B_50)
      | ~ v5_relat_1(B_50,A_52)
      | ~ v1_relat_1(B_50) ) ),
    inference(resolution,[status(thm)],[c_12,c_107])).

tff(c_126,plain,(
    ! [A_52] :
      ( m1_subset_1(k1_funct_1('#skF_4','#skF_3'),A_52)
      | ~ v1_funct_1('#skF_4')
      | ~ v5_relat_1('#skF_4',A_52)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_18,c_115])).

tff(c_133,plain,(
    ! [A_53] :
      ( m1_subset_1(k1_funct_1('#skF_4','#skF_3'),A_53)
      | ~ v5_relat_1('#skF_4',A_53) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_20,c_126])).

tff(c_16,plain,(
    ~ m1_subset_1(k1_funct_1('#skF_4','#skF_3'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_136,plain,(
    ~ v5_relat_1('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_133,c_16])).

tff(c_140,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_136])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n006.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 09:48:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.83/1.19  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.83/1.19  
% 1.83/1.19  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.83/1.19  %$ v5_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 1.83/1.19  
% 1.83/1.19  %Foreground sorts:
% 1.83/1.19  
% 1.83/1.19  
% 1.83/1.19  %Background operators:
% 1.83/1.19  
% 1.83/1.19  
% 1.83/1.19  %Foreground operators:
% 1.83/1.19  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.83/1.19  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.83/1.19  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.83/1.19  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.83/1.19  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.83/1.19  tff('#skF_2', type, '#skF_2': $i).
% 1.83/1.19  tff('#skF_3', type, '#skF_3': $i).
% 1.83/1.19  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 1.83/1.19  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 1.83/1.19  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.83/1.19  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.83/1.19  tff('#skF_4', type, '#skF_4': $i).
% 1.83/1.19  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.83/1.19  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.83/1.19  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.83/1.19  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.83/1.19  
% 1.83/1.20  tff(f_61, negated_conjecture, ~(![A, B, C]: (((v1_relat_1(C) & v5_relat_1(C, A)) & v1_funct_1(C)) => (r2_hidden(B, k1_relat_1(C)) => m1_subset_1(k1_funct_1(C, B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t176_funct_1)).
% 1.83/1.20  tff(f_42, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 1.83/1.20  tff(f_50, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r2_hidden(A, k1_relat_1(B)) => r2_hidden(k1_funct_1(B, A), k2_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_funct_1)).
% 1.83/1.20  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 1.83/1.20  tff(f_36, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_subset)).
% 1.83/1.20  tff(c_22, plain, (v5_relat_1('#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_61])).
% 1.83/1.20  tff(c_24, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_61])).
% 1.83/1.20  tff(c_20, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_61])).
% 1.83/1.20  tff(c_18, plain, (r2_hidden('#skF_3', k1_relat_1('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_61])).
% 1.83/1.20  tff(c_12, plain, (![B_9, A_8]: (r1_tarski(k2_relat_1(B_9), A_8) | ~v5_relat_1(B_9, A_8) | ~v1_relat_1(B_9))), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.83/1.20  tff(c_83, plain, (![B_36, A_37]: (r2_hidden(k1_funct_1(B_36, A_37), k2_relat_1(B_36)) | ~r2_hidden(A_37, k1_relat_1(B_36)) | ~v1_funct_1(B_36) | ~v1_relat_1(B_36))), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.83/1.20  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.83/1.20  tff(c_99, plain, (![B_44, A_45, B_46]: (r2_hidden(k1_funct_1(B_44, A_45), B_46) | ~r1_tarski(k2_relat_1(B_44), B_46) | ~r2_hidden(A_45, k1_relat_1(B_44)) | ~v1_funct_1(B_44) | ~v1_relat_1(B_44))), inference(resolution, [status(thm)], [c_83, c_2])).
% 1.83/1.21  tff(c_8, plain, (![A_6, B_7]: (m1_subset_1(A_6, B_7) | ~r2_hidden(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.83/1.21  tff(c_107, plain, (![B_47, A_48, B_49]: (m1_subset_1(k1_funct_1(B_47, A_48), B_49) | ~r1_tarski(k2_relat_1(B_47), B_49) | ~r2_hidden(A_48, k1_relat_1(B_47)) | ~v1_funct_1(B_47) | ~v1_relat_1(B_47))), inference(resolution, [status(thm)], [c_99, c_8])).
% 1.83/1.21  tff(c_115, plain, (![B_50, A_51, A_52]: (m1_subset_1(k1_funct_1(B_50, A_51), A_52) | ~r2_hidden(A_51, k1_relat_1(B_50)) | ~v1_funct_1(B_50) | ~v5_relat_1(B_50, A_52) | ~v1_relat_1(B_50))), inference(resolution, [status(thm)], [c_12, c_107])).
% 1.83/1.21  tff(c_126, plain, (![A_52]: (m1_subset_1(k1_funct_1('#skF_4', '#skF_3'), A_52) | ~v1_funct_1('#skF_4') | ~v5_relat_1('#skF_4', A_52) | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_18, c_115])).
% 1.83/1.21  tff(c_133, plain, (![A_53]: (m1_subset_1(k1_funct_1('#skF_4', '#skF_3'), A_53) | ~v5_relat_1('#skF_4', A_53))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_20, c_126])).
% 1.83/1.21  tff(c_16, plain, (~m1_subset_1(k1_funct_1('#skF_4', '#skF_3'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_61])).
% 1.83/1.21  tff(c_136, plain, (~v5_relat_1('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_133, c_16])).
% 1.83/1.21  tff(c_140, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_22, c_136])).
% 1.83/1.21  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.83/1.21  
% 1.83/1.21  Inference rules
% 1.83/1.21  ----------------------
% 1.83/1.21  #Ref     : 0
% 1.83/1.21  #Sup     : 24
% 1.83/1.21  #Fact    : 0
% 1.83/1.21  #Define  : 0
% 1.83/1.21  #Split   : 0
% 1.83/1.21  #Chain   : 0
% 1.83/1.21  #Close   : 0
% 1.83/1.21  
% 1.83/1.21  Ordering : KBO
% 1.83/1.21  
% 1.83/1.21  Simplification rules
% 1.83/1.21  ----------------------
% 1.83/1.21  #Subsume      : 2
% 1.83/1.21  #Demod        : 4
% 1.83/1.21  #Tautology    : 3
% 1.83/1.21  #SimpNegUnit  : 0
% 1.83/1.21  #BackRed      : 0
% 1.83/1.21  
% 1.83/1.21  #Partial instantiations: 0
% 1.83/1.21  #Strategies tried      : 1
% 1.83/1.21  
% 1.83/1.21  Timing (in seconds)
% 1.83/1.21  ----------------------
% 1.83/1.21  Preprocessing        : 0.27
% 1.83/1.21  Parsing              : 0.15
% 1.83/1.21  CNF conversion       : 0.02
% 1.83/1.21  Main loop            : 0.17
% 1.83/1.21  Inferencing          : 0.07
% 1.83/1.21  Reduction            : 0.04
% 1.83/1.21  Demodulation         : 0.03
% 1.83/1.21  BG Simplification    : 0.01
% 1.83/1.21  Subsumption          : 0.03
% 1.83/1.21  Abstraction          : 0.01
% 1.83/1.21  MUC search           : 0.00
% 1.83/1.21  Cooper               : 0.00
% 1.83/1.21  Total                : 0.46
% 1.83/1.21  Index Insertion      : 0.00
% 1.83/1.21  Index Deletion       : 0.00
% 1.83/1.21  Index Matching       : 0.00
% 1.83/1.21  BG Taut test         : 0.00
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:53 EST 2020

% Result     : Theorem 1.69s
% Output     : CNFRefutation 1.69s
% Verified   : 
% Statistics : Number of formulae       :   37 (  41 expanded)
%              Number of leaves         :   21 (  25 expanded)
%              Depth                    :    8
%              Number of atoms          :   55 (  75 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

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

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

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

tff(f_60,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_relat_1(C)
          & v5_relat_1(C,A)
          & v1_funct_1(C) )
       => ( r2_hidden(B,k1_relat_1(C))
         => m1_subset_1(k1_funct_1(C,B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t176_funct_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r2_hidden(A,k1_relat_1(B))
       => r2_hidden(k1_funct_1(B,A),k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_funct_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

tff(c_20,plain,(
    v5_relat_1('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_22,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_18,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_16,plain,(
    r2_hidden('#skF_2',k1_relat_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_10,plain,(
    ! [B_7,A_6] :
      ( r1_tarski(k2_relat_1(B_7),A_6)
      | ~ v5_relat_1(B_7,A_6)
      | ~ v1_relat_1(B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_44,plain,(
    ! [B_25,A_26] :
      ( r2_hidden(k1_funct_1(B_25,A_26),k2_relat_1(B_25))
      | ~ r2_hidden(A_26,k1_relat_1(B_25))
      | ~ v1_funct_1(B_25)
      | ~ v1_relat_1(B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( m1_subset_1(A_1,k1_zfmisc_1(B_2))
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_35,plain,(
    ! [A_18,C_19,B_20] :
      ( m1_subset_1(A_18,C_19)
      | ~ m1_subset_1(B_20,k1_zfmisc_1(C_19))
      | ~ r2_hidden(A_18,B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_38,plain,(
    ! [A_18,B_2,A_1] :
      ( m1_subset_1(A_18,B_2)
      | ~ r2_hidden(A_18,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(resolution,[status(thm)],[c_4,c_35])).

tff(c_48,plain,(
    ! [B_27,A_28,B_29] :
      ( m1_subset_1(k1_funct_1(B_27,A_28),B_29)
      | ~ r1_tarski(k2_relat_1(B_27),B_29)
      | ~ r2_hidden(A_28,k1_relat_1(B_27))
      | ~ v1_funct_1(B_27)
      | ~ v1_relat_1(B_27) ) ),
    inference(resolution,[status(thm)],[c_44,c_38])).

tff(c_52,plain,(
    ! [B_30,A_31,A_32] :
      ( m1_subset_1(k1_funct_1(B_30,A_31),A_32)
      | ~ r2_hidden(A_31,k1_relat_1(B_30))
      | ~ v1_funct_1(B_30)
      | ~ v5_relat_1(B_30,A_32)
      | ~ v1_relat_1(B_30) ) ),
    inference(resolution,[status(thm)],[c_10,c_48])).

tff(c_54,plain,(
    ! [A_32] :
      ( m1_subset_1(k1_funct_1('#skF_3','#skF_2'),A_32)
      | ~ v1_funct_1('#skF_3')
      | ~ v5_relat_1('#skF_3',A_32)
      | ~ v1_relat_1('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_16,c_52])).

tff(c_58,plain,(
    ! [A_33] :
      ( m1_subset_1(k1_funct_1('#skF_3','#skF_2'),A_33)
      | ~ v5_relat_1('#skF_3',A_33) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_18,c_54])).

tff(c_14,plain,(
    ~ m1_subset_1(k1_funct_1('#skF_3','#skF_2'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_68,plain,(
    ~ v5_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_58,c_14])).

tff(c_74,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_68])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:58:30 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.69/1.12  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.69/1.13  
% 1.69/1.13  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.69/1.13  %$ v5_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 1.69/1.13  
% 1.69/1.13  %Foreground sorts:
% 1.69/1.13  
% 1.69/1.13  
% 1.69/1.13  %Background operators:
% 1.69/1.13  
% 1.69/1.13  
% 1.69/1.13  %Foreground operators:
% 1.69/1.13  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.69/1.13  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.69/1.13  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.69/1.13  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.69/1.13  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.69/1.13  tff('#skF_2', type, '#skF_2': $i).
% 1.69/1.13  tff('#skF_3', type, '#skF_3': $i).
% 1.69/1.13  tff('#skF_1', type, '#skF_1': $i).
% 1.69/1.13  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 1.69/1.13  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.69/1.13  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 1.69/1.13  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.69/1.13  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.69/1.13  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.69/1.13  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.69/1.13  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.69/1.13  
% 1.69/1.14  tff(f_60, negated_conjecture, ~(![A, B, C]: (((v1_relat_1(C) & v5_relat_1(C, A)) & v1_funct_1(C)) => (r2_hidden(B, k1_relat_1(C)) => m1_subset_1(k1_funct_1(C, B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t176_funct_1)).
% 1.69/1.14  tff(f_41, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 1.69/1.14  tff(f_49, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r2_hidden(A, k1_relat_1(B)) => r2_hidden(k1_funct_1(B, A), k2_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_funct_1)).
% 1.69/1.14  tff(f_29, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 1.69/1.14  tff(f_35, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 1.69/1.14  tff(c_20, plain, (v5_relat_1('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_60])).
% 1.69/1.14  tff(c_22, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_60])).
% 1.69/1.14  tff(c_18, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_60])).
% 1.69/1.14  tff(c_16, plain, (r2_hidden('#skF_2', k1_relat_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_60])).
% 1.69/1.14  tff(c_10, plain, (![B_7, A_6]: (r1_tarski(k2_relat_1(B_7), A_6) | ~v5_relat_1(B_7, A_6) | ~v1_relat_1(B_7))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.69/1.14  tff(c_44, plain, (![B_25, A_26]: (r2_hidden(k1_funct_1(B_25, A_26), k2_relat_1(B_25)) | ~r2_hidden(A_26, k1_relat_1(B_25)) | ~v1_funct_1(B_25) | ~v1_relat_1(B_25))), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.69/1.14  tff(c_4, plain, (![A_1, B_2]: (m1_subset_1(A_1, k1_zfmisc_1(B_2)) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.69/1.14  tff(c_35, plain, (![A_18, C_19, B_20]: (m1_subset_1(A_18, C_19) | ~m1_subset_1(B_20, k1_zfmisc_1(C_19)) | ~r2_hidden(A_18, B_20))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.69/1.14  tff(c_38, plain, (![A_18, B_2, A_1]: (m1_subset_1(A_18, B_2) | ~r2_hidden(A_18, A_1) | ~r1_tarski(A_1, B_2))), inference(resolution, [status(thm)], [c_4, c_35])).
% 1.69/1.14  tff(c_48, plain, (![B_27, A_28, B_29]: (m1_subset_1(k1_funct_1(B_27, A_28), B_29) | ~r1_tarski(k2_relat_1(B_27), B_29) | ~r2_hidden(A_28, k1_relat_1(B_27)) | ~v1_funct_1(B_27) | ~v1_relat_1(B_27))), inference(resolution, [status(thm)], [c_44, c_38])).
% 1.69/1.14  tff(c_52, plain, (![B_30, A_31, A_32]: (m1_subset_1(k1_funct_1(B_30, A_31), A_32) | ~r2_hidden(A_31, k1_relat_1(B_30)) | ~v1_funct_1(B_30) | ~v5_relat_1(B_30, A_32) | ~v1_relat_1(B_30))), inference(resolution, [status(thm)], [c_10, c_48])).
% 1.69/1.14  tff(c_54, plain, (![A_32]: (m1_subset_1(k1_funct_1('#skF_3', '#skF_2'), A_32) | ~v1_funct_1('#skF_3') | ~v5_relat_1('#skF_3', A_32) | ~v1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_16, c_52])).
% 1.69/1.14  tff(c_58, plain, (![A_33]: (m1_subset_1(k1_funct_1('#skF_3', '#skF_2'), A_33) | ~v5_relat_1('#skF_3', A_33))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_18, c_54])).
% 1.69/1.14  tff(c_14, plain, (~m1_subset_1(k1_funct_1('#skF_3', '#skF_2'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_60])).
% 1.69/1.14  tff(c_68, plain, (~v5_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_58, c_14])).
% 1.69/1.14  tff(c_74, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_20, c_68])).
% 1.69/1.14  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.69/1.14  
% 1.69/1.14  Inference rules
% 1.69/1.14  ----------------------
% 1.69/1.14  #Ref     : 0
% 1.69/1.14  #Sup     : 10
% 1.69/1.14  #Fact    : 0
% 1.69/1.14  #Define  : 0
% 1.69/1.14  #Split   : 0
% 1.69/1.14  #Chain   : 0
% 1.69/1.14  #Close   : 0
% 1.69/1.14  
% 1.69/1.14  Ordering : KBO
% 1.69/1.14  
% 1.69/1.14  Simplification rules
% 1.69/1.14  ----------------------
% 1.69/1.14  #Subsume      : 0
% 1.69/1.14  #Demod        : 3
% 1.69/1.14  #Tautology    : 2
% 1.69/1.14  #SimpNegUnit  : 0
% 1.69/1.14  #BackRed      : 0
% 1.69/1.14  
% 1.69/1.14  #Partial instantiations: 0
% 1.69/1.14  #Strategies tried      : 1
% 1.69/1.14  
% 1.69/1.14  Timing (in seconds)
% 1.69/1.14  ----------------------
% 1.69/1.14  Preprocessing        : 0.26
% 1.69/1.14  Parsing              : 0.15
% 1.69/1.14  CNF conversion       : 0.02
% 1.69/1.14  Main loop            : 0.11
% 1.69/1.14  Inferencing          : 0.05
% 1.69/1.14  Reduction            : 0.03
% 1.69/1.14  Demodulation         : 0.02
% 1.69/1.14  BG Simplification    : 0.01
% 1.69/1.14  Subsumption          : 0.02
% 1.69/1.14  Abstraction          : 0.00
% 1.69/1.14  MUC search           : 0.00
% 1.69/1.14  Cooper               : 0.00
% 1.69/1.14  Total                : 0.40
% 1.69/1.14  Index Insertion      : 0.00
% 1.69/1.14  Index Deletion       : 0.00
% 1.69/1.14  Index Matching       : 0.00
% 1.69/1.14  BG Taut test         : 0.00
%------------------------------------------------------------------------------

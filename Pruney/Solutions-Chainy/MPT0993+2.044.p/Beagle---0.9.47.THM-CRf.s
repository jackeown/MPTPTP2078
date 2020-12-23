%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:13:48 EST 2020

% Result     : Theorem 1.65s
% Output     : CNFRefutation 1.65s
% Verified   : 
% Statistics : Number of formulae       :   36 (  43 expanded)
%              Number of leaves         :   21 (  26 expanded)
%              Depth                    :    6
%              Number of atoms          :   36 (  63 expanded)
%              Number of equality atoms :    7 (   7 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > r1_tarski > m1_subset_1 > v1_funct_1 > k5_relset_1 > k2_partfun1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k5_relset_1,type,(
    k5_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_relset_1,type,(
    r2_relset_1: ( $i * $i * $i * $i ) > $o )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_partfun1,type,(
    k2_partfun1: ( $i * $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_52,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( r1_tarski(A,C)
         => r2_relset_1(A,B,k2_partfun1(A,B,D,C),D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_funct_2)).

tff(f_29,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k5_relset_1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k5_relset_1)).

tff(f_35,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,A)))
     => ( r1_tarski(B,C)
       => r2_relset_1(B,A,k5_relset_1(B,A,D,C),D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_relset_1)).

tff(f_41,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => k2_partfun1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

tff(c_10,plain,(
    r1_tarski('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_12,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_17,plain,(
    ! [A_13,B_14,C_15,D_16] :
      ( k5_relset_1(A_13,B_14,C_15,D_16) = k7_relat_1(C_15,D_16)
      | ~ m1_subset_1(C_15,k1_zfmisc_1(k2_zfmisc_1(A_13,B_14))) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_20,plain,(
    ! [D_16] : k5_relset_1('#skF_1','#skF_2','#skF_4',D_16) = k7_relat_1('#skF_4',D_16) ),
    inference(resolution,[status(thm)],[c_12,c_17])).

tff(c_46,plain,(
    ! [B_23,A_24,D_25,C_26] :
      ( r2_relset_1(B_23,A_24,k5_relset_1(B_23,A_24,D_25,C_26),D_25)
      | ~ r1_tarski(B_23,C_26)
      | ~ m1_subset_1(D_25,k1_zfmisc_1(k2_zfmisc_1(B_23,A_24))) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_48,plain,(
    ! [C_26] :
      ( r2_relset_1('#skF_1','#skF_2',k5_relset_1('#skF_1','#skF_2','#skF_4',C_26),'#skF_4')
      | ~ r1_tarski('#skF_1',C_26) ) ),
    inference(resolution,[status(thm)],[c_12,c_46])).

tff(c_51,plain,(
    ! [C_27] :
      ( r2_relset_1('#skF_1','#skF_2',k7_relat_1('#skF_4',C_27),'#skF_4')
      | ~ r1_tarski('#skF_1',C_27) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_48])).

tff(c_16,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_30,plain,(
    ! [A_18,B_19,C_20,D_21] :
      ( k2_partfun1(A_18,B_19,C_20,D_21) = k7_relat_1(C_20,D_21)
      | ~ m1_subset_1(C_20,k1_zfmisc_1(k2_zfmisc_1(A_18,B_19)))
      | ~ v1_funct_1(C_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_32,plain,(
    ! [D_21] :
      ( k2_partfun1('#skF_1','#skF_2','#skF_4',D_21) = k7_relat_1('#skF_4',D_21)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_12,c_30])).

tff(c_35,plain,(
    ! [D_21] : k2_partfun1('#skF_1','#skF_2','#skF_4',D_21) = k7_relat_1('#skF_4',D_21) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_32])).

tff(c_8,plain,(
    ~ r2_relset_1('#skF_1','#skF_2',k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_36,plain,(
    ~ r2_relset_1('#skF_1','#skF_2',k7_relat_1('#skF_4','#skF_3'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_35,c_8])).

tff(c_54,plain,(
    ~ r1_tarski('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_51,c_36])).

tff(c_58,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_54])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:17:06 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.65/1.13  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.65/1.14  
% 1.65/1.14  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.65/1.14  %$ r2_relset_1 > v1_funct_2 > r1_tarski > m1_subset_1 > v1_funct_1 > k5_relset_1 > k2_partfun1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 1.65/1.14  
% 1.65/1.14  %Foreground sorts:
% 1.65/1.14  
% 1.65/1.14  
% 1.65/1.14  %Background operators:
% 1.65/1.14  
% 1.65/1.14  
% 1.65/1.14  %Foreground operators:
% 1.65/1.14  tff(k5_relset_1, type, k5_relset_1: ($i * $i * $i * $i) > $i).
% 1.65/1.14  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.65/1.14  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.65/1.14  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 1.65/1.14  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 1.65/1.14  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.65/1.14  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 1.65/1.14  tff('#skF_2', type, '#skF_2': $i).
% 1.65/1.14  tff('#skF_3', type, '#skF_3': $i).
% 1.65/1.14  tff('#skF_1', type, '#skF_1': $i).
% 1.65/1.14  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.65/1.14  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.65/1.14  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.65/1.14  tff('#skF_4', type, '#skF_4': $i).
% 1.65/1.14  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.65/1.14  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 1.65/1.14  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.65/1.14  
% 1.65/1.15  tff(f_52, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r1_tarski(A, C) => r2_relset_1(A, B, k2_partfun1(A, B, D, C), D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t40_funct_2)).
% 1.65/1.15  tff(f_29, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k5_relset_1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k5_relset_1)).
% 1.65/1.15  tff(f_35, axiom, (![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A))) => (r1_tarski(B, C) => r2_relset_1(B, A, k5_relset_1(B, A, D, C), D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t34_relset_1)).
% 1.65/1.15  tff(f_41, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k2_partfun1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 1.65/1.15  tff(c_10, plain, (r1_tarski('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.65/1.15  tff(c_12, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.65/1.15  tff(c_17, plain, (![A_13, B_14, C_15, D_16]: (k5_relset_1(A_13, B_14, C_15, D_16)=k7_relat_1(C_15, D_16) | ~m1_subset_1(C_15, k1_zfmisc_1(k2_zfmisc_1(A_13, B_14))))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.65/1.15  tff(c_20, plain, (![D_16]: (k5_relset_1('#skF_1', '#skF_2', '#skF_4', D_16)=k7_relat_1('#skF_4', D_16))), inference(resolution, [status(thm)], [c_12, c_17])).
% 1.65/1.15  tff(c_46, plain, (![B_23, A_24, D_25, C_26]: (r2_relset_1(B_23, A_24, k5_relset_1(B_23, A_24, D_25, C_26), D_25) | ~r1_tarski(B_23, C_26) | ~m1_subset_1(D_25, k1_zfmisc_1(k2_zfmisc_1(B_23, A_24))))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.65/1.15  tff(c_48, plain, (![C_26]: (r2_relset_1('#skF_1', '#skF_2', k5_relset_1('#skF_1', '#skF_2', '#skF_4', C_26), '#skF_4') | ~r1_tarski('#skF_1', C_26))), inference(resolution, [status(thm)], [c_12, c_46])).
% 1.65/1.15  tff(c_51, plain, (![C_27]: (r2_relset_1('#skF_1', '#skF_2', k7_relat_1('#skF_4', C_27), '#skF_4') | ~r1_tarski('#skF_1', C_27))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_48])).
% 1.65/1.15  tff(c_16, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.65/1.15  tff(c_30, plain, (![A_18, B_19, C_20, D_21]: (k2_partfun1(A_18, B_19, C_20, D_21)=k7_relat_1(C_20, D_21) | ~m1_subset_1(C_20, k1_zfmisc_1(k2_zfmisc_1(A_18, B_19))) | ~v1_funct_1(C_20))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.65/1.15  tff(c_32, plain, (![D_21]: (k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_21)=k7_relat_1('#skF_4', D_21) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_12, c_30])).
% 1.65/1.15  tff(c_35, plain, (![D_21]: (k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_21)=k7_relat_1('#skF_4', D_21))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_32])).
% 1.65/1.15  tff(c_8, plain, (~r2_relset_1('#skF_1', '#skF_2', k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.65/1.15  tff(c_36, plain, (~r2_relset_1('#skF_1', '#skF_2', k7_relat_1('#skF_4', '#skF_3'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_35, c_8])).
% 1.65/1.15  tff(c_54, plain, (~r1_tarski('#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_51, c_36])).
% 1.65/1.15  tff(c_58, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_10, c_54])).
% 1.65/1.15  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.65/1.15  
% 1.65/1.15  Inference rules
% 1.65/1.15  ----------------------
% 1.65/1.15  #Ref     : 0
% 1.65/1.15  #Sup     : 8
% 1.65/1.15  #Fact    : 0
% 1.65/1.15  #Define  : 0
% 1.65/1.15  #Split   : 0
% 1.65/1.15  #Chain   : 0
% 1.65/1.15  #Close   : 0
% 1.65/1.15  
% 1.65/1.15  Ordering : KBO
% 1.65/1.15  
% 1.65/1.15  Simplification rules
% 1.65/1.15  ----------------------
% 1.65/1.15  #Subsume      : 0
% 1.65/1.15  #Demod        : 4
% 1.65/1.15  #Tautology    : 4
% 1.65/1.15  #SimpNegUnit  : 0
% 1.65/1.15  #BackRed      : 1
% 1.65/1.15  
% 1.65/1.15  #Partial instantiations: 0
% 1.65/1.15  #Strategies tried      : 1
% 1.65/1.15  
% 1.65/1.15  Timing (in seconds)
% 1.65/1.15  ----------------------
% 1.65/1.15  Preprocessing        : 0.28
% 1.65/1.15  Parsing              : 0.15
% 1.65/1.15  CNF conversion       : 0.01
% 1.65/1.15  Main loop            : 0.08
% 1.65/1.15  Inferencing          : 0.04
% 1.65/1.15  Reduction            : 0.02
% 1.65/1.15  Demodulation         : 0.02
% 1.65/1.15  BG Simplification    : 0.01
% 1.65/1.15  Subsumption          : 0.01
% 1.65/1.15  Abstraction          : 0.01
% 1.65/1.15  MUC search           : 0.00
% 1.65/1.15  Cooper               : 0.00
% 1.65/1.15  Total                : 0.38
% 1.65/1.15  Index Insertion      : 0.00
% 1.65/1.15  Index Deletion       : 0.00
% 1.65/1.15  Index Matching       : 0.00
% 1.65/1.15  BG Taut test         : 0.00
%------------------------------------------------------------------------------

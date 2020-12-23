%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:07:42 EST 2020

% Result     : Theorem 2.12s
% Output     : CNFRefutation 2.12s
% Verified   : 
% Statistics : Number of formulae       :   37 (  47 expanded)
%              Number of leaves         :   21 (  26 expanded)
%              Depth                    :    8
%              Number of atoms          :   37 (  53 expanded)
%              Number of equality atoms :    3 (   6 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > v1_relat_1 > k6_relset_1 > k8_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k8_relat_1,type,(
    k8_relat_1: ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k6_relset_1,type,(
    k6_relset_1: ( $i * $i * $i * $i ) > $i )).

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

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_52,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(C,A)))
       => m1_subset_1(k6_relset_1(C,A,B,D),k1_zfmisc_1(k2_zfmisc_1(C,B))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_relset_1)).

tff(f_33,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k2_relat_1(k8_relat_1(A,B)),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t116_relat_1)).

tff(f_41,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k6_relset_1(A,B,C,D) = k8_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_relset_1)).

tff(f_37,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k6_relset_1(A,B,C,D),k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relset_1)).

tff(f_47,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(C,A)))
     => ( r1_tarski(k2_relat_1(D),B)
       => m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(C,B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_relset_1)).

tff(c_14,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_16,plain,(
    ! [C_20,A_21,B_22] :
      ( v1_relat_1(C_20)
      | ~ m1_subset_1(C_20,k1_zfmisc_1(k2_zfmisc_1(A_21,B_22))) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_20,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_14,c_16])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( r1_tarski(k2_relat_1(k8_relat_1(A_1,B_2)),A_1)
      | ~ v1_relat_1(B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_21,plain,(
    ! [A_23,B_24,C_25,D_26] :
      ( k6_relset_1(A_23,B_24,C_25,D_26) = k8_relat_1(C_25,D_26)
      | ~ m1_subset_1(D_26,k1_zfmisc_1(k2_zfmisc_1(A_23,B_24))) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_24,plain,(
    ! [C_25] : k6_relset_1('#skF_3','#skF_1',C_25,'#skF_4') = k8_relat_1(C_25,'#skF_4') ),
    inference(resolution,[status(thm)],[c_14,c_21])).

tff(c_35,plain,(
    ! [A_28,B_29,C_30,D_31] :
      ( m1_subset_1(k6_relset_1(A_28,B_29,C_30,D_31),k1_zfmisc_1(k2_zfmisc_1(A_28,B_29)))
      | ~ m1_subset_1(D_31,k1_zfmisc_1(k2_zfmisc_1(A_28,B_29))) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_43,plain,(
    ! [C_25] :
      ( m1_subset_1(k8_relat_1(C_25,'#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_1')))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_1'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_35])).

tff(c_47,plain,(
    ! [C_25] : m1_subset_1(k8_relat_1(C_25,'#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_43])).

tff(c_85,plain,(
    ! [D_44,C_45,B_46,A_47] :
      ( m1_subset_1(D_44,k1_zfmisc_1(k2_zfmisc_1(C_45,B_46)))
      | ~ r1_tarski(k2_relat_1(D_44),B_46)
      | ~ m1_subset_1(D_44,k1_zfmisc_1(k2_zfmisc_1(C_45,A_47))) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_128,plain,(
    ! [C_58,B_59] :
      ( m1_subset_1(k8_relat_1(C_58,'#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_59)))
      | ~ r1_tarski(k2_relat_1(k8_relat_1(C_58,'#skF_4')),B_59) ) ),
    inference(resolution,[status(thm)],[c_47,c_85])).

tff(c_12,plain,(
    ~ m1_subset_1(k6_relset_1('#skF_3','#skF_1','#skF_2','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_25,plain,(
    ~ m1_subset_1(k8_relat_1('#skF_2','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_12])).

tff(c_143,plain,(
    ~ r1_tarski(k2_relat_1(k8_relat_1('#skF_2','#skF_4')),'#skF_2') ),
    inference(resolution,[status(thm)],[c_128,c_25])).

tff(c_149,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_2,c_143])).

tff(c_153,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_149])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.13/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n024.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:14:51 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.12/1.34  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.12/1.35  
% 2.12/1.35  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.12/1.35  %$ r1_tarski > m1_subset_1 > v1_relat_1 > k6_relset_1 > k8_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.12/1.35  
% 2.12/1.35  %Foreground sorts:
% 2.12/1.35  
% 2.12/1.35  
% 2.12/1.35  %Background operators:
% 2.12/1.35  
% 2.12/1.35  
% 2.12/1.35  %Foreground operators:
% 2.12/1.35  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 2.12/1.35  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.12/1.35  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.12/1.35  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.12/1.35  tff(k6_relset_1, type, k6_relset_1: ($i * $i * $i * $i) > $i).
% 2.12/1.35  tff('#skF_2', type, '#skF_2': $i).
% 2.12/1.35  tff('#skF_3', type, '#skF_3': $i).
% 2.12/1.35  tff('#skF_1', type, '#skF_1': $i).
% 2.12/1.35  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.12/1.35  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.12/1.35  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.12/1.35  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.12/1.35  tff('#skF_4', type, '#skF_4': $i).
% 2.12/1.35  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.12/1.35  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.12/1.35  
% 2.12/1.36  tff(f_52, negated_conjecture, ~(![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(C, A))) => m1_subset_1(k6_relset_1(C, A, B, D), k1_zfmisc_1(k2_zfmisc_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_relset_1)).
% 2.12/1.36  tff(f_33, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.12/1.36  tff(f_29, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k2_relat_1(k8_relat_1(A, B)), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t116_relat_1)).
% 2.12/1.36  tff(f_41, axiom, (![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k6_relset_1(A, B, C, D) = k8_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_relset_1)).
% 2.12/1.36  tff(f_37, axiom, (![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k6_relset_1(A, B, C, D), k1_zfmisc_1(k2_zfmisc_1(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_relset_1)).
% 2.12/1.36  tff(f_47, axiom, (![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(C, A))) => (r1_tarski(k2_relat_1(D), B) => m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(C, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t14_relset_1)).
% 2.12/1.36  tff(c_14, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.12/1.36  tff(c_16, plain, (![C_20, A_21, B_22]: (v1_relat_1(C_20) | ~m1_subset_1(C_20, k1_zfmisc_1(k2_zfmisc_1(A_21, B_22))))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.12/1.36  tff(c_20, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_14, c_16])).
% 2.12/1.36  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(k2_relat_1(k8_relat_1(A_1, B_2)), A_1) | ~v1_relat_1(B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.12/1.36  tff(c_21, plain, (![A_23, B_24, C_25, D_26]: (k6_relset_1(A_23, B_24, C_25, D_26)=k8_relat_1(C_25, D_26) | ~m1_subset_1(D_26, k1_zfmisc_1(k2_zfmisc_1(A_23, B_24))))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.12/1.36  tff(c_24, plain, (![C_25]: (k6_relset_1('#skF_3', '#skF_1', C_25, '#skF_4')=k8_relat_1(C_25, '#skF_4'))), inference(resolution, [status(thm)], [c_14, c_21])).
% 2.12/1.36  tff(c_35, plain, (![A_28, B_29, C_30, D_31]: (m1_subset_1(k6_relset_1(A_28, B_29, C_30, D_31), k1_zfmisc_1(k2_zfmisc_1(A_28, B_29))) | ~m1_subset_1(D_31, k1_zfmisc_1(k2_zfmisc_1(A_28, B_29))))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.12/1.36  tff(c_43, plain, (![C_25]: (m1_subset_1(k8_relat_1(C_25, '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_1'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_1'))))), inference(superposition, [status(thm), theory('equality')], [c_24, c_35])).
% 2.12/1.36  tff(c_47, plain, (![C_25]: (m1_subset_1(k8_relat_1(C_25, '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_43])).
% 2.12/1.36  tff(c_85, plain, (![D_44, C_45, B_46, A_47]: (m1_subset_1(D_44, k1_zfmisc_1(k2_zfmisc_1(C_45, B_46))) | ~r1_tarski(k2_relat_1(D_44), B_46) | ~m1_subset_1(D_44, k1_zfmisc_1(k2_zfmisc_1(C_45, A_47))))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.12/1.36  tff(c_128, plain, (![C_58, B_59]: (m1_subset_1(k8_relat_1(C_58, '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_59))) | ~r1_tarski(k2_relat_1(k8_relat_1(C_58, '#skF_4')), B_59))), inference(resolution, [status(thm)], [c_47, c_85])).
% 2.12/1.36  tff(c_12, plain, (~m1_subset_1(k6_relset_1('#skF_3', '#skF_1', '#skF_2', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.12/1.36  tff(c_25, plain, (~m1_subset_1(k8_relat_1('#skF_2', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_12])).
% 2.12/1.36  tff(c_143, plain, (~r1_tarski(k2_relat_1(k8_relat_1('#skF_2', '#skF_4')), '#skF_2')), inference(resolution, [status(thm)], [c_128, c_25])).
% 2.12/1.36  tff(c_149, plain, (~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_2, c_143])).
% 2.12/1.36  tff(c_153, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_20, c_149])).
% 2.12/1.36  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.12/1.36  
% 2.12/1.36  Inference rules
% 2.12/1.36  ----------------------
% 2.12/1.36  #Ref     : 0
% 2.12/1.36  #Sup     : 32
% 2.12/1.36  #Fact    : 0
% 2.12/1.36  #Define  : 0
% 2.12/1.36  #Split   : 0
% 2.12/1.36  #Chain   : 0
% 2.12/1.36  #Close   : 0
% 2.12/1.36  
% 2.12/1.36  Ordering : KBO
% 2.12/1.36  
% 2.12/1.36  Simplification rules
% 2.12/1.36  ----------------------
% 2.12/1.36  #Subsume      : 2
% 2.12/1.36  #Demod        : 10
% 2.12/1.36  #Tautology    : 8
% 2.12/1.36  #SimpNegUnit  : 0
% 2.12/1.36  #BackRed      : 2
% 2.12/1.36  
% 2.12/1.36  #Partial instantiations: 0
% 2.12/1.36  #Strategies tried      : 1
% 2.12/1.36  
% 2.12/1.36  Timing (in seconds)
% 2.12/1.36  ----------------------
% 2.12/1.36  Preprocessing        : 0.38
% 2.12/1.36  Parsing              : 0.20
% 2.12/1.36  CNF conversion       : 0.02
% 2.12/1.36  Main loop            : 0.17
% 2.12/1.36  Inferencing          : 0.07
% 2.12/1.36  Reduction            : 0.05
% 2.12/1.36  Demodulation         : 0.04
% 2.12/1.36  BG Simplification    : 0.01
% 2.12/1.36  Subsumption          : 0.03
% 2.12/1.36  Abstraction          : 0.01
% 2.12/1.36  MUC search           : 0.00
% 2.12/1.36  Cooper               : 0.00
% 2.12/1.36  Total                : 0.57
% 2.12/1.36  Index Insertion      : 0.00
% 2.12/1.36  Index Deletion       : 0.00
% 2.12/1.36  Index Matching       : 0.00
% 2.12/1.36  BG Taut test         : 0.00
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:07:29 EST 2020

% Result     : Theorem 1.91s
% Output     : CNFRefutation 2.04s
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
%$ r1_tarski > m1_subset_1 > v1_relat_1 > k5_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k5_relset_1,type,(
    k5_relset_1: ( $i * $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_52,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,C)))
       => m1_subset_1(k5_relset_1(A,C,D,B),k1_zfmisc_1(k2_zfmisc_1(B,C))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_relset_1)).

tff(f_33,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k1_relat_1(k7_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_relat_1)).

tff(f_41,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k5_relset_1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k5_relset_1)).

tff(f_37,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k5_relset_1(A,B,C,D),k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relset_1)).

tff(f_47,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,C)))
     => ( r1_tarski(k1_relat_1(D),B)
       => m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,C))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_relset_1)).

tff(c_14,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3'))) ),
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
    ! [B_2,A_1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_2,A_1)),A_1)
      | ~ v1_relat_1(B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_21,plain,(
    ! [A_23,B_24,C_25,D_26] :
      ( k5_relset_1(A_23,B_24,C_25,D_26) = k7_relat_1(C_25,D_26)
      | ~ m1_subset_1(C_25,k1_zfmisc_1(k2_zfmisc_1(A_23,B_24))) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_24,plain,(
    ! [D_26] : k5_relset_1('#skF_1','#skF_3','#skF_4',D_26) = k7_relat_1('#skF_4',D_26) ),
    inference(resolution,[status(thm)],[c_14,c_21])).

tff(c_35,plain,(
    ! [A_28,B_29,C_30,D_31] :
      ( m1_subset_1(k5_relset_1(A_28,B_29,C_30,D_31),k1_zfmisc_1(k2_zfmisc_1(A_28,B_29)))
      | ~ m1_subset_1(C_30,k1_zfmisc_1(k2_zfmisc_1(A_28,B_29))) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_43,plain,(
    ! [D_26] :
      ( m1_subset_1(k7_relat_1('#skF_4',D_26),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3')))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_35])).

tff(c_47,plain,(
    ! [D_26] : m1_subset_1(k7_relat_1('#skF_4',D_26),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_43])).

tff(c_85,plain,(
    ! [D_44,B_45,C_46,A_47] :
      ( m1_subset_1(D_44,k1_zfmisc_1(k2_zfmisc_1(B_45,C_46)))
      | ~ r1_tarski(k1_relat_1(D_44),B_45)
      | ~ m1_subset_1(D_44,k1_zfmisc_1(k2_zfmisc_1(A_47,C_46))) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_128,plain,(
    ! [D_58,B_59] :
      ( m1_subset_1(k7_relat_1('#skF_4',D_58),k1_zfmisc_1(k2_zfmisc_1(B_59,'#skF_3')))
      | ~ r1_tarski(k1_relat_1(k7_relat_1('#skF_4',D_58)),B_59) ) ),
    inference(resolution,[status(thm)],[c_47,c_85])).

tff(c_12,plain,(
    ~ m1_subset_1(k5_relset_1('#skF_1','#skF_3','#skF_4','#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_25,plain,(
    ~ m1_subset_1(k7_relat_1('#skF_4','#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_12])).

tff(c_143,plain,(
    ~ r1_tarski(k1_relat_1(k7_relat_1('#skF_4','#skF_2')),'#skF_2') ),
    inference(resolution,[status(thm)],[c_128,c_25])).

tff(c_149,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_2,c_143])).

tff(c_153,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_149])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n010.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 13:46:14 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.18/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.91/1.21  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.91/1.21  
% 1.91/1.21  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.91/1.21  %$ r1_tarski > m1_subset_1 > v1_relat_1 > k5_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 1.91/1.21  
% 1.91/1.21  %Foreground sorts:
% 1.91/1.21  
% 1.91/1.21  
% 1.91/1.21  %Background operators:
% 1.91/1.21  
% 1.91/1.21  
% 1.91/1.21  %Foreground operators:
% 1.91/1.21  tff(k5_relset_1, type, k5_relset_1: ($i * $i * $i * $i) > $i).
% 1.91/1.21  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.91/1.21  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 1.91/1.21  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.91/1.21  tff('#skF_2', type, '#skF_2': $i).
% 1.91/1.21  tff('#skF_3', type, '#skF_3': $i).
% 1.91/1.21  tff('#skF_1', type, '#skF_1': $i).
% 1.91/1.21  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.91/1.21  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.91/1.21  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.91/1.21  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.91/1.21  tff('#skF_4', type, '#skF_4': $i).
% 1.91/1.21  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.91/1.21  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.91/1.21  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.91/1.21  
% 2.04/1.22  tff(f_52, negated_conjecture, ~(![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, C))) => m1_subset_1(k5_relset_1(A, C, D, B), k1_zfmisc_1(k2_zfmisc_1(B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t33_relset_1)).
% 2.04/1.22  tff(f_33, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.04/1.22  tff(f_29, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k7_relat_1(B, A)), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t87_relat_1)).
% 2.04/1.22  tff(f_41, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k5_relset_1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k5_relset_1)).
% 2.04/1.22  tff(f_37, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k5_relset_1(A, B, C, D), k1_zfmisc_1(k2_zfmisc_1(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k5_relset_1)).
% 2.04/1.22  tff(f_47, axiom, (![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, C))) => (r1_tarski(k1_relat_1(D), B) => m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t13_relset_1)).
% 2.04/1.22  tff(c_14, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.04/1.22  tff(c_16, plain, (![C_20, A_21, B_22]: (v1_relat_1(C_20) | ~m1_subset_1(C_20, k1_zfmisc_1(k2_zfmisc_1(A_21, B_22))))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.04/1.22  tff(c_20, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_14, c_16])).
% 2.04/1.22  tff(c_2, plain, (![B_2, A_1]: (r1_tarski(k1_relat_1(k7_relat_1(B_2, A_1)), A_1) | ~v1_relat_1(B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.04/1.22  tff(c_21, plain, (![A_23, B_24, C_25, D_26]: (k5_relset_1(A_23, B_24, C_25, D_26)=k7_relat_1(C_25, D_26) | ~m1_subset_1(C_25, k1_zfmisc_1(k2_zfmisc_1(A_23, B_24))))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.04/1.22  tff(c_24, plain, (![D_26]: (k5_relset_1('#skF_1', '#skF_3', '#skF_4', D_26)=k7_relat_1('#skF_4', D_26))), inference(resolution, [status(thm)], [c_14, c_21])).
% 2.04/1.22  tff(c_35, plain, (![A_28, B_29, C_30, D_31]: (m1_subset_1(k5_relset_1(A_28, B_29, C_30, D_31), k1_zfmisc_1(k2_zfmisc_1(A_28, B_29))) | ~m1_subset_1(C_30, k1_zfmisc_1(k2_zfmisc_1(A_28, B_29))))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.04/1.22  tff(c_43, plain, (![D_26]: (m1_subset_1(k7_relat_1('#skF_4', D_26), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3'))))), inference(superposition, [status(thm), theory('equality')], [c_24, c_35])).
% 2.04/1.22  tff(c_47, plain, (![D_26]: (m1_subset_1(k7_relat_1('#skF_4', D_26), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_43])).
% 2.04/1.22  tff(c_85, plain, (![D_44, B_45, C_46, A_47]: (m1_subset_1(D_44, k1_zfmisc_1(k2_zfmisc_1(B_45, C_46))) | ~r1_tarski(k1_relat_1(D_44), B_45) | ~m1_subset_1(D_44, k1_zfmisc_1(k2_zfmisc_1(A_47, C_46))))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.04/1.22  tff(c_128, plain, (![D_58, B_59]: (m1_subset_1(k7_relat_1('#skF_4', D_58), k1_zfmisc_1(k2_zfmisc_1(B_59, '#skF_3'))) | ~r1_tarski(k1_relat_1(k7_relat_1('#skF_4', D_58)), B_59))), inference(resolution, [status(thm)], [c_47, c_85])).
% 2.04/1.22  tff(c_12, plain, (~m1_subset_1(k5_relset_1('#skF_1', '#skF_3', '#skF_4', '#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.04/1.22  tff(c_25, plain, (~m1_subset_1(k7_relat_1('#skF_4', '#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_12])).
% 2.04/1.22  tff(c_143, plain, (~r1_tarski(k1_relat_1(k7_relat_1('#skF_4', '#skF_2')), '#skF_2')), inference(resolution, [status(thm)], [c_128, c_25])).
% 2.04/1.22  tff(c_149, plain, (~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_2, c_143])).
% 2.04/1.22  tff(c_153, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_20, c_149])).
% 2.04/1.22  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.04/1.22  
% 2.04/1.22  Inference rules
% 2.04/1.22  ----------------------
% 2.04/1.22  #Ref     : 0
% 2.04/1.22  #Sup     : 32
% 2.04/1.22  #Fact    : 0
% 2.04/1.22  #Define  : 0
% 2.04/1.22  #Split   : 0
% 2.04/1.22  #Chain   : 0
% 2.04/1.22  #Close   : 0
% 2.04/1.22  
% 2.04/1.22  Ordering : KBO
% 2.04/1.22  
% 2.04/1.22  Simplification rules
% 2.04/1.22  ----------------------
% 2.04/1.22  #Subsume      : 2
% 2.04/1.22  #Demod        : 10
% 2.04/1.22  #Tautology    : 8
% 2.04/1.22  #SimpNegUnit  : 0
% 2.04/1.22  #BackRed      : 2
% 2.04/1.22  
% 2.04/1.22  #Partial instantiations: 0
% 2.04/1.22  #Strategies tried      : 1
% 2.04/1.22  
% 2.04/1.22  Timing (in seconds)
% 2.04/1.22  ----------------------
% 2.04/1.22  Preprocessing        : 0.28
% 2.04/1.22  Parsing              : 0.15
% 2.04/1.22  CNF conversion       : 0.02
% 2.04/1.22  Main loop            : 0.15
% 2.04/1.22  Inferencing          : 0.06
% 2.04/1.22  Reduction            : 0.05
% 2.04/1.22  Demodulation         : 0.03
% 2.04/1.23  BG Simplification    : 0.01
% 2.04/1.23  Subsumption          : 0.02
% 2.04/1.23  Abstraction          : 0.01
% 2.04/1.23  MUC search           : 0.00
% 2.04/1.23  Cooper               : 0.00
% 2.04/1.23  Total                : 0.46
% 2.04/1.23  Index Insertion      : 0.00
% 2.04/1.23  Index Deletion       : 0.00
% 2.04/1.23  Index Matching       : 0.00
% 2.04/1.23  BG Taut test         : 0.00
%------------------------------------------------------------------------------

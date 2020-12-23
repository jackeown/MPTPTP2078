%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:06:57 EST 2020

% Result     : Theorem 1.81s
% Output     : CNFRefutation 1.81s
% Verified   : 
% Statistics : Number of formulae       :   34 (  43 expanded)
%              Number of leaves         :   21 (  26 expanded)
%              Depth                    :    5
%              Number of atoms          :   38 (  57 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

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

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_56,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(C,A)))
       => ( r1_tarski(k2_relat_1(D),B)
         => m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(C,B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_relset_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( ( r1_tarski(k1_relat_1(C),A)
          & r1_tarski(k2_relat_1(C),B) )
       => m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).

tff(c_18,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_19,plain,(
    ! [C_12,A_13,B_14] :
      ( v1_relat_1(C_12)
      | ~ m1_subset_1(C_12,k1_zfmisc_1(k2_zfmisc_1(A_13,B_14))) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_23,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_18,c_19])).

tff(c_29,plain,(
    ! [C_18,A_19,B_20] :
      ( v4_relat_1(C_18,A_19)
      | ~ m1_subset_1(C_18,k1_zfmisc_1(k2_zfmisc_1(A_19,B_20))) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_33,plain,(
    v4_relat_1('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_18,c_29])).

tff(c_4,plain,(
    ! [B_2,A_1] :
      ( r1_tarski(k1_relat_1(B_2),A_1)
      | ~ v4_relat_1(B_2,A_1)
      | ~ v1_relat_1(B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_16,plain,(
    r1_tarski(k2_relat_1('#skF_4'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_40,plain,(
    ! [C_25,A_26,B_27] :
      ( m1_subset_1(C_25,k1_zfmisc_1(k2_zfmisc_1(A_26,B_27)))
      | ~ r1_tarski(k2_relat_1(C_25),B_27)
      | ~ r1_tarski(k1_relat_1(C_25),A_26)
      | ~ v1_relat_1(C_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_14,plain,(
    ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_52,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_4'),'#skF_2')
    | ~ r1_tarski(k1_relat_1('#skF_4'),'#skF_3')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_40,c_14])).

tff(c_58,plain,(
    ~ r1_tarski(k1_relat_1('#skF_4'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_23,c_16,c_52])).

tff(c_61,plain,
    ( ~ v4_relat_1('#skF_4','#skF_3')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_4,c_58])).

tff(c_65,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_23,c_33,c_61])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.02/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.02/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.11/0.33  % Computer   : n012.cluster.edu
% 0.11/0.33  % Model      : x86_64 x86_64
% 0.11/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.33  % Memory     : 8042.1875MB
% 0.11/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.33  % CPULimit   : 60
% 0.11/0.33  % DateTime   : Tue Dec  1 13:22:37 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.11/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.81/1.24  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.81/1.25  
% 1.81/1.25  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.81/1.25  %$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 1.81/1.25  
% 1.81/1.25  %Foreground sorts:
% 1.81/1.25  
% 1.81/1.25  
% 1.81/1.25  %Background operators:
% 1.81/1.25  
% 1.81/1.25  
% 1.81/1.25  %Foreground operators:
% 1.81/1.25  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.81/1.25  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.81/1.25  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.81/1.25  tff('#skF_2', type, '#skF_2': $i).
% 1.81/1.25  tff('#skF_3', type, '#skF_3': $i).
% 1.81/1.25  tff('#skF_1', type, '#skF_1': $i).
% 1.81/1.25  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 1.81/1.25  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.81/1.25  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.81/1.25  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.81/1.25  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.81/1.25  tff('#skF_4', type, '#skF_4': $i).
% 1.81/1.25  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.81/1.25  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 1.81/1.25  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.81/1.25  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.81/1.25  
% 1.81/1.26  tff(f_56, negated_conjecture, ~(![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(C, A))) => (r1_tarski(k2_relat_1(D), B) => m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(C, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t14_relset_1)).
% 1.81/1.26  tff(f_35, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 1.81/1.26  tff(f_41, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 1.81/1.26  tff(f_31, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 1.81/1.26  tff(f_49, axiom, (![A, B, C]: (v1_relat_1(C) => ((r1_tarski(k1_relat_1(C), A) & r1_tarski(k2_relat_1(C), B)) => m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_relset_1)).
% 1.81/1.26  tff(c_18, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.81/1.26  tff(c_19, plain, (![C_12, A_13, B_14]: (v1_relat_1(C_12) | ~m1_subset_1(C_12, k1_zfmisc_1(k2_zfmisc_1(A_13, B_14))))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.81/1.26  tff(c_23, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_18, c_19])).
% 1.81/1.26  tff(c_29, plain, (![C_18, A_19, B_20]: (v4_relat_1(C_18, A_19) | ~m1_subset_1(C_18, k1_zfmisc_1(k2_zfmisc_1(A_19, B_20))))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.81/1.26  tff(c_33, plain, (v4_relat_1('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_18, c_29])).
% 1.81/1.26  tff(c_4, plain, (![B_2, A_1]: (r1_tarski(k1_relat_1(B_2), A_1) | ~v4_relat_1(B_2, A_1) | ~v1_relat_1(B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.81/1.26  tff(c_16, plain, (r1_tarski(k2_relat_1('#skF_4'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.81/1.26  tff(c_40, plain, (![C_25, A_26, B_27]: (m1_subset_1(C_25, k1_zfmisc_1(k2_zfmisc_1(A_26, B_27))) | ~r1_tarski(k2_relat_1(C_25), B_27) | ~r1_tarski(k1_relat_1(C_25), A_26) | ~v1_relat_1(C_25))), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.81/1.26  tff(c_14, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.81/1.26  tff(c_52, plain, (~r1_tarski(k2_relat_1('#skF_4'), '#skF_2') | ~r1_tarski(k1_relat_1('#skF_4'), '#skF_3') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_40, c_14])).
% 1.81/1.26  tff(c_58, plain, (~r1_tarski(k1_relat_1('#skF_4'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_23, c_16, c_52])).
% 1.81/1.26  tff(c_61, plain, (~v4_relat_1('#skF_4', '#skF_3') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_4, c_58])).
% 1.81/1.26  tff(c_65, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_23, c_33, c_61])).
% 1.81/1.26  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.81/1.26  
% 1.81/1.26  Inference rules
% 1.81/1.26  ----------------------
% 1.81/1.26  #Ref     : 0
% 1.81/1.26  #Sup     : 9
% 1.81/1.26  #Fact    : 0
% 1.81/1.26  #Define  : 0
% 1.81/1.26  #Split   : 0
% 1.81/1.26  #Chain   : 0
% 1.81/1.26  #Close   : 0
% 1.81/1.26  
% 1.81/1.26  Ordering : KBO
% 1.81/1.26  
% 1.81/1.26  Simplification rules
% 1.81/1.26  ----------------------
% 1.81/1.26  #Subsume      : 1
% 1.81/1.26  #Demod        : 4
% 1.81/1.26  #Tautology    : 2
% 1.81/1.26  #SimpNegUnit  : 0
% 1.81/1.26  #BackRed      : 0
% 1.81/1.26  
% 1.81/1.26  #Partial instantiations: 0
% 1.81/1.26  #Strategies tried      : 1
% 1.81/1.26  
% 1.81/1.26  Timing (in seconds)
% 1.81/1.26  ----------------------
% 1.81/1.26  Preprocessing        : 0.36
% 1.81/1.26  Parsing              : 0.21
% 1.81/1.26  CNF conversion       : 0.02
% 1.81/1.26  Main loop            : 0.10
% 1.81/1.26  Inferencing          : 0.05
% 1.81/1.26  Reduction            : 0.03
% 1.81/1.27  Demodulation         : 0.02
% 1.81/1.27  BG Simplification    : 0.01
% 1.81/1.27  Subsumption          : 0.02
% 1.81/1.27  Abstraction          : 0.00
% 1.81/1.27  MUC search           : 0.00
% 1.81/1.27  Cooper               : 0.00
% 1.81/1.27  Total                : 0.48
% 1.81/1.27  Index Insertion      : 0.00
% 1.81/1.27  Index Deletion       : 0.00
% 1.81/1.27  Index Matching       : 0.00
% 1.81/1.27  BG Taut test         : 0.00
%------------------------------------------------------------------------------

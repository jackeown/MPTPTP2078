%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:06:56 EST 2020

% Result     : Theorem 1.88s
% Output     : CNFRefutation 1.88s
% Verified   : 
% Statistics : Number of formulae       :   43 (  60 expanded)
%              Number of leaves         :   22 (  31 expanded)
%              Depth                    :    6
%              Number of atoms          :   60 (  92 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_49,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_66,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,C)))
       => ( r1_tarski(k1_relat_1(D),B)
         => m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,C))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_relset_1)).

tff(f_32,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_51,axiom,(
    ! [A,B] : r1_tarski(k2_relat_1(k2_zfmisc_1(A,B)),B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t194_relat_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(B))
         => v5_relat_1(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc6_relat_1)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( ( r1_tarski(k1_relat_1(C),A)
          & r1_tarski(k2_relat_1(C),B) )
       => m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_relset_1)).

tff(c_10,plain,(
    ! [A_10,B_11] : v1_relat_1(k2_zfmisc_1(A_10,B_11)) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_20,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_23,plain,(
    ! [B_21,A_22] :
      ( v1_relat_1(B_21)
      | ~ m1_subset_1(B_21,k1_zfmisc_1(A_22))
      | ~ v1_relat_1(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_26,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_3')) ),
    inference(resolution,[status(thm)],[c_20,c_23])).

tff(c_29,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_26])).

tff(c_12,plain,(
    ! [A_12,B_13] : r1_tarski(k2_relat_1(k2_zfmisc_1(A_12,B_13)),B_13) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_30,plain,(
    ! [B_23,A_24] :
      ( v5_relat_1(B_23,A_24)
      | ~ r1_tarski(k2_relat_1(B_23),A_24)
      | ~ v1_relat_1(B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_33,plain,(
    ! [A_12,B_13] :
      ( v5_relat_1(k2_zfmisc_1(A_12,B_13),B_13)
      | ~ v1_relat_1(k2_zfmisc_1(A_12,B_13)) ) ),
    inference(resolution,[status(thm)],[c_12,c_30])).

tff(c_36,plain,(
    ! [A_12,B_13] : v5_relat_1(k2_zfmisc_1(A_12,B_13),B_13) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_33])).

tff(c_43,plain,(
    ! [C_29,A_30,B_31] :
      ( v5_relat_1(C_29,A_30)
      | ~ m1_subset_1(C_29,k1_zfmisc_1(B_31))
      | ~ v5_relat_1(B_31,A_30)
      | ~ v1_relat_1(B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_45,plain,(
    ! [A_30] :
      ( v5_relat_1('#skF_4',A_30)
      | ~ v5_relat_1(k2_zfmisc_1('#skF_1','#skF_3'),A_30)
      | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_20,c_43])).

tff(c_49,plain,(
    ! [A_32] :
      ( v5_relat_1('#skF_4',A_32)
      | ~ v5_relat_1(k2_zfmisc_1('#skF_1','#skF_3'),A_32) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_45])).

tff(c_54,plain,(
    v5_relat_1('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_36,c_49])).

tff(c_8,plain,(
    ! [B_9,A_8] :
      ( r1_tarski(k2_relat_1(B_9),A_8)
      | ~ v5_relat_1(B_9,A_8)
      | ~ v1_relat_1(B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_18,plain,(
    r1_tarski(k1_relat_1('#skF_4'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_55,plain,(
    ! [C_33,A_34,B_35] :
      ( m1_subset_1(C_33,k1_zfmisc_1(k2_zfmisc_1(A_34,B_35)))
      | ~ r1_tarski(k2_relat_1(C_33),B_35)
      | ~ r1_tarski(k1_relat_1(C_33),A_34)
      | ~ v1_relat_1(C_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_16,plain,(
    ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_63,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_4'),'#skF_3')
    | ~ r1_tarski(k1_relat_1('#skF_4'),'#skF_2')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_55,c_16])).

tff(c_72,plain,(
    ~ r1_tarski(k2_relat_1('#skF_4'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_29,c_18,c_63])).

tff(c_75,plain,
    ( ~ v5_relat_1('#skF_4','#skF_3')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_8,c_72])).

tff(c_79,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_29,c_54,c_75])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n021.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:13:19 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.88/1.19  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.88/1.19  
% 1.88/1.19  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.88/1.19  %$ v5_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 1.88/1.19  
% 1.88/1.19  %Foreground sorts:
% 1.88/1.19  
% 1.88/1.19  
% 1.88/1.19  %Background operators:
% 1.88/1.19  
% 1.88/1.19  
% 1.88/1.19  %Foreground operators:
% 1.88/1.19  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.88/1.19  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.88/1.19  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.88/1.19  tff('#skF_2', type, '#skF_2': $i).
% 1.88/1.19  tff('#skF_3', type, '#skF_3': $i).
% 1.88/1.19  tff('#skF_1', type, '#skF_1': $i).
% 1.88/1.19  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 1.88/1.19  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.88/1.19  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.88/1.19  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.88/1.19  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.88/1.19  tff('#skF_4', type, '#skF_4': $i).
% 1.88/1.19  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.88/1.19  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.88/1.19  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.88/1.19  
% 1.88/1.21  tff(f_49, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 1.88/1.21  tff(f_66, negated_conjecture, ~(![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, C))) => (r1_tarski(k1_relat_1(D), B) => m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t13_relset_1)).
% 1.88/1.21  tff(f_32, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 1.88/1.21  tff(f_51, axiom, (![A, B]: r1_tarski(k2_relat_1(k2_zfmisc_1(A, B)), B)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t194_relat_1)).
% 1.88/1.21  tff(f_47, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 1.88/1.21  tff(f_41, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(B)) => v5_relat_1(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc6_relat_1)).
% 1.88/1.21  tff(f_59, axiom, (![A, B, C]: (v1_relat_1(C) => ((r1_tarski(k1_relat_1(C), A) & r1_tarski(k2_relat_1(C), B)) => m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_relset_1)).
% 1.88/1.21  tff(c_10, plain, (![A_10, B_11]: (v1_relat_1(k2_zfmisc_1(A_10, B_11)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.88/1.21  tff(c_20, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_66])).
% 1.88/1.21  tff(c_23, plain, (![B_21, A_22]: (v1_relat_1(B_21) | ~m1_subset_1(B_21, k1_zfmisc_1(A_22)) | ~v1_relat_1(A_22))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.88/1.21  tff(c_26, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_3'))), inference(resolution, [status(thm)], [c_20, c_23])).
% 1.88/1.21  tff(c_29, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_10, c_26])).
% 1.88/1.21  tff(c_12, plain, (![A_12, B_13]: (r1_tarski(k2_relat_1(k2_zfmisc_1(A_12, B_13)), B_13))), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.88/1.21  tff(c_30, plain, (![B_23, A_24]: (v5_relat_1(B_23, A_24) | ~r1_tarski(k2_relat_1(B_23), A_24) | ~v1_relat_1(B_23))), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.88/1.21  tff(c_33, plain, (![A_12, B_13]: (v5_relat_1(k2_zfmisc_1(A_12, B_13), B_13) | ~v1_relat_1(k2_zfmisc_1(A_12, B_13)))), inference(resolution, [status(thm)], [c_12, c_30])).
% 1.88/1.21  tff(c_36, plain, (![A_12, B_13]: (v5_relat_1(k2_zfmisc_1(A_12, B_13), B_13))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_33])).
% 1.88/1.21  tff(c_43, plain, (![C_29, A_30, B_31]: (v5_relat_1(C_29, A_30) | ~m1_subset_1(C_29, k1_zfmisc_1(B_31)) | ~v5_relat_1(B_31, A_30) | ~v1_relat_1(B_31))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.88/1.21  tff(c_45, plain, (![A_30]: (v5_relat_1('#skF_4', A_30) | ~v5_relat_1(k2_zfmisc_1('#skF_1', '#skF_3'), A_30) | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_3')))), inference(resolution, [status(thm)], [c_20, c_43])).
% 1.88/1.21  tff(c_49, plain, (![A_32]: (v5_relat_1('#skF_4', A_32) | ~v5_relat_1(k2_zfmisc_1('#skF_1', '#skF_3'), A_32))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_45])).
% 1.88/1.21  tff(c_54, plain, (v5_relat_1('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_36, c_49])).
% 1.88/1.21  tff(c_8, plain, (![B_9, A_8]: (r1_tarski(k2_relat_1(B_9), A_8) | ~v5_relat_1(B_9, A_8) | ~v1_relat_1(B_9))), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.88/1.21  tff(c_18, plain, (r1_tarski(k1_relat_1('#skF_4'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_66])).
% 1.88/1.21  tff(c_55, plain, (![C_33, A_34, B_35]: (m1_subset_1(C_33, k1_zfmisc_1(k2_zfmisc_1(A_34, B_35))) | ~r1_tarski(k2_relat_1(C_33), B_35) | ~r1_tarski(k1_relat_1(C_33), A_34) | ~v1_relat_1(C_33))), inference(cnfTransformation, [status(thm)], [f_59])).
% 1.88/1.21  tff(c_16, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_66])).
% 1.88/1.21  tff(c_63, plain, (~r1_tarski(k2_relat_1('#skF_4'), '#skF_3') | ~r1_tarski(k1_relat_1('#skF_4'), '#skF_2') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_55, c_16])).
% 1.88/1.21  tff(c_72, plain, (~r1_tarski(k2_relat_1('#skF_4'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_29, c_18, c_63])).
% 1.88/1.21  tff(c_75, plain, (~v5_relat_1('#skF_4', '#skF_3') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_8, c_72])).
% 1.88/1.21  tff(c_79, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_29, c_54, c_75])).
% 1.88/1.21  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.88/1.21  
% 1.88/1.21  Inference rules
% 1.88/1.21  ----------------------
% 1.88/1.21  #Ref     : 0
% 1.88/1.21  #Sup     : 9
% 1.88/1.21  #Fact    : 0
% 1.88/1.21  #Define  : 0
% 1.88/1.21  #Split   : 0
% 1.88/1.21  #Chain   : 0
% 1.88/1.21  #Close   : 0
% 1.88/1.21  
% 1.88/1.21  Ordering : KBO
% 1.88/1.21  
% 1.88/1.21  Simplification rules
% 1.88/1.21  ----------------------
% 1.88/1.21  #Subsume      : 0
% 1.88/1.21  #Demod        : 9
% 1.88/1.21  #Tautology    : 2
% 1.88/1.21  #SimpNegUnit  : 0
% 1.88/1.21  #BackRed      : 0
% 1.88/1.21  
% 1.88/1.21  #Partial instantiations: 0
% 1.88/1.21  #Strategies tried      : 1
% 1.88/1.21  
% 1.88/1.21  Timing (in seconds)
% 1.88/1.21  ----------------------
% 1.97/1.21  Preprocessing        : 0.29
% 1.97/1.21  Parsing              : 0.17
% 1.97/1.21  CNF conversion       : 0.02
% 1.97/1.21  Main loop            : 0.11
% 1.97/1.21  Inferencing          : 0.05
% 1.97/1.21  Reduction            : 0.03
% 1.97/1.21  Demodulation         : 0.03
% 1.97/1.21  BG Simplification    : 0.01
% 1.97/1.21  Subsumption          : 0.02
% 1.97/1.21  Abstraction          : 0.00
% 1.97/1.21  MUC search           : 0.00
% 1.97/1.21  Cooper               : 0.00
% 1.97/1.21  Total                : 0.44
% 1.97/1.21  Index Insertion      : 0.00
% 1.97/1.21  Index Deletion       : 0.00
% 1.97/1.21  Index Matching       : 0.00
% 1.97/1.21  BG Taut test         : 0.00
%------------------------------------------------------------------------------

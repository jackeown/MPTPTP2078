%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:16:43 EST 2020

% Result     : Theorem 1.98s
% Output     : CNFRefutation 1.98s
% Verified   : 
% Statistics : Number of formulae       :   44 (  60 expanded)
%              Number of leaves         :   24 (  33 expanded)
%              Depth                    :    9
%              Number of atoms          :   59 ( 117 expanded)
%              Number of equality atoms :    6 (  14 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_70,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( k1_relset_1(A,B,C) = A
         => ( v1_funct_1(C)
            & v1_funct_2(C,A,B)
            & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t130_funct_2)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r1_tarski(k2_relat_1(B),A)
       => ( v1_funct_1(B)
          & v1_funct_2(B,k1_relat_1(B),A)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B),A))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_funct_2)).

tff(c_24,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_38,plain,(
    ! [C_17,B_18,A_19] :
      ( v5_relat_1(C_17,B_18)
      | ~ m1_subset_1(C_17,k1_zfmisc_1(k2_zfmisc_1(A_19,B_18))) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_42,plain,(
    v5_relat_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_24,c_38])).

tff(c_33,plain,(
    ! [C_14,A_15,B_16] :
      ( v1_relat_1(C_14)
      | ~ m1_subset_1(C_14,k1_zfmisc_1(k2_zfmisc_1(A_15,B_16))) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_37,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_24,c_33])).

tff(c_4,plain,(
    ! [B_2,A_1] :
      ( r1_tarski(k2_relat_1(B_2),A_1)
      | ~ v5_relat_1(B_2,A_1)
      | ~ v1_relat_1(B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_26,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_22,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_54,plain,(
    ! [A_27,B_28,C_29] :
      ( k1_relset_1(A_27,B_28,C_29) = k1_relat_1(C_29)
      | ~ m1_subset_1(C_29,k1_zfmisc_1(k2_zfmisc_1(A_27,B_28))) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_57,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_24,c_54])).

tff(c_59,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_57])).

tff(c_64,plain,(
    ! [B_30,A_31] :
      ( v1_funct_2(B_30,k1_relat_1(B_30),A_31)
      | ~ r1_tarski(k2_relat_1(B_30),A_31)
      | ~ v1_funct_1(B_30)
      | ~ v1_relat_1(B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_67,plain,(
    ! [A_31] :
      ( v1_funct_2('#skF_3','#skF_1',A_31)
      | ~ r1_tarski(k2_relat_1('#skF_3'),A_31)
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_59,c_64])).

tff(c_92,plain,(
    ! [A_34] :
      ( v1_funct_2('#skF_3','#skF_1',A_34)
      | ~ r1_tarski(k2_relat_1('#skF_3'),A_34) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_37,c_26,c_67])).

tff(c_96,plain,(
    ! [A_1] :
      ( v1_funct_2('#skF_3','#skF_1',A_1)
      | ~ v5_relat_1('#skF_3',A_1)
      | ~ v1_relat_1('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_4,c_92])).

tff(c_100,plain,(
    ! [A_35] :
      ( v1_funct_2('#skF_3','#skF_1',A_35)
      | ~ v5_relat_1('#skF_3',A_35) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_37,c_96])).

tff(c_20,plain,
    ( ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_28,plain,(
    ~ v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_20])).

tff(c_103,plain,(
    ~ v5_relat_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_100,c_28])).

tff(c_107,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_103])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:06:38 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.98/1.24  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.98/1.24  
% 1.98/1.24  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.98/1.24  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 1.98/1.24  
% 1.98/1.24  %Foreground sorts:
% 1.98/1.24  
% 1.98/1.24  
% 1.98/1.24  %Background operators:
% 1.98/1.24  
% 1.98/1.24  
% 1.98/1.24  %Foreground operators:
% 1.98/1.24  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.98/1.24  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.98/1.24  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.98/1.24  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.98/1.24  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 1.98/1.24  tff('#skF_2', type, '#skF_2': $i).
% 1.98/1.24  tff('#skF_3', type, '#skF_3': $i).
% 1.98/1.24  tff('#skF_1', type, '#skF_1': $i).
% 1.98/1.24  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 1.98/1.24  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 1.98/1.24  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.98/1.24  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.98/1.24  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.98/1.24  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.98/1.24  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.98/1.24  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 1.98/1.24  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.98/1.24  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.98/1.24  
% 1.98/1.26  tff(f_70, negated_conjecture, ~(![A, B, C]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((k1_relset_1(A, B, C) = A) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t130_funct_2)).
% 1.98/1.26  tff(f_41, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 1.98/1.26  tff(f_35, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 1.98/1.26  tff(f_31, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 1.98/1.26  tff(f_45, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 1.98/1.26  tff(f_57, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(k2_relat_1(B), A) => ((v1_funct_1(B) & v1_funct_2(B, k1_relat_1(B), A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B), A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_funct_2)).
% 1.98/1.26  tff(c_24, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_70])).
% 1.98/1.26  tff(c_38, plain, (![C_17, B_18, A_19]: (v5_relat_1(C_17, B_18) | ~m1_subset_1(C_17, k1_zfmisc_1(k2_zfmisc_1(A_19, B_18))))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.98/1.26  tff(c_42, plain, (v5_relat_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_24, c_38])).
% 1.98/1.26  tff(c_33, plain, (![C_14, A_15, B_16]: (v1_relat_1(C_14) | ~m1_subset_1(C_14, k1_zfmisc_1(k2_zfmisc_1(A_15, B_16))))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.98/1.26  tff(c_37, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_24, c_33])).
% 1.98/1.26  tff(c_4, plain, (![B_2, A_1]: (r1_tarski(k2_relat_1(B_2), A_1) | ~v5_relat_1(B_2, A_1) | ~v1_relat_1(B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.98/1.26  tff(c_26, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_70])).
% 1.98/1.26  tff(c_22, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_1'), inference(cnfTransformation, [status(thm)], [f_70])).
% 1.98/1.26  tff(c_54, plain, (![A_27, B_28, C_29]: (k1_relset_1(A_27, B_28, C_29)=k1_relat_1(C_29) | ~m1_subset_1(C_29, k1_zfmisc_1(k2_zfmisc_1(A_27, B_28))))), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.98/1.26  tff(c_57, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_24, c_54])).
% 1.98/1.26  tff(c_59, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_22, c_57])).
% 1.98/1.26  tff(c_64, plain, (![B_30, A_31]: (v1_funct_2(B_30, k1_relat_1(B_30), A_31) | ~r1_tarski(k2_relat_1(B_30), A_31) | ~v1_funct_1(B_30) | ~v1_relat_1(B_30))), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.98/1.26  tff(c_67, plain, (![A_31]: (v1_funct_2('#skF_3', '#skF_1', A_31) | ~r1_tarski(k2_relat_1('#skF_3'), A_31) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_59, c_64])).
% 1.98/1.26  tff(c_92, plain, (![A_34]: (v1_funct_2('#skF_3', '#skF_1', A_34) | ~r1_tarski(k2_relat_1('#skF_3'), A_34))), inference(demodulation, [status(thm), theory('equality')], [c_37, c_26, c_67])).
% 1.98/1.26  tff(c_96, plain, (![A_1]: (v1_funct_2('#skF_3', '#skF_1', A_1) | ~v5_relat_1('#skF_3', A_1) | ~v1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_4, c_92])).
% 1.98/1.26  tff(c_100, plain, (![A_35]: (v1_funct_2('#skF_3', '#skF_1', A_35) | ~v5_relat_1('#skF_3', A_35))), inference(demodulation, [status(thm), theory('equality')], [c_37, c_96])).
% 1.98/1.26  tff(c_20, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_70])).
% 1.98/1.26  tff(c_28, plain, (~v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_24, c_20])).
% 1.98/1.26  tff(c_103, plain, (~v5_relat_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_100, c_28])).
% 1.98/1.26  tff(c_107, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42, c_103])).
% 1.98/1.26  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.98/1.26  
% 1.98/1.26  Inference rules
% 1.98/1.26  ----------------------
% 1.98/1.26  #Ref     : 0
% 1.98/1.26  #Sup     : 17
% 1.98/1.26  #Fact    : 0
% 1.98/1.26  #Define  : 0
% 1.98/1.26  #Split   : 0
% 1.98/1.26  #Chain   : 0
% 1.98/1.26  #Close   : 0
% 1.98/1.26  
% 1.98/1.26  Ordering : KBO
% 1.98/1.26  
% 1.98/1.26  Simplification rules
% 1.98/1.26  ----------------------
% 1.98/1.26  #Subsume      : 1
% 1.98/1.26  #Demod        : 9
% 1.98/1.26  #Tautology    : 7
% 1.98/1.26  #SimpNegUnit  : 0
% 1.98/1.26  #BackRed      : 0
% 1.98/1.26  
% 1.98/1.26  #Partial instantiations: 0
% 1.98/1.26  #Strategies tried      : 1
% 1.98/1.26  
% 1.98/1.26  Timing (in seconds)
% 1.98/1.26  ----------------------
% 1.98/1.26  Preprocessing        : 0.31
% 1.98/1.26  Parsing              : 0.17
% 1.98/1.26  CNF conversion       : 0.02
% 1.98/1.26  Main loop            : 0.12
% 1.98/1.26  Inferencing          : 0.05
% 1.98/1.26  Reduction            : 0.04
% 1.98/1.26  Demodulation         : 0.03
% 1.98/1.26  BG Simplification    : 0.01
% 1.98/1.26  Subsumption          : 0.02
% 1.98/1.26  Abstraction          : 0.01
% 1.98/1.26  MUC search           : 0.00
% 1.98/1.26  Cooper               : 0.00
% 1.98/1.26  Total                : 0.47
% 1.98/1.26  Index Insertion      : 0.00
% 1.98/1.26  Index Deletion       : 0.00
% 1.98/1.26  Index Matching       : 0.00
% 1.98/1.26  BG Taut test         : 0.00
%------------------------------------------------------------------------------

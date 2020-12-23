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
% DateTime   : Thu Dec  3 10:15:45 EST 2020

% Result     : Theorem 1.93s
% Output     : CNFRefutation 2.19s
% Verified   : 
% Statistics : Number of formulae       :   51 (  99 expanded)
%              Number of leaves         :   24 (  47 expanded)
%              Depth                    :    7
%              Number of atoms          :   76 ( 276 expanded)
%              Number of equality atoms :   10 (  36 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(v2_funct_2,type,(
    v2_funct_2: ( $i * $i ) > $o )).

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

tff(v3_funct_2,type,(
    v3_funct_2: ( $i * $i * $i ) > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_78,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_funct_1(B)
          & v1_funct_2(B,A,A)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
       => ( ( v2_funct_1(B)
            & k2_relset_1(A,A,B) = A )
         => ( v1_funct_1(B)
            & v1_funct_2(B,A,A)
            & v3_funct_2(B,A,A)
            & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_funct_2)).

tff(f_29,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ( v2_funct_2(B,A)
      <=> k2_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_funct_2)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( v1_funct_1(C)
          & v2_funct_1(C)
          & v2_funct_2(C,B) )
       => ( v1_funct_1(C)
          & v3_funct_2(C,A,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc3_funct_2)).

tff(c_28,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_26,plain,(
    v1_funct_2('#skF_2','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_24,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_18,plain,
    ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_30,plain,(
    ~ v3_funct_2('#skF_2','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_24,c_18])).

tff(c_22,plain,(
    v2_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_35,plain,(
    ! [C_15,A_16,B_17] :
      ( v1_relat_1(C_15)
      | ~ m1_subset_1(C_15,k1_zfmisc_1(k2_zfmisc_1(A_16,B_17))) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_39,plain,(
    v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_24,c_35])).

tff(c_45,plain,(
    ! [C_21,B_22,A_23] :
      ( v5_relat_1(C_21,B_22)
      | ~ m1_subset_1(C_21,k1_zfmisc_1(k2_zfmisc_1(A_23,B_22))) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_49,plain,(
    v5_relat_1('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_24,c_45])).

tff(c_20,plain,(
    k2_relset_1('#skF_1','#skF_1','#skF_2') = '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_59,plain,(
    ! [A_27,B_28,C_29] :
      ( k2_relset_1(A_27,B_28,C_29) = k2_relat_1(C_29)
      | ~ m1_subset_1(C_29,k1_zfmisc_1(k2_zfmisc_1(A_27,B_28))) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_62,plain,(
    k2_relset_1('#skF_1','#skF_1','#skF_2') = k2_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_24,c_59])).

tff(c_64,plain,(
    k2_relat_1('#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_62])).

tff(c_14,plain,(
    ! [B_14] :
      ( v2_funct_2(B_14,k2_relat_1(B_14))
      | ~ v5_relat_1(B_14,k2_relat_1(B_14))
      | ~ v1_relat_1(B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_68,plain,
    ( v2_funct_2('#skF_2',k2_relat_1('#skF_2'))
    | ~ v5_relat_1('#skF_2','#skF_1')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_64,c_14])).

tff(c_72,plain,(
    v2_funct_2('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_39,c_49,c_64,c_68])).

tff(c_51,plain,(
    ! [B_25,A_26] :
      ( k2_relat_1(B_25) = A_26
      | ~ v2_funct_2(B_25,A_26)
      | ~ v5_relat_1(B_25,A_26)
      | ~ v1_relat_1(B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_54,plain,
    ( k2_relat_1('#skF_2') = '#skF_1'
    | ~ v2_funct_2('#skF_2','#skF_1')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_49,c_51])).

tff(c_57,plain,
    ( k2_relat_1('#skF_2') = '#skF_1'
    | ~ v2_funct_2('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_39,c_54])).

tff(c_58,plain,(
    ~ v2_funct_2('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_57])).

tff(c_75,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_58])).

tff(c_77,plain,(
    v2_funct_2('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_57])).

tff(c_94,plain,(
    ! [C_33,A_34,B_35] :
      ( v3_funct_2(C_33,A_34,B_35)
      | ~ v2_funct_2(C_33,B_35)
      | ~ v2_funct_1(C_33)
      | ~ v1_funct_1(C_33)
      | ~ m1_subset_1(C_33,k1_zfmisc_1(k2_zfmisc_1(A_34,B_35))) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_97,plain,
    ( v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v2_funct_2('#skF_2','#skF_1')
    | ~ v2_funct_1('#skF_2')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_24,c_94])).

tff(c_100,plain,(
    v3_funct_2('#skF_2','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_22,c_77,c_97])).

tff(c_102,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_100])).
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
% 0.13/0.34  % DateTime   : Tue Dec  1 11:13:29 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.93/1.22  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.19/1.22  
% 2.19/1.22  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.19/1.23  %$ v3_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > #skF_2 > #skF_1
% 2.19/1.23  
% 2.19/1.23  %Foreground sorts:
% 2.19/1.23  
% 2.19/1.23  
% 2.19/1.23  %Background operators:
% 2.19/1.23  
% 2.19/1.23  
% 2.19/1.23  %Foreground operators:
% 2.19/1.23  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.19/1.23  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.19/1.23  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 2.19/1.23  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.19/1.23  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.19/1.23  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.19/1.23  tff('#skF_2', type, '#skF_2': $i).
% 2.19/1.23  tff('#skF_1', type, '#skF_1': $i).
% 2.19/1.23  tff(v2_funct_2, type, v2_funct_2: ($i * $i) > $o).
% 2.19/1.23  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.19/1.23  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.19/1.23  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.19/1.23  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.19/1.23  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.19/1.23  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.19/1.23  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.19/1.23  tff(v3_funct_2, type, v3_funct_2: ($i * $i * $i) > $o).
% 2.19/1.23  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.19/1.23  
% 2.19/1.24  tff(f_78, negated_conjecture, ~(![A, B]: (((v1_funct_1(B) & v1_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => ((v2_funct_1(B) & (k2_relset_1(A, A, B) = A)) => (((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_funct_2)).
% 2.19/1.24  tff(f_29, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.19/1.24  tff(f_35, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.19/1.24  tff(f_39, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 2.19/1.24  tff(f_59, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (v2_funct_2(B, A) <=> (k2_relat_1(B) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_funct_2)).
% 2.19/1.24  tff(f_51, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (((v1_funct_1(C) & v2_funct_1(C)) & v2_funct_2(C, B)) => (v1_funct_1(C) & v3_funct_2(C, A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc3_funct_2)).
% 2.19/1.24  tff(c_28, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.19/1.24  tff(c_26, plain, (v1_funct_2('#skF_2', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.19/1.24  tff(c_24, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.19/1.24  tff(c_18, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.19/1.24  tff(c_30, plain, (~v3_funct_2('#skF_2', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_24, c_18])).
% 2.19/1.24  tff(c_22, plain, (v2_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.19/1.24  tff(c_35, plain, (![C_15, A_16, B_17]: (v1_relat_1(C_15) | ~m1_subset_1(C_15, k1_zfmisc_1(k2_zfmisc_1(A_16, B_17))))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.19/1.24  tff(c_39, plain, (v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_24, c_35])).
% 2.19/1.24  tff(c_45, plain, (![C_21, B_22, A_23]: (v5_relat_1(C_21, B_22) | ~m1_subset_1(C_21, k1_zfmisc_1(k2_zfmisc_1(A_23, B_22))))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.19/1.24  tff(c_49, plain, (v5_relat_1('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_24, c_45])).
% 2.19/1.24  tff(c_20, plain, (k2_relset_1('#skF_1', '#skF_1', '#skF_2')='#skF_1'), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.19/1.24  tff(c_59, plain, (![A_27, B_28, C_29]: (k2_relset_1(A_27, B_28, C_29)=k2_relat_1(C_29) | ~m1_subset_1(C_29, k1_zfmisc_1(k2_zfmisc_1(A_27, B_28))))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.19/1.24  tff(c_62, plain, (k2_relset_1('#skF_1', '#skF_1', '#skF_2')=k2_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_24, c_59])).
% 2.19/1.24  tff(c_64, plain, (k2_relat_1('#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_20, c_62])).
% 2.19/1.24  tff(c_14, plain, (![B_14]: (v2_funct_2(B_14, k2_relat_1(B_14)) | ~v5_relat_1(B_14, k2_relat_1(B_14)) | ~v1_relat_1(B_14))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.19/1.24  tff(c_68, plain, (v2_funct_2('#skF_2', k2_relat_1('#skF_2')) | ~v5_relat_1('#skF_2', '#skF_1') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_64, c_14])).
% 2.19/1.24  tff(c_72, plain, (v2_funct_2('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_39, c_49, c_64, c_68])).
% 2.19/1.24  tff(c_51, plain, (![B_25, A_26]: (k2_relat_1(B_25)=A_26 | ~v2_funct_2(B_25, A_26) | ~v5_relat_1(B_25, A_26) | ~v1_relat_1(B_25))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.19/1.24  tff(c_54, plain, (k2_relat_1('#skF_2')='#skF_1' | ~v2_funct_2('#skF_2', '#skF_1') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_49, c_51])).
% 2.19/1.24  tff(c_57, plain, (k2_relat_1('#skF_2')='#skF_1' | ~v2_funct_2('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_39, c_54])).
% 2.19/1.24  tff(c_58, plain, (~v2_funct_2('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_57])).
% 2.19/1.24  tff(c_75, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_72, c_58])).
% 2.19/1.24  tff(c_77, plain, (v2_funct_2('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_57])).
% 2.19/1.24  tff(c_94, plain, (![C_33, A_34, B_35]: (v3_funct_2(C_33, A_34, B_35) | ~v2_funct_2(C_33, B_35) | ~v2_funct_1(C_33) | ~v1_funct_1(C_33) | ~m1_subset_1(C_33, k1_zfmisc_1(k2_zfmisc_1(A_34, B_35))))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.19/1.24  tff(c_97, plain, (v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v2_funct_2('#skF_2', '#skF_1') | ~v2_funct_1('#skF_2') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_24, c_94])).
% 2.19/1.24  tff(c_100, plain, (v3_funct_2('#skF_2', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_22, c_77, c_97])).
% 2.19/1.24  tff(c_102, plain, $false, inference(negUnitSimplification, [status(thm)], [c_30, c_100])).
% 2.19/1.24  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.19/1.24  
% 2.19/1.24  Inference rules
% 2.19/1.24  ----------------------
% 2.19/1.24  #Ref     : 0
% 2.19/1.24  #Sup     : 15
% 2.19/1.24  #Fact    : 0
% 2.19/1.24  #Define  : 0
% 2.19/1.24  #Split   : 1
% 2.19/1.24  #Chain   : 0
% 2.19/1.24  #Close   : 0
% 2.19/1.24  
% 2.19/1.24  Ordering : KBO
% 2.19/1.24  
% 2.19/1.24  Simplification rules
% 2.19/1.24  ----------------------
% 2.19/1.24  #Subsume      : 0
% 2.19/1.24  #Demod        : 18
% 2.19/1.24  #Tautology    : 9
% 2.19/1.24  #SimpNegUnit  : 1
% 2.19/1.24  #BackRed      : 0
% 2.19/1.24  
% 2.19/1.24  #Partial instantiations: 0
% 2.19/1.24  #Strategies tried      : 1
% 2.19/1.24  
% 2.19/1.24  Timing (in seconds)
% 2.19/1.24  ----------------------
% 2.19/1.24  Preprocessing        : 0.31
% 2.19/1.24  Parsing              : 0.17
% 2.19/1.24  CNF conversion       : 0.02
% 2.19/1.24  Main loop            : 0.12
% 2.19/1.24  Inferencing          : 0.04
% 2.19/1.24  Reduction            : 0.04
% 2.19/1.24  Demodulation         : 0.03
% 2.19/1.24  BG Simplification    : 0.01
% 2.19/1.24  Subsumption          : 0.01
% 2.19/1.24  Abstraction          : 0.01
% 2.19/1.24  MUC search           : 0.00
% 2.19/1.24  Cooper               : 0.00
% 2.19/1.24  Total                : 0.45
% 2.19/1.24  Index Insertion      : 0.00
% 2.19/1.24  Index Deletion       : 0.00
% 2.19/1.24  Index Matching       : 0.00
% 2.19/1.24  BG Taut test         : 0.00
%------------------------------------------------------------------------------

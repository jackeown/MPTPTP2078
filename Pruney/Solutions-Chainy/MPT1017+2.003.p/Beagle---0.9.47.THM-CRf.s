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

% Result     : Theorem 1.97s
% Output     : CNFRefutation 2.02s
% Verified   : 
% Statistics : Number of formulae       :   48 (  71 expanded)
%              Number of leaves         :   25 (  38 expanded)
%              Depth                    :    7
%              Number of atoms          :   70 ( 191 expanded)
%              Number of equality atoms :    7 (  24 expanded)
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

tff(f_83,negated_conjecture,(
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

tff(f_34,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_32,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_40,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_44,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ( v2_funct_2(B,A)
      <=> k2_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_funct_2)).

tff(f_56,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( v1_funct_1(C)
          & v2_funct_1(C)
          & v2_funct_2(C,B) )
       => ( v1_funct_1(C)
          & v3_funct_2(C,A,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc3_funct_2)).

tff(c_30,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_28,plain,(
    v1_funct_2('#skF_2','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_26,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_20,plain,
    ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_32,plain,(
    ~ v3_funct_2('#skF_2','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_26,c_20])).

tff(c_24,plain,(
    v2_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_4,plain,(
    ! [A_4,B_5] : v1_relat_1(k2_zfmisc_1(A_4,B_5)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_38,plain,(
    ! [B_19,A_20] :
      ( v1_relat_1(B_19)
      | ~ m1_subset_1(B_19,k1_zfmisc_1(A_20))
      | ~ v1_relat_1(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_41,plain,
    ( v1_relat_1('#skF_2')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_1')) ),
    inference(resolution,[status(thm)],[c_26,c_38])).

tff(c_44,plain,(
    v1_relat_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_41])).

tff(c_45,plain,(
    ! [C_21,B_22,A_23] :
      ( v5_relat_1(C_21,B_22)
      | ~ m1_subset_1(C_21,k1_zfmisc_1(k2_zfmisc_1(A_23,B_22))) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_49,plain,(
    v5_relat_1('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_26,c_45])).

tff(c_22,plain,(
    k2_relset_1('#skF_1','#skF_1','#skF_2') = '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_63,plain,(
    ! [A_30,B_31,C_32] :
      ( k2_relset_1(A_30,B_31,C_32) = k2_relat_1(C_32)
      | ~ m1_subset_1(C_32,k1_zfmisc_1(k2_zfmisc_1(A_30,B_31))) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_66,plain,(
    k2_relset_1('#skF_1','#skF_1','#skF_2') = k2_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_26,c_63])).

tff(c_68,plain,(
    k2_relat_1('#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_66])).

tff(c_16,plain,(
    ! [B_16] :
      ( v2_funct_2(B_16,k2_relat_1(B_16))
      | ~ v5_relat_1(B_16,k2_relat_1(B_16))
      | ~ v1_relat_1(B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_72,plain,
    ( v2_funct_2('#skF_2',k2_relat_1('#skF_2'))
    | ~ v5_relat_1('#skF_2','#skF_1')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_68,c_16])).

tff(c_76,plain,(
    v2_funct_2('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_49,c_68,c_72])).

tff(c_80,plain,(
    ! [C_33,A_34,B_35] :
      ( v3_funct_2(C_33,A_34,B_35)
      | ~ v2_funct_2(C_33,B_35)
      | ~ v2_funct_1(C_33)
      | ~ v1_funct_1(C_33)
      | ~ m1_subset_1(C_33,k1_zfmisc_1(k2_zfmisc_1(A_34,B_35))) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_83,plain,
    ( v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v2_funct_2('#skF_2','#skF_1')
    | ~ v2_funct_1('#skF_2')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_26,c_80])).

tff(c_86,plain,(
    v3_funct_2('#skF_2','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_24,c_76,c_83])).

tff(c_88,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_86])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:53:45 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.97/1.18  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.97/1.19  
% 1.97/1.19  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.97/1.19  %$ v3_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > #skF_2 > #skF_1
% 1.97/1.19  
% 1.97/1.19  %Foreground sorts:
% 1.97/1.19  
% 1.97/1.19  
% 1.97/1.19  %Background operators:
% 1.97/1.19  
% 1.97/1.19  
% 1.97/1.19  %Foreground operators:
% 1.97/1.19  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 1.97/1.19  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.97/1.19  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 1.97/1.19  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.97/1.19  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.97/1.19  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 1.97/1.19  tff('#skF_2', type, '#skF_2': $i).
% 1.97/1.19  tff('#skF_1', type, '#skF_1': $i).
% 1.97/1.19  tff(v2_funct_2, type, v2_funct_2: ($i * $i) > $o).
% 1.97/1.19  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 1.97/1.19  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.97/1.19  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.97/1.19  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.97/1.19  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.97/1.19  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.97/1.19  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 1.97/1.19  tff(v3_funct_2, type, v3_funct_2: ($i * $i * $i) > $o).
% 1.97/1.19  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.97/1.19  
% 2.02/1.20  tff(f_83, negated_conjecture, ~(![A, B]: (((v1_funct_1(B) & v1_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => ((v2_funct_1(B) & (k2_relset_1(A, A, B) = A)) => (((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_funct_2)).
% 2.02/1.20  tff(f_34, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.02/1.20  tff(f_32, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.02/1.20  tff(f_40, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.02/1.20  tff(f_44, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 2.02/1.20  tff(f_64, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (v2_funct_2(B, A) <=> (k2_relat_1(B) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_funct_2)).
% 2.02/1.20  tff(f_56, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (((v1_funct_1(C) & v2_funct_1(C)) & v2_funct_2(C, B)) => (v1_funct_1(C) & v3_funct_2(C, A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc3_funct_2)).
% 2.02/1.20  tff(c_30, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.02/1.20  tff(c_28, plain, (v1_funct_2('#skF_2', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.02/1.20  tff(c_26, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.02/1.20  tff(c_20, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.02/1.20  tff(c_32, plain, (~v3_funct_2('#skF_2', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_26, c_20])).
% 2.02/1.20  tff(c_24, plain, (v2_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.02/1.20  tff(c_4, plain, (![A_4, B_5]: (v1_relat_1(k2_zfmisc_1(A_4, B_5)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.02/1.20  tff(c_38, plain, (![B_19, A_20]: (v1_relat_1(B_19) | ~m1_subset_1(B_19, k1_zfmisc_1(A_20)) | ~v1_relat_1(A_20))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.02/1.20  tff(c_41, plain, (v1_relat_1('#skF_2') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_1'))), inference(resolution, [status(thm)], [c_26, c_38])).
% 2.02/1.20  tff(c_44, plain, (v1_relat_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_41])).
% 2.02/1.20  tff(c_45, plain, (![C_21, B_22, A_23]: (v5_relat_1(C_21, B_22) | ~m1_subset_1(C_21, k1_zfmisc_1(k2_zfmisc_1(A_23, B_22))))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.02/1.20  tff(c_49, plain, (v5_relat_1('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_26, c_45])).
% 2.02/1.20  tff(c_22, plain, (k2_relset_1('#skF_1', '#skF_1', '#skF_2')='#skF_1'), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.02/1.20  tff(c_63, plain, (![A_30, B_31, C_32]: (k2_relset_1(A_30, B_31, C_32)=k2_relat_1(C_32) | ~m1_subset_1(C_32, k1_zfmisc_1(k2_zfmisc_1(A_30, B_31))))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.02/1.20  tff(c_66, plain, (k2_relset_1('#skF_1', '#skF_1', '#skF_2')=k2_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_26, c_63])).
% 2.02/1.20  tff(c_68, plain, (k2_relat_1('#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_22, c_66])).
% 2.02/1.20  tff(c_16, plain, (![B_16]: (v2_funct_2(B_16, k2_relat_1(B_16)) | ~v5_relat_1(B_16, k2_relat_1(B_16)) | ~v1_relat_1(B_16))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.02/1.20  tff(c_72, plain, (v2_funct_2('#skF_2', k2_relat_1('#skF_2')) | ~v5_relat_1('#skF_2', '#skF_1') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_68, c_16])).
% 2.02/1.20  tff(c_76, plain, (v2_funct_2('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_49, c_68, c_72])).
% 2.02/1.20  tff(c_80, plain, (![C_33, A_34, B_35]: (v3_funct_2(C_33, A_34, B_35) | ~v2_funct_2(C_33, B_35) | ~v2_funct_1(C_33) | ~v1_funct_1(C_33) | ~m1_subset_1(C_33, k1_zfmisc_1(k2_zfmisc_1(A_34, B_35))))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.02/1.20  tff(c_83, plain, (v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v2_funct_2('#skF_2', '#skF_1') | ~v2_funct_1('#skF_2') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_26, c_80])).
% 2.02/1.20  tff(c_86, plain, (v3_funct_2('#skF_2', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_24, c_76, c_83])).
% 2.02/1.20  tff(c_88, plain, $false, inference(negUnitSimplification, [status(thm)], [c_32, c_86])).
% 2.02/1.20  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.02/1.20  
% 2.02/1.20  Inference rules
% 2.02/1.20  ----------------------
% 2.02/1.20  #Ref     : 0
% 2.02/1.20  #Sup     : 11
% 2.02/1.20  #Fact    : 0
% 2.02/1.20  #Define  : 0
% 2.02/1.20  #Split   : 0
% 2.02/1.20  #Chain   : 0
% 2.02/1.20  #Close   : 0
% 2.02/1.20  
% 2.02/1.20  Ordering : KBO
% 2.02/1.20  
% 2.02/1.20  Simplification rules
% 2.02/1.20  ----------------------
% 2.02/1.20  #Subsume      : 0
% 2.02/1.20  #Demod        : 14
% 2.02/1.20  #Tautology    : 6
% 2.02/1.20  #SimpNegUnit  : 1
% 2.02/1.20  #BackRed      : 0
% 2.02/1.20  
% 2.02/1.20  #Partial instantiations: 0
% 2.02/1.20  #Strategies tried      : 1
% 2.02/1.20  
% 2.02/1.20  Timing (in seconds)
% 2.02/1.20  ----------------------
% 2.02/1.21  Preprocessing        : 0.32
% 2.02/1.21  Parsing              : 0.17
% 2.02/1.21  CNF conversion       : 0.02
% 2.02/1.21  Main loop            : 0.11
% 2.02/1.21  Inferencing          : 0.04
% 2.02/1.21  Reduction            : 0.04
% 2.02/1.21  Demodulation         : 0.03
% 2.02/1.21  BG Simplification    : 0.01
% 2.02/1.21  Subsumption          : 0.01
% 2.02/1.21  Abstraction          : 0.01
% 2.02/1.21  MUC search           : 0.00
% 2.02/1.21  Cooper               : 0.00
% 2.02/1.21  Total                : 0.46
% 2.02/1.21  Index Insertion      : 0.00
% 2.02/1.21  Index Deletion       : 0.00
% 2.02/1.21  Index Matching       : 0.00
% 2.02/1.21  BG Taut test         : 0.00
%------------------------------------------------------------------------------

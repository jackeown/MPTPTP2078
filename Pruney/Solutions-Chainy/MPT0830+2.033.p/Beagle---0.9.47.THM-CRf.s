%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:07:30 EST 2020

% Result     : Theorem 2.27s
% Output     : CNFRefutation 2.63s
% Verified   : 
% Statistics : Number of formulae       :   52 (  78 expanded)
%              Number of leaves         :   26 (  38 expanded)
%              Depth                    :    8
%              Number of atoms          :   69 ( 116 expanded)
%              Number of equality atoms :    3 (   6 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k5_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(f_50,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_75,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,C)))
       => m1_subset_1(k5_relset_1(A,C,D,B),k1_zfmisc_1(k2_zfmisc_1(B,C))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_relset_1)).

tff(f_32,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_56,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_48,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v4_relat_1(C,B) )
     => ( v1_relat_1(k7_relat_1(C,A))
        & v4_relat_1(k7_relat_1(C,A),A)
        & v4_relat_1(k7_relat_1(C,A),B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc23_relat_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_64,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k5_relset_1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k5_relset_1)).

tff(f_60,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k5_relset_1(A,B,C,D),k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relset_1)).

tff(f_70,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,C)))
     => ( r1_tarski(k1_relat_1(D),B)
       => m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,C))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_relset_1)).

tff(c_14,plain,(
    ! [A_9,B_10] : v1_relat_1(k2_zfmisc_1(A_9,B_10)) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_28,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_30,plain,(
    ! [B_28,A_29] :
      ( v1_relat_1(B_28)
      | ~ m1_subset_1(B_28,k1_zfmisc_1(A_29))
      | ~ v1_relat_1(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_33,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_3')) ),
    inference(resolution,[status(thm)],[c_28,c_30])).

tff(c_36,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_33])).

tff(c_39,plain,(
    ! [C_35,A_36,B_37] :
      ( v4_relat_1(C_35,A_36)
      | ~ m1_subset_1(C_35,k1_zfmisc_1(k2_zfmisc_1(A_36,B_37))) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_43,plain,(
    v4_relat_1('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_28,c_39])).

tff(c_12,plain,(
    ! [C_8,A_6,B_7] :
      ( v1_relat_1(k7_relat_1(C_8,A_6))
      | ~ v4_relat_1(C_8,B_7)
      | ~ v1_relat_1(C_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_45,plain,(
    ! [A_6] :
      ( v1_relat_1(k7_relat_1('#skF_4',A_6))
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_43,c_12])).

tff(c_48,plain,(
    ! [A_6] : v1_relat_1(k7_relat_1('#skF_4',A_6)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_45])).

tff(c_64,plain,(
    ! [C_47,A_48,B_49] :
      ( v4_relat_1(k7_relat_1(C_47,A_48),A_48)
      | ~ v4_relat_1(C_47,B_49)
      | ~ v1_relat_1(C_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_68,plain,(
    ! [A_48] :
      ( v4_relat_1(k7_relat_1('#skF_4',A_48),A_48)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_43,c_64])).

tff(c_72,plain,(
    ! [A_48] : v4_relat_1(k7_relat_1('#skF_4',A_48),A_48) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_68])).

tff(c_6,plain,(
    ! [B_5,A_4] :
      ( r1_tarski(k1_relat_1(B_5),A_4)
      | ~ v4_relat_1(B_5,A_4)
      | ~ v1_relat_1(B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_73,plain,(
    ! [A_50,B_51,C_52,D_53] :
      ( k5_relset_1(A_50,B_51,C_52,D_53) = k7_relat_1(C_52,D_53)
      | ~ m1_subset_1(C_52,k1_zfmisc_1(k2_zfmisc_1(A_50,B_51))) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_76,plain,(
    ! [D_53] : k5_relset_1('#skF_1','#skF_3','#skF_4',D_53) = k7_relat_1('#skF_4',D_53) ),
    inference(resolution,[status(thm)],[c_28,c_73])).

tff(c_134,plain,(
    ! [A_74,B_75,C_76,D_77] :
      ( m1_subset_1(k5_relset_1(A_74,B_75,C_76,D_77),k1_zfmisc_1(k2_zfmisc_1(A_74,B_75)))
      | ~ m1_subset_1(C_76,k1_zfmisc_1(k2_zfmisc_1(A_74,B_75))) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_148,plain,(
    ! [D_53] :
      ( m1_subset_1(k7_relat_1('#skF_4',D_53),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3')))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_76,c_134])).

tff(c_156,plain,(
    ! [D_53] : m1_subset_1(k7_relat_1('#skF_4',D_53),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_148])).

tff(c_247,plain,(
    ! [D_96,B_97,C_98,A_99] :
      ( m1_subset_1(D_96,k1_zfmisc_1(k2_zfmisc_1(B_97,C_98)))
      | ~ r1_tarski(k1_relat_1(D_96),B_97)
      | ~ m1_subset_1(D_96,k1_zfmisc_1(k2_zfmisc_1(A_99,C_98))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_412,plain,(
    ! [D_149,B_150] :
      ( m1_subset_1(k7_relat_1('#skF_4',D_149),k1_zfmisc_1(k2_zfmisc_1(B_150,'#skF_3')))
      | ~ r1_tarski(k1_relat_1(k7_relat_1('#skF_4',D_149)),B_150) ) ),
    inference(resolution,[status(thm)],[c_156,c_247])).

tff(c_26,plain,(
    ~ m1_subset_1(k5_relset_1('#skF_1','#skF_3','#skF_4','#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_100,plain,(
    ~ m1_subset_1(k7_relat_1('#skF_4','#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_26])).

tff(c_439,plain,(
    ~ r1_tarski(k1_relat_1(k7_relat_1('#skF_4','#skF_2')),'#skF_2') ),
    inference(resolution,[status(thm)],[c_412,c_100])).

tff(c_449,plain,
    ( ~ v4_relat_1(k7_relat_1('#skF_4','#skF_2'),'#skF_2')
    | ~ v1_relat_1(k7_relat_1('#skF_4','#skF_2')) ),
    inference(resolution,[status(thm)],[c_6,c_439])).

tff(c_453,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_72,c_449])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:47:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.27/1.37  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.27/1.38  
% 2.27/1.38  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.27/1.38  %$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k5_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.27/1.38  
% 2.27/1.38  %Foreground sorts:
% 2.27/1.38  
% 2.27/1.38  
% 2.27/1.38  %Background operators:
% 2.27/1.38  
% 2.27/1.38  
% 2.27/1.38  %Foreground operators:
% 2.27/1.38  tff(k5_relset_1, type, k5_relset_1: ($i * $i * $i * $i) > $i).
% 2.27/1.38  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.27/1.38  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.27/1.38  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.27/1.38  tff('#skF_2', type, '#skF_2': $i).
% 2.27/1.38  tff('#skF_3', type, '#skF_3': $i).
% 2.27/1.38  tff('#skF_1', type, '#skF_1': $i).
% 2.27/1.38  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.27/1.38  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.27/1.38  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.27/1.38  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.27/1.38  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.27/1.38  tff('#skF_4', type, '#skF_4': $i).
% 2.27/1.38  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.27/1.38  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.27/1.38  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.27/1.38  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.27/1.38  
% 2.63/1.39  tff(f_50, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.63/1.39  tff(f_75, negated_conjecture, ~(![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, C))) => m1_subset_1(k5_relset_1(A, C, D, B), k1_zfmisc_1(k2_zfmisc_1(B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t33_relset_1)).
% 2.63/1.39  tff(f_32, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.63/1.39  tff(f_56, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.63/1.39  tff(f_48, axiom, (![A, B, C]: ((v1_relat_1(C) & v4_relat_1(C, B)) => ((v1_relat_1(k7_relat_1(C, A)) & v4_relat_1(k7_relat_1(C, A), A)) & v4_relat_1(k7_relat_1(C, A), B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc23_relat_1)).
% 2.63/1.39  tff(f_38, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 2.63/1.39  tff(f_64, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k5_relset_1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k5_relset_1)).
% 2.63/1.39  tff(f_60, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k5_relset_1(A, B, C, D), k1_zfmisc_1(k2_zfmisc_1(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k5_relset_1)).
% 2.63/1.39  tff(f_70, axiom, (![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, C))) => (r1_tarski(k1_relat_1(D), B) => m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t13_relset_1)).
% 2.63/1.39  tff(c_14, plain, (![A_9, B_10]: (v1_relat_1(k2_zfmisc_1(A_9, B_10)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.63/1.39  tff(c_28, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.63/1.39  tff(c_30, plain, (![B_28, A_29]: (v1_relat_1(B_28) | ~m1_subset_1(B_28, k1_zfmisc_1(A_29)) | ~v1_relat_1(A_29))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.63/1.39  tff(c_33, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_3'))), inference(resolution, [status(thm)], [c_28, c_30])).
% 2.63/1.39  tff(c_36, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_14, c_33])).
% 2.63/1.39  tff(c_39, plain, (![C_35, A_36, B_37]: (v4_relat_1(C_35, A_36) | ~m1_subset_1(C_35, k1_zfmisc_1(k2_zfmisc_1(A_36, B_37))))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.63/1.39  tff(c_43, plain, (v4_relat_1('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_28, c_39])).
% 2.63/1.39  tff(c_12, plain, (![C_8, A_6, B_7]: (v1_relat_1(k7_relat_1(C_8, A_6)) | ~v4_relat_1(C_8, B_7) | ~v1_relat_1(C_8))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.63/1.39  tff(c_45, plain, (![A_6]: (v1_relat_1(k7_relat_1('#skF_4', A_6)) | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_43, c_12])).
% 2.63/1.39  tff(c_48, plain, (![A_6]: (v1_relat_1(k7_relat_1('#skF_4', A_6)))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_45])).
% 2.63/1.39  tff(c_64, plain, (![C_47, A_48, B_49]: (v4_relat_1(k7_relat_1(C_47, A_48), A_48) | ~v4_relat_1(C_47, B_49) | ~v1_relat_1(C_47))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.63/1.39  tff(c_68, plain, (![A_48]: (v4_relat_1(k7_relat_1('#skF_4', A_48), A_48) | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_43, c_64])).
% 2.63/1.39  tff(c_72, plain, (![A_48]: (v4_relat_1(k7_relat_1('#skF_4', A_48), A_48))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_68])).
% 2.63/1.39  tff(c_6, plain, (![B_5, A_4]: (r1_tarski(k1_relat_1(B_5), A_4) | ~v4_relat_1(B_5, A_4) | ~v1_relat_1(B_5))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.63/1.39  tff(c_73, plain, (![A_50, B_51, C_52, D_53]: (k5_relset_1(A_50, B_51, C_52, D_53)=k7_relat_1(C_52, D_53) | ~m1_subset_1(C_52, k1_zfmisc_1(k2_zfmisc_1(A_50, B_51))))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.63/1.39  tff(c_76, plain, (![D_53]: (k5_relset_1('#skF_1', '#skF_3', '#skF_4', D_53)=k7_relat_1('#skF_4', D_53))), inference(resolution, [status(thm)], [c_28, c_73])).
% 2.63/1.39  tff(c_134, plain, (![A_74, B_75, C_76, D_77]: (m1_subset_1(k5_relset_1(A_74, B_75, C_76, D_77), k1_zfmisc_1(k2_zfmisc_1(A_74, B_75))) | ~m1_subset_1(C_76, k1_zfmisc_1(k2_zfmisc_1(A_74, B_75))))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.63/1.39  tff(c_148, plain, (![D_53]: (m1_subset_1(k7_relat_1('#skF_4', D_53), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3'))))), inference(superposition, [status(thm), theory('equality')], [c_76, c_134])).
% 2.63/1.39  tff(c_156, plain, (![D_53]: (m1_subset_1(k7_relat_1('#skF_4', D_53), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_148])).
% 2.63/1.39  tff(c_247, plain, (![D_96, B_97, C_98, A_99]: (m1_subset_1(D_96, k1_zfmisc_1(k2_zfmisc_1(B_97, C_98))) | ~r1_tarski(k1_relat_1(D_96), B_97) | ~m1_subset_1(D_96, k1_zfmisc_1(k2_zfmisc_1(A_99, C_98))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.63/1.39  tff(c_412, plain, (![D_149, B_150]: (m1_subset_1(k7_relat_1('#skF_4', D_149), k1_zfmisc_1(k2_zfmisc_1(B_150, '#skF_3'))) | ~r1_tarski(k1_relat_1(k7_relat_1('#skF_4', D_149)), B_150))), inference(resolution, [status(thm)], [c_156, c_247])).
% 2.63/1.39  tff(c_26, plain, (~m1_subset_1(k5_relset_1('#skF_1', '#skF_3', '#skF_4', '#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.63/1.39  tff(c_100, plain, (~m1_subset_1(k7_relat_1('#skF_4', '#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_26])).
% 2.63/1.39  tff(c_439, plain, (~r1_tarski(k1_relat_1(k7_relat_1('#skF_4', '#skF_2')), '#skF_2')), inference(resolution, [status(thm)], [c_412, c_100])).
% 2.63/1.39  tff(c_449, plain, (~v4_relat_1(k7_relat_1('#skF_4', '#skF_2'), '#skF_2') | ~v1_relat_1(k7_relat_1('#skF_4', '#skF_2'))), inference(resolution, [status(thm)], [c_6, c_439])).
% 2.63/1.39  tff(c_453, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_72, c_449])).
% 2.63/1.39  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.63/1.39  
% 2.63/1.39  Inference rules
% 2.63/1.39  ----------------------
% 2.63/1.39  #Ref     : 0
% 2.63/1.39  #Sup     : 89
% 2.63/1.39  #Fact    : 0
% 2.63/1.39  #Define  : 0
% 2.63/1.39  #Split   : 0
% 2.63/1.39  #Chain   : 0
% 2.63/1.39  #Close   : 0
% 2.63/1.39  
% 2.63/1.39  Ordering : KBO
% 2.63/1.39  
% 2.63/1.39  Simplification rules
% 2.63/1.39  ----------------------
% 2.63/1.40  #Subsume      : 2
% 2.63/1.40  #Demod        : 64
% 2.63/1.40  #Tautology    : 27
% 2.63/1.40  #SimpNegUnit  : 0
% 2.63/1.40  #BackRed      : 1
% 2.63/1.40  
% 2.63/1.40  #Partial instantiations: 0
% 2.63/1.40  #Strategies tried      : 1
% 2.63/1.40  
% 2.63/1.40  Timing (in seconds)
% 2.63/1.40  ----------------------
% 2.63/1.40  Preprocessing        : 0.31
% 2.63/1.40  Parsing              : 0.17
% 2.63/1.40  CNF conversion       : 0.02
% 2.63/1.40  Main loop            : 0.27
% 2.63/1.40  Inferencing          : 0.11
% 2.63/1.40  Reduction            : 0.09
% 2.63/1.40  Demodulation         : 0.07
% 2.63/1.40  BG Simplification    : 0.01
% 2.63/1.40  Subsumption          : 0.04
% 2.63/1.40  Abstraction          : 0.02
% 2.63/1.40  MUC search           : 0.00
% 2.63/1.40  Cooper               : 0.00
% 2.63/1.40  Total                : 0.60
% 2.63/1.40  Index Insertion      : 0.00
% 2.63/1.40  Index Deletion       : 0.00
% 2.63/1.40  Index Matching       : 0.00
% 2.63/1.40  BG Taut test         : 0.00
%------------------------------------------------------------------------------

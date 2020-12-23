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
% DateTime   : Thu Dec  3 10:17:16 EST 2020

% Result     : Theorem 1.69s
% Output     : CNFRefutation 1.94s
% Verified   : 
% Statistics : Number of formulae       :   56 (  70 expanded)
%              Number of leaves         :   29 (  37 expanded)
%              Depth                    :    7
%              Number of atoms          :   61 (  78 expanded)
%              Number of equality atoms :   22 (  34 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k9_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k8_relset_1,type,(
    k8_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k6_partfun1,type,(
    k6_partfun1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_63,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_61,axiom,(
    ! [A] : m1_subset_1(k6_relat_1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_relset_1)).

tff(f_59,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(f_68,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => k8_relset_1(A,A,k6_partfun1(A),B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t171_funct_2)).

tff(f_29,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_43,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k9_relat_1(k6_relat_1(A),B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t162_funct_1)).

tff(f_39,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_55,axiom,(
    ! [A] : v2_funct_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_funct_1)).

tff(f_35,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( ( r1_tarski(A,k1_relat_1(B))
          & v2_funct_1(B) )
       => k10_relat_1(B,k9_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t164_funct_1)).

tff(c_26,plain,(
    ! [A_16] : k6_relat_1(A_16) = k6_partfun1(A_16) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_24,plain,(
    ! [A_15] : m1_subset_1(k6_relat_1(A_15),k1_zfmisc_1(k2_zfmisc_1(A_15,A_15))) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_31,plain,(
    ! [A_15] : m1_subset_1(k6_partfun1(A_15),k1_zfmisc_1(k2_zfmisc_1(A_15,A_15))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24])).

tff(c_102,plain,(
    ! [A_31,B_32,C_33,D_34] :
      ( k8_relset_1(A_31,B_32,C_33,D_34) = k10_relat_1(C_33,D_34)
      | ~ m1_subset_1(C_33,k1_zfmisc_1(k2_zfmisc_1(A_31,B_32))) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_108,plain,(
    ! [A_15,D_34] : k8_relset_1(A_15,A_15,k6_partfun1(A_15),D_34) = k10_relat_1(k6_partfun1(A_15),D_34) ),
    inference(resolution,[status(thm)],[c_31,c_102])).

tff(c_28,plain,(
    k8_relset_1('#skF_1','#skF_1',k6_partfun1('#skF_1'),'#skF_2') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_152,plain,(
    k10_relat_1(k6_partfun1('#skF_1'),'#skF_2') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_108,c_28])).

tff(c_30,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_69,plain,(
    ! [A_23,B_24] :
      ( r1_tarski(A_23,B_24)
      | ~ m1_subset_1(A_23,k1_zfmisc_1(B_24)) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_73,plain,(
    r1_tarski('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_69])).

tff(c_16,plain,(
    ! [A_6,B_7] :
      ( k9_relat_1(k6_relat_1(A_6),B_7) = B_7
      | ~ m1_subset_1(B_7,k1_zfmisc_1(A_6)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_85,plain,(
    ! [A_29,B_30] :
      ( k9_relat_1(k6_partfun1(A_29),B_30) = B_30
      | ~ m1_subset_1(B_30,k1_zfmisc_1(A_29)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_16])).

tff(c_97,plain,(
    k9_relat_1(k6_partfun1('#skF_1'),'#skF_2') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_30,c_85])).

tff(c_12,plain,(
    ! [A_5] : v1_relat_1(k6_relat_1(A_5)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_35,plain,(
    ! [A_5] : v1_relat_1(k6_partfun1(A_5)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_12])).

tff(c_14,plain,(
    ! [A_5] : v1_funct_1(k6_relat_1(A_5)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_34,plain,(
    ! [A_5] : v1_funct_1(k6_partfun1(A_5)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_14])).

tff(c_20,plain,(
    ! [A_10] : v2_funct_1(k6_relat_1(A_10)) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_32,plain,(
    ! [A_10] : v2_funct_1(k6_partfun1(A_10)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_20])).

tff(c_8,plain,(
    ! [A_4] : k1_relat_1(k6_relat_1(A_4)) = A_4 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_37,plain,(
    ! [A_4] : k1_relat_1(k6_partfun1(A_4)) = A_4 ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_8])).

tff(c_167,plain,(
    ! [B_44,A_45] :
      ( k10_relat_1(B_44,k9_relat_1(B_44,A_45)) = A_45
      | ~ v2_funct_1(B_44)
      | ~ r1_tarski(A_45,k1_relat_1(B_44))
      | ~ v1_funct_1(B_44)
      | ~ v1_relat_1(B_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_169,plain,(
    ! [A_4,A_45] :
      ( k10_relat_1(k6_partfun1(A_4),k9_relat_1(k6_partfun1(A_4),A_45)) = A_45
      | ~ v2_funct_1(k6_partfun1(A_4))
      | ~ r1_tarski(A_45,A_4)
      | ~ v1_funct_1(k6_partfun1(A_4))
      | ~ v1_relat_1(k6_partfun1(A_4)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_37,c_167])).

tff(c_172,plain,(
    ! [A_46,A_47] :
      ( k10_relat_1(k6_partfun1(A_46),k9_relat_1(k6_partfun1(A_46),A_47)) = A_47
      | ~ r1_tarski(A_47,A_46) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_35,c_34,c_32,c_169])).

tff(c_187,plain,
    ( k10_relat_1(k6_partfun1('#skF_1'),'#skF_2') = '#skF_2'
    | ~ r1_tarski('#skF_2','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_97,c_172])).

tff(c_193,plain,(
    k10_relat_1(k6_partfun1('#skF_1'),'#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_73,c_187])).

tff(c_195,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_152,c_193])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:11:38 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.69/1.18  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.94/1.18  
% 1.94/1.18  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.94/1.18  %$ r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k9_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_1
% 1.94/1.18  
% 1.94/1.18  %Foreground sorts:
% 1.94/1.18  
% 1.94/1.18  
% 1.94/1.18  %Background operators:
% 1.94/1.18  
% 1.94/1.18  
% 1.94/1.18  %Foreground operators:
% 1.94/1.18  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.94/1.18  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 1.94/1.18  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.94/1.18  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 1.94/1.18  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.94/1.18  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.94/1.18  tff('#skF_2', type, '#skF_2': $i).
% 1.94/1.18  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 1.94/1.18  tff('#skF_1', type, '#skF_1': $i).
% 1.94/1.18  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.94/1.18  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 1.94/1.18  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.94/1.18  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 1.94/1.18  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.94/1.18  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.94/1.18  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 1.94/1.18  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.94/1.18  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.94/1.18  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.94/1.18  
% 1.94/1.20  tff(f_63, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 1.94/1.20  tff(f_61, axiom, (![A]: m1_subset_1(k6_relat_1(A), k1_zfmisc_1(k2_zfmisc_1(A, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_relset_1)).
% 1.94/1.20  tff(f_59, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 1.94/1.20  tff(f_68, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k8_relset_1(A, A, k6_partfun1(A), B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t171_funct_2)).
% 1.94/1.20  tff(f_29, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 1.94/1.20  tff(f_43, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k9_relat_1(k6_relat_1(A), B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t162_funct_1)).
% 1.94/1.20  tff(f_39, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc3_funct_1)).
% 1.94/1.20  tff(f_55, axiom, (![A]: v2_funct_1(k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_funct_1)).
% 1.94/1.20  tff(f_35, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 1.94/1.20  tff(f_53, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((r1_tarski(A, k1_relat_1(B)) & v2_funct_1(B)) => (k10_relat_1(B, k9_relat_1(B, A)) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t164_funct_1)).
% 1.94/1.20  tff(c_26, plain, (![A_16]: (k6_relat_1(A_16)=k6_partfun1(A_16))), inference(cnfTransformation, [status(thm)], [f_63])).
% 1.94/1.20  tff(c_24, plain, (![A_15]: (m1_subset_1(k6_relat_1(A_15), k1_zfmisc_1(k2_zfmisc_1(A_15, A_15))))), inference(cnfTransformation, [status(thm)], [f_61])).
% 1.94/1.20  tff(c_31, plain, (![A_15]: (m1_subset_1(k6_partfun1(A_15), k1_zfmisc_1(k2_zfmisc_1(A_15, A_15))))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_24])).
% 1.94/1.20  tff(c_102, plain, (![A_31, B_32, C_33, D_34]: (k8_relset_1(A_31, B_32, C_33, D_34)=k10_relat_1(C_33, D_34) | ~m1_subset_1(C_33, k1_zfmisc_1(k2_zfmisc_1(A_31, B_32))))), inference(cnfTransformation, [status(thm)], [f_59])).
% 1.94/1.20  tff(c_108, plain, (![A_15, D_34]: (k8_relset_1(A_15, A_15, k6_partfun1(A_15), D_34)=k10_relat_1(k6_partfun1(A_15), D_34))), inference(resolution, [status(thm)], [c_31, c_102])).
% 1.94/1.20  tff(c_28, plain, (k8_relset_1('#skF_1', '#skF_1', k6_partfun1('#skF_1'), '#skF_2')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_68])).
% 1.94/1.20  tff(c_152, plain, (k10_relat_1(k6_partfun1('#skF_1'), '#skF_2')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_108, c_28])).
% 1.94/1.20  tff(c_30, plain, (m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_68])).
% 1.94/1.20  tff(c_69, plain, (![A_23, B_24]: (r1_tarski(A_23, B_24) | ~m1_subset_1(A_23, k1_zfmisc_1(B_24)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.94/1.20  tff(c_73, plain, (r1_tarski('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_30, c_69])).
% 1.94/1.20  tff(c_16, plain, (![A_6, B_7]: (k9_relat_1(k6_relat_1(A_6), B_7)=B_7 | ~m1_subset_1(B_7, k1_zfmisc_1(A_6)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.94/1.20  tff(c_85, plain, (![A_29, B_30]: (k9_relat_1(k6_partfun1(A_29), B_30)=B_30 | ~m1_subset_1(B_30, k1_zfmisc_1(A_29)))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_16])).
% 1.94/1.20  tff(c_97, plain, (k9_relat_1(k6_partfun1('#skF_1'), '#skF_2')='#skF_2'), inference(resolution, [status(thm)], [c_30, c_85])).
% 1.94/1.20  tff(c_12, plain, (![A_5]: (v1_relat_1(k6_relat_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.94/1.20  tff(c_35, plain, (![A_5]: (v1_relat_1(k6_partfun1(A_5)))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_12])).
% 1.94/1.20  tff(c_14, plain, (![A_5]: (v1_funct_1(k6_relat_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.94/1.20  tff(c_34, plain, (![A_5]: (v1_funct_1(k6_partfun1(A_5)))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_14])).
% 1.94/1.20  tff(c_20, plain, (![A_10]: (v2_funct_1(k6_relat_1(A_10)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 1.94/1.20  tff(c_32, plain, (![A_10]: (v2_funct_1(k6_partfun1(A_10)))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_20])).
% 1.94/1.20  tff(c_8, plain, (![A_4]: (k1_relat_1(k6_relat_1(A_4))=A_4)), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.94/1.20  tff(c_37, plain, (![A_4]: (k1_relat_1(k6_partfun1(A_4))=A_4)), inference(demodulation, [status(thm), theory('equality')], [c_26, c_8])).
% 1.94/1.20  tff(c_167, plain, (![B_44, A_45]: (k10_relat_1(B_44, k9_relat_1(B_44, A_45))=A_45 | ~v2_funct_1(B_44) | ~r1_tarski(A_45, k1_relat_1(B_44)) | ~v1_funct_1(B_44) | ~v1_relat_1(B_44))), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.94/1.20  tff(c_169, plain, (![A_4, A_45]: (k10_relat_1(k6_partfun1(A_4), k9_relat_1(k6_partfun1(A_4), A_45))=A_45 | ~v2_funct_1(k6_partfun1(A_4)) | ~r1_tarski(A_45, A_4) | ~v1_funct_1(k6_partfun1(A_4)) | ~v1_relat_1(k6_partfun1(A_4)))), inference(superposition, [status(thm), theory('equality')], [c_37, c_167])).
% 1.94/1.20  tff(c_172, plain, (![A_46, A_47]: (k10_relat_1(k6_partfun1(A_46), k9_relat_1(k6_partfun1(A_46), A_47))=A_47 | ~r1_tarski(A_47, A_46))), inference(demodulation, [status(thm), theory('equality')], [c_35, c_34, c_32, c_169])).
% 1.94/1.20  tff(c_187, plain, (k10_relat_1(k6_partfun1('#skF_1'), '#skF_2')='#skF_2' | ~r1_tarski('#skF_2', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_97, c_172])).
% 1.94/1.20  tff(c_193, plain, (k10_relat_1(k6_partfun1('#skF_1'), '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_73, c_187])).
% 1.94/1.20  tff(c_195, plain, $false, inference(negUnitSimplification, [status(thm)], [c_152, c_193])).
% 1.94/1.20  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.94/1.20  
% 1.94/1.20  Inference rules
% 1.94/1.20  ----------------------
% 1.94/1.20  #Ref     : 0
% 1.94/1.20  #Sup     : 33
% 1.94/1.20  #Fact    : 0
% 1.94/1.20  #Define  : 0
% 1.94/1.20  #Split   : 0
% 1.94/1.20  #Chain   : 0
% 1.94/1.20  #Close   : 0
% 1.94/1.20  
% 1.94/1.20  Ordering : KBO
% 1.94/1.20  
% 1.94/1.20  Simplification rules
% 1.94/1.20  ----------------------
% 1.94/1.20  #Subsume      : 0
% 1.94/1.20  #Demod        : 20
% 1.94/1.20  #Tautology    : 23
% 1.94/1.20  #SimpNegUnit  : 1
% 1.94/1.20  #BackRed      : 1
% 1.94/1.20  
% 1.94/1.20  #Partial instantiations: 0
% 1.94/1.20  #Strategies tried      : 1
% 1.94/1.20  
% 1.94/1.20  Timing (in seconds)
% 1.94/1.20  ----------------------
% 1.94/1.20  Preprocessing        : 0.30
% 1.94/1.20  Parsing              : 0.17
% 1.94/1.20  CNF conversion       : 0.02
% 1.94/1.20  Main loop            : 0.13
% 1.94/1.20  Inferencing          : 0.05
% 1.94/1.20  Reduction            : 0.04
% 1.94/1.20  Demodulation         : 0.03
% 1.94/1.20  BG Simplification    : 0.01
% 1.94/1.20  Subsumption          : 0.01
% 1.94/1.20  Abstraction          : 0.01
% 1.94/1.20  MUC search           : 0.00
% 1.94/1.20  Cooper               : 0.00
% 1.94/1.20  Total                : 0.46
% 1.94/1.20  Index Insertion      : 0.00
% 1.94/1.20  Index Deletion       : 0.00
% 1.94/1.20  Index Matching       : 0.00
% 1.94/1.20  BG Taut test         : 0.00
%------------------------------------------------------------------------------

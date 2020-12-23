%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:15 EST 2020

% Result     : Theorem 1.93s
% Output     : CNFRefutation 2.05s
% Verified   : 
% Statistics : Number of formulae       :   56 (  68 expanded)
%              Number of leaves         :   30 (  37 expanded)
%              Depth                    :    7
%              Number of atoms          :   62 (  77 expanded)
%              Number of equality atoms :   22 (  32 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_partfun1 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k9_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_1

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

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

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
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_59,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(f_70,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => k8_relset_1(A,A,k6_partfun1(A),B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t171_funct_2)).

tff(f_29,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_65,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k9_relat_1(k6_relat_1(A),B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t162_funct_1)).

tff(f_41,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v2_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).

tff(f_37,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_33,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( ( r1_tarski(A,k1_relat_1(B))
          & v2_funct_1(B) )
       => k10_relat_1(B,k9_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t164_funct_1)).

tff(c_26,plain,(
    ! [A_14] : m1_subset_1(k6_partfun1(A_14),k1_zfmisc_1(k2_zfmisc_1(A_14,A_14))) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_100,plain,(
    ! [A_31,B_32,C_33,D_34] :
      ( k8_relset_1(A_31,B_32,C_33,D_34) = k10_relat_1(C_33,D_34)
      | ~ m1_subset_1(C_33,k1_zfmisc_1(k2_zfmisc_1(A_31,B_32))) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_106,plain,(
    ! [A_14,D_34] : k8_relset_1(A_14,A_14,k6_partfun1(A_14),D_34) = k10_relat_1(k6_partfun1(A_14),D_34) ),
    inference(resolution,[status(thm)],[c_26,c_100])).

tff(c_30,plain,(
    k8_relset_1('#skF_1','#skF_1',k6_partfun1('#skF_1'),'#skF_2') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_159,plain,(
    k10_relat_1(k6_partfun1('#skF_1'),'#skF_2') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_30])).

tff(c_32,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_71,plain,(
    ! [A_23,B_24] :
      ( r1_tarski(A_23,B_24)
      | ~ m1_subset_1(A_23,k1_zfmisc_1(B_24)) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_75,plain,(
    r1_tarski('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_71])).

tff(c_28,plain,(
    ! [A_15] : k6_relat_1(A_15) = k6_partfun1(A_15) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_18,plain,(
    ! [A_6,B_7] :
      ( k9_relat_1(k6_relat_1(A_6),B_7) = B_7
      | ~ m1_subset_1(B_7,k1_zfmisc_1(A_6)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_87,plain,(
    ! [A_29,B_30] :
      ( k9_relat_1(k6_partfun1(A_29),B_30) = B_30
      | ~ m1_subset_1(B_30,k1_zfmisc_1(A_29)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_18])).

tff(c_99,plain,(
    k9_relat_1(k6_partfun1('#skF_1'),'#skF_2') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_32,c_87])).

tff(c_14,plain,(
    ! [A_5] : v1_relat_1(k6_relat_1(A_5)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_35,plain,(
    ! [A_5] : v1_relat_1(k6_partfun1(A_5)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_14])).

tff(c_12,plain,(
    ! [A_4] : v1_funct_1(k6_relat_1(A_4)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_36,plain,(
    ! [A_4] : v1_funct_1(k6_partfun1(A_4)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_12])).

tff(c_16,plain,(
    ! [A_5] : v2_funct_1(k6_relat_1(A_5)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_34,plain,(
    ! [A_5] : v2_funct_1(k6_partfun1(A_5)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_16])).

tff(c_6,plain,(
    ! [A_3] : k1_relat_1(k6_relat_1(A_3)) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_39,plain,(
    ! [A_3] : k1_relat_1(k6_partfun1(A_3)) = A_3 ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_6])).

tff(c_154,plain,(
    ! [B_38,A_39] :
      ( k10_relat_1(B_38,k9_relat_1(B_38,A_39)) = A_39
      | ~ v2_funct_1(B_38)
      | ~ r1_tarski(A_39,k1_relat_1(B_38))
      | ~ v1_funct_1(B_38)
      | ~ v1_relat_1(B_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_156,plain,(
    ! [A_3,A_39] :
      ( k10_relat_1(k6_partfun1(A_3),k9_relat_1(k6_partfun1(A_3),A_39)) = A_39
      | ~ v2_funct_1(k6_partfun1(A_3))
      | ~ r1_tarski(A_39,A_3)
      | ~ v1_funct_1(k6_partfun1(A_3))
      | ~ v1_relat_1(k6_partfun1(A_3)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_39,c_154])).

tff(c_169,plain,(
    ! [A_42,A_43] :
      ( k10_relat_1(k6_partfun1(A_42),k9_relat_1(k6_partfun1(A_42),A_43)) = A_43
      | ~ r1_tarski(A_43,A_42) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_35,c_36,c_34,c_156])).

tff(c_184,plain,
    ( k10_relat_1(k6_partfun1('#skF_1'),'#skF_2') = '#skF_2'
    | ~ r1_tarski('#skF_2','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_99,c_169])).

tff(c_190,plain,(
    k10_relat_1(k6_partfun1('#skF_1'),'#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_75,c_184])).

tff(c_192,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_159,c_190])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:38:16 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.93/1.24  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.93/1.24  
% 1.93/1.24  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.93/1.24  %$ v1_partfun1 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k9_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_1
% 1.93/1.24  
% 1.93/1.24  %Foreground sorts:
% 1.93/1.24  
% 1.93/1.24  
% 1.93/1.24  %Background operators:
% 1.93/1.24  
% 1.93/1.24  
% 1.93/1.24  %Foreground operators:
% 1.93/1.24  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.93/1.24  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 1.93/1.24  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.93/1.24  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 1.93/1.24  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.93/1.24  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.93/1.24  tff('#skF_2', type, '#skF_2': $i).
% 1.93/1.24  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 1.93/1.24  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 1.93/1.24  tff('#skF_1', type, '#skF_1': $i).
% 1.93/1.24  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.93/1.24  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 1.93/1.24  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.93/1.24  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 1.93/1.24  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.93/1.24  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.93/1.24  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 1.93/1.24  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.93/1.24  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.93/1.24  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.93/1.24  
% 2.05/1.26  tff(f_63, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 2.05/1.26  tff(f_59, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 2.05/1.26  tff(f_70, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k8_relset_1(A, A, k6_partfun1(A), B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t171_funct_2)).
% 2.05/1.26  tff(f_29, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 2.05/1.26  tff(f_65, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 2.05/1.26  tff(f_45, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k9_relat_1(k6_relat_1(A), B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t162_funct_1)).
% 2.05/1.26  tff(f_41, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v2_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc4_funct_1)).
% 2.05/1.26  tff(f_37, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc3_funct_1)).
% 2.05/1.26  tff(f_33, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 2.05/1.26  tff(f_55, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((r1_tarski(A, k1_relat_1(B)) & v2_funct_1(B)) => (k10_relat_1(B, k9_relat_1(B, A)) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t164_funct_1)).
% 2.05/1.26  tff(c_26, plain, (![A_14]: (m1_subset_1(k6_partfun1(A_14), k1_zfmisc_1(k2_zfmisc_1(A_14, A_14))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.05/1.26  tff(c_100, plain, (![A_31, B_32, C_33, D_34]: (k8_relset_1(A_31, B_32, C_33, D_34)=k10_relat_1(C_33, D_34) | ~m1_subset_1(C_33, k1_zfmisc_1(k2_zfmisc_1(A_31, B_32))))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.05/1.26  tff(c_106, plain, (![A_14, D_34]: (k8_relset_1(A_14, A_14, k6_partfun1(A_14), D_34)=k10_relat_1(k6_partfun1(A_14), D_34))), inference(resolution, [status(thm)], [c_26, c_100])).
% 2.05/1.26  tff(c_30, plain, (k8_relset_1('#skF_1', '#skF_1', k6_partfun1('#skF_1'), '#skF_2')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.05/1.26  tff(c_159, plain, (k10_relat_1(k6_partfun1('#skF_1'), '#skF_2')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_106, c_30])).
% 2.05/1.26  tff(c_32, plain, (m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.05/1.26  tff(c_71, plain, (![A_23, B_24]: (r1_tarski(A_23, B_24) | ~m1_subset_1(A_23, k1_zfmisc_1(B_24)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.05/1.26  tff(c_75, plain, (r1_tarski('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_32, c_71])).
% 2.05/1.26  tff(c_28, plain, (![A_15]: (k6_relat_1(A_15)=k6_partfun1(A_15))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.05/1.26  tff(c_18, plain, (![A_6, B_7]: (k9_relat_1(k6_relat_1(A_6), B_7)=B_7 | ~m1_subset_1(B_7, k1_zfmisc_1(A_6)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.05/1.26  tff(c_87, plain, (![A_29, B_30]: (k9_relat_1(k6_partfun1(A_29), B_30)=B_30 | ~m1_subset_1(B_30, k1_zfmisc_1(A_29)))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_18])).
% 2.05/1.26  tff(c_99, plain, (k9_relat_1(k6_partfun1('#skF_1'), '#skF_2')='#skF_2'), inference(resolution, [status(thm)], [c_32, c_87])).
% 2.05/1.26  tff(c_14, plain, (![A_5]: (v1_relat_1(k6_relat_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.05/1.26  tff(c_35, plain, (![A_5]: (v1_relat_1(k6_partfun1(A_5)))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_14])).
% 2.05/1.26  tff(c_12, plain, (![A_4]: (v1_funct_1(k6_relat_1(A_4)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.05/1.26  tff(c_36, plain, (![A_4]: (v1_funct_1(k6_partfun1(A_4)))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_12])).
% 2.05/1.26  tff(c_16, plain, (![A_5]: (v2_funct_1(k6_relat_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.05/1.26  tff(c_34, plain, (![A_5]: (v2_funct_1(k6_partfun1(A_5)))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_16])).
% 2.05/1.26  tff(c_6, plain, (![A_3]: (k1_relat_1(k6_relat_1(A_3))=A_3)), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.05/1.26  tff(c_39, plain, (![A_3]: (k1_relat_1(k6_partfun1(A_3))=A_3)), inference(demodulation, [status(thm), theory('equality')], [c_28, c_6])).
% 2.05/1.26  tff(c_154, plain, (![B_38, A_39]: (k10_relat_1(B_38, k9_relat_1(B_38, A_39))=A_39 | ~v2_funct_1(B_38) | ~r1_tarski(A_39, k1_relat_1(B_38)) | ~v1_funct_1(B_38) | ~v1_relat_1(B_38))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.05/1.26  tff(c_156, plain, (![A_3, A_39]: (k10_relat_1(k6_partfun1(A_3), k9_relat_1(k6_partfun1(A_3), A_39))=A_39 | ~v2_funct_1(k6_partfun1(A_3)) | ~r1_tarski(A_39, A_3) | ~v1_funct_1(k6_partfun1(A_3)) | ~v1_relat_1(k6_partfun1(A_3)))), inference(superposition, [status(thm), theory('equality')], [c_39, c_154])).
% 2.05/1.26  tff(c_169, plain, (![A_42, A_43]: (k10_relat_1(k6_partfun1(A_42), k9_relat_1(k6_partfun1(A_42), A_43))=A_43 | ~r1_tarski(A_43, A_42))), inference(demodulation, [status(thm), theory('equality')], [c_35, c_36, c_34, c_156])).
% 2.05/1.26  tff(c_184, plain, (k10_relat_1(k6_partfun1('#skF_1'), '#skF_2')='#skF_2' | ~r1_tarski('#skF_2', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_99, c_169])).
% 2.05/1.26  tff(c_190, plain, (k10_relat_1(k6_partfun1('#skF_1'), '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_75, c_184])).
% 2.05/1.26  tff(c_192, plain, $false, inference(negUnitSimplification, [status(thm)], [c_159, c_190])).
% 2.05/1.26  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.05/1.26  
% 2.05/1.26  Inference rules
% 2.05/1.26  ----------------------
% 2.05/1.26  #Ref     : 0
% 2.05/1.26  #Sup     : 32
% 2.05/1.26  #Fact    : 0
% 2.05/1.26  #Define  : 0
% 2.05/1.26  #Split   : 0
% 2.05/1.26  #Chain   : 0
% 2.05/1.26  #Close   : 0
% 2.05/1.26  
% 2.05/1.26  Ordering : KBO
% 2.05/1.26  
% 2.05/1.26  Simplification rules
% 2.05/1.26  ----------------------
% 2.05/1.26  #Subsume      : 0
% 2.05/1.26  #Demod        : 18
% 2.05/1.26  #Tautology    : 22
% 2.05/1.26  #SimpNegUnit  : 1
% 2.05/1.26  #BackRed      : 1
% 2.05/1.26  
% 2.05/1.26  #Partial instantiations: 0
% 2.05/1.26  #Strategies tried      : 1
% 2.05/1.26  
% 2.05/1.26  Timing (in seconds)
% 2.05/1.26  ----------------------
% 2.05/1.26  Preprocessing        : 0.31
% 2.05/1.26  Parsing              : 0.18
% 2.05/1.26  CNF conversion       : 0.02
% 2.05/1.26  Main loop            : 0.14
% 2.05/1.26  Inferencing          : 0.06
% 2.05/1.26  Reduction            : 0.05
% 2.05/1.26  Demodulation         : 0.03
% 2.05/1.26  BG Simplification    : 0.01
% 2.05/1.26  Subsumption          : 0.01
% 2.05/1.26  Abstraction          : 0.01
% 2.05/1.26  MUC search           : 0.00
% 2.05/1.26  Cooper               : 0.00
% 2.05/1.26  Total                : 0.49
% 2.05/1.26  Index Insertion      : 0.00
% 2.05/1.26  Index Deletion       : 0.00
% 2.05/1.26  Index Matching       : 0.00
% 2.05/1.26  BG Taut test         : 0.00
%------------------------------------------------------------------------------

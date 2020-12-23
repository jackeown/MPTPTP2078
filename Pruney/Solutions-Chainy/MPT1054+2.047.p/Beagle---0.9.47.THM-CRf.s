%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:18 EST 2020

% Result     : Theorem 1.95s
% Output     : CNFRefutation 1.95s
% Verified   : 
% Statistics : Number of formulae       :   56 (  70 expanded)
%              Number of leaves         :   29 (  37 expanded)
%              Depth                    :    7
%              Number of atoms          :   62 (  79 expanded)
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_61,axiom,(
    ! [A] : m1_subset_1(k6_relat_1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_relset_1)).

tff(f_59,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(f_68,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => k8_relset_1(A,A,k6_partfun1(A),B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t171_funct_2)).

tff(f_29,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_45,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k9_relat_1(k6_relat_1(A),B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t162_funct_1)).

tff(f_41,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v2_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_funct_1)).

tff(f_37,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_33,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( ( r1_tarski(A,k1_relat_1(B))
          & v2_funct_1(B) )
       => k10_relat_1(B,k9_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t164_funct_1)).

tff(c_26,plain,(
    ! [A_15] : k6_relat_1(A_15) = k6_partfun1(A_15) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_24,plain,(
    ! [A_14] : m1_subset_1(k6_relat_1(A_14),k1_zfmisc_1(k2_zfmisc_1(A_14,A_14))) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_31,plain,(
    ! [A_14] : m1_subset_1(k6_partfun1(A_14),k1_zfmisc_1(k2_zfmisc_1(A_14,A_14))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24])).

tff(c_102,plain,(
    ! [A_30,B_31,C_32,D_33] :
      ( k8_relset_1(A_30,B_31,C_32,D_33) = k10_relat_1(C_32,D_33)
      | ~ m1_subset_1(C_32,k1_zfmisc_1(k2_zfmisc_1(A_30,B_31))) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_108,plain,(
    ! [A_14,D_33] : k8_relset_1(A_14,A_14,k6_partfun1(A_14),D_33) = k10_relat_1(k6_partfun1(A_14),D_33) ),
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

tff(c_70,plain,(
    ! [A_24,B_25] :
      ( r1_tarski(A_24,B_25)
      | ~ m1_subset_1(A_24,k1_zfmisc_1(B_25)) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_78,plain,(
    r1_tarski('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_70])).

tff(c_18,plain,(
    ! [A_6,B_7] :
      ( k9_relat_1(k6_relat_1(A_6),B_7) = B_7
      | ~ m1_subset_1(B_7,k1_zfmisc_1(A_6)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_85,plain,(
    ! [A_28,B_29] :
      ( k9_relat_1(k6_partfun1(A_28),B_29) = B_29
      | ~ m1_subset_1(B_29,k1_zfmisc_1(A_28)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_18])).

tff(c_97,plain,(
    k9_relat_1(k6_partfun1('#skF_1'),'#skF_2') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_30,c_85])).

tff(c_14,plain,(
    ! [A_5] : v1_relat_1(k6_relat_1(A_5)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_34,plain,(
    ! [A_5] : v1_relat_1(k6_partfun1(A_5)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_14])).

tff(c_12,plain,(
    ! [A_4] : v1_funct_1(k6_relat_1(A_4)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_35,plain,(
    ! [A_4] : v1_funct_1(k6_partfun1(A_4)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_12])).

tff(c_16,plain,(
    ! [A_5] : v2_funct_1(k6_relat_1(A_5)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_33,plain,(
    ! [A_5] : v2_funct_1(k6_partfun1(A_5)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_16])).

tff(c_6,plain,(
    ! [A_3] : k1_relat_1(k6_relat_1(A_3)) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_38,plain,(
    ! [A_3] : k1_relat_1(k6_partfun1(A_3)) = A_3 ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_6])).

tff(c_167,plain,(
    ! [B_43,A_44] :
      ( k10_relat_1(B_43,k9_relat_1(B_43,A_44)) = A_44
      | ~ v2_funct_1(B_43)
      | ~ r1_tarski(A_44,k1_relat_1(B_43))
      | ~ v1_funct_1(B_43)
      | ~ v1_relat_1(B_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_169,plain,(
    ! [A_3,A_44] :
      ( k10_relat_1(k6_partfun1(A_3),k9_relat_1(k6_partfun1(A_3),A_44)) = A_44
      | ~ v2_funct_1(k6_partfun1(A_3))
      | ~ r1_tarski(A_44,A_3)
      | ~ v1_funct_1(k6_partfun1(A_3))
      | ~ v1_relat_1(k6_partfun1(A_3)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_167])).

tff(c_172,plain,(
    ! [A_45,A_46] :
      ( k10_relat_1(k6_partfun1(A_45),k9_relat_1(k6_partfun1(A_45),A_46)) = A_46
      | ~ r1_tarski(A_46,A_45) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_35,c_33,c_169])).

tff(c_187,plain,
    ( k10_relat_1(k6_partfun1('#skF_1'),'#skF_2') = '#skF_2'
    | ~ r1_tarski('#skF_2','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_97,c_172])).

tff(c_193,plain,(
    k10_relat_1(k6_partfun1('#skF_1'),'#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_187])).

tff(c_195,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_152,c_193])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:58:46 EST 2020
% 0.20/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.95/1.24  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.95/1.25  
% 1.95/1.25  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.95/1.25  %$ r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k9_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_1
% 1.95/1.25  
% 1.95/1.25  %Foreground sorts:
% 1.95/1.25  
% 1.95/1.25  
% 1.95/1.25  %Background operators:
% 1.95/1.25  
% 1.95/1.25  
% 1.95/1.25  %Foreground operators:
% 1.95/1.25  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.95/1.25  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 1.95/1.25  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.95/1.25  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 1.95/1.25  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.95/1.25  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.95/1.25  tff('#skF_2', type, '#skF_2': $i).
% 1.95/1.25  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 1.95/1.25  tff('#skF_1', type, '#skF_1': $i).
% 1.95/1.25  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.95/1.25  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 1.95/1.25  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.95/1.25  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 1.95/1.25  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.95/1.25  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.95/1.25  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 1.95/1.25  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.95/1.25  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.95/1.25  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.95/1.25  
% 1.95/1.26  tff(f_63, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 1.95/1.26  tff(f_61, axiom, (![A]: m1_subset_1(k6_relat_1(A), k1_zfmisc_1(k2_zfmisc_1(A, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_relset_1)).
% 1.95/1.26  tff(f_59, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 1.95/1.26  tff(f_68, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k8_relset_1(A, A, k6_partfun1(A), B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t171_funct_2)).
% 1.95/1.26  tff(f_29, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 1.95/1.26  tff(f_45, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k9_relat_1(k6_relat_1(A), B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t162_funct_1)).
% 1.95/1.26  tff(f_41, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v2_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc4_funct_1)).
% 1.95/1.26  tff(f_37, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc3_funct_1)).
% 1.95/1.26  tff(f_33, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 1.95/1.26  tff(f_55, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((r1_tarski(A, k1_relat_1(B)) & v2_funct_1(B)) => (k10_relat_1(B, k9_relat_1(B, A)) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t164_funct_1)).
% 1.95/1.26  tff(c_26, plain, (![A_15]: (k6_relat_1(A_15)=k6_partfun1(A_15))), inference(cnfTransformation, [status(thm)], [f_63])).
% 1.95/1.26  tff(c_24, plain, (![A_14]: (m1_subset_1(k6_relat_1(A_14), k1_zfmisc_1(k2_zfmisc_1(A_14, A_14))))), inference(cnfTransformation, [status(thm)], [f_61])).
% 1.95/1.26  tff(c_31, plain, (![A_14]: (m1_subset_1(k6_partfun1(A_14), k1_zfmisc_1(k2_zfmisc_1(A_14, A_14))))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_24])).
% 1.95/1.26  tff(c_102, plain, (![A_30, B_31, C_32, D_33]: (k8_relset_1(A_30, B_31, C_32, D_33)=k10_relat_1(C_32, D_33) | ~m1_subset_1(C_32, k1_zfmisc_1(k2_zfmisc_1(A_30, B_31))))), inference(cnfTransformation, [status(thm)], [f_59])).
% 1.95/1.26  tff(c_108, plain, (![A_14, D_33]: (k8_relset_1(A_14, A_14, k6_partfun1(A_14), D_33)=k10_relat_1(k6_partfun1(A_14), D_33))), inference(resolution, [status(thm)], [c_31, c_102])).
% 1.95/1.26  tff(c_28, plain, (k8_relset_1('#skF_1', '#skF_1', k6_partfun1('#skF_1'), '#skF_2')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_68])).
% 1.95/1.26  tff(c_152, plain, (k10_relat_1(k6_partfun1('#skF_1'), '#skF_2')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_108, c_28])).
% 1.95/1.26  tff(c_30, plain, (m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_68])).
% 1.95/1.26  tff(c_70, plain, (![A_24, B_25]: (r1_tarski(A_24, B_25) | ~m1_subset_1(A_24, k1_zfmisc_1(B_25)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.95/1.26  tff(c_78, plain, (r1_tarski('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_30, c_70])).
% 1.95/1.26  tff(c_18, plain, (![A_6, B_7]: (k9_relat_1(k6_relat_1(A_6), B_7)=B_7 | ~m1_subset_1(B_7, k1_zfmisc_1(A_6)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.95/1.26  tff(c_85, plain, (![A_28, B_29]: (k9_relat_1(k6_partfun1(A_28), B_29)=B_29 | ~m1_subset_1(B_29, k1_zfmisc_1(A_28)))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_18])).
% 1.95/1.26  tff(c_97, plain, (k9_relat_1(k6_partfun1('#skF_1'), '#skF_2')='#skF_2'), inference(resolution, [status(thm)], [c_30, c_85])).
% 1.95/1.26  tff(c_14, plain, (![A_5]: (v1_relat_1(k6_relat_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.95/1.26  tff(c_34, plain, (![A_5]: (v1_relat_1(k6_partfun1(A_5)))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_14])).
% 1.95/1.26  tff(c_12, plain, (![A_4]: (v1_funct_1(k6_relat_1(A_4)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.95/1.26  tff(c_35, plain, (![A_4]: (v1_funct_1(k6_partfun1(A_4)))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_12])).
% 1.95/1.26  tff(c_16, plain, (![A_5]: (v2_funct_1(k6_relat_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.95/1.26  tff(c_33, plain, (![A_5]: (v2_funct_1(k6_partfun1(A_5)))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_16])).
% 1.95/1.26  tff(c_6, plain, (![A_3]: (k1_relat_1(k6_relat_1(A_3))=A_3)), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.95/1.26  tff(c_38, plain, (![A_3]: (k1_relat_1(k6_partfun1(A_3))=A_3)), inference(demodulation, [status(thm), theory('equality')], [c_26, c_6])).
% 1.95/1.26  tff(c_167, plain, (![B_43, A_44]: (k10_relat_1(B_43, k9_relat_1(B_43, A_44))=A_44 | ~v2_funct_1(B_43) | ~r1_tarski(A_44, k1_relat_1(B_43)) | ~v1_funct_1(B_43) | ~v1_relat_1(B_43))), inference(cnfTransformation, [status(thm)], [f_55])).
% 1.95/1.26  tff(c_169, plain, (![A_3, A_44]: (k10_relat_1(k6_partfun1(A_3), k9_relat_1(k6_partfun1(A_3), A_44))=A_44 | ~v2_funct_1(k6_partfun1(A_3)) | ~r1_tarski(A_44, A_3) | ~v1_funct_1(k6_partfun1(A_3)) | ~v1_relat_1(k6_partfun1(A_3)))), inference(superposition, [status(thm), theory('equality')], [c_38, c_167])).
% 1.95/1.26  tff(c_172, plain, (![A_45, A_46]: (k10_relat_1(k6_partfun1(A_45), k9_relat_1(k6_partfun1(A_45), A_46))=A_46 | ~r1_tarski(A_46, A_45))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_35, c_33, c_169])).
% 1.95/1.26  tff(c_187, plain, (k10_relat_1(k6_partfun1('#skF_1'), '#skF_2')='#skF_2' | ~r1_tarski('#skF_2', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_97, c_172])).
% 1.95/1.26  tff(c_193, plain, (k10_relat_1(k6_partfun1('#skF_1'), '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_78, c_187])).
% 1.95/1.26  tff(c_195, plain, $false, inference(negUnitSimplification, [status(thm)], [c_152, c_193])).
% 1.95/1.26  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.95/1.26  
% 1.95/1.26  Inference rules
% 1.95/1.26  ----------------------
% 1.95/1.26  #Ref     : 0
% 1.95/1.26  #Sup     : 33
% 1.95/1.26  #Fact    : 0
% 1.95/1.26  #Define  : 0
% 1.95/1.26  #Split   : 0
% 1.95/1.26  #Chain   : 0
% 1.95/1.26  #Close   : 0
% 1.95/1.26  
% 1.95/1.26  Ordering : KBO
% 1.95/1.26  
% 1.95/1.26  Simplification rules
% 1.95/1.26  ----------------------
% 1.95/1.26  #Subsume      : 0
% 1.95/1.26  #Demod        : 20
% 1.95/1.26  #Tautology    : 23
% 1.95/1.26  #SimpNegUnit  : 1
% 1.95/1.26  #BackRed      : 1
% 1.95/1.26  
% 1.95/1.26  #Partial instantiations: 0
% 1.95/1.26  #Strategies tried      : 1
% 1.95/1.26  
% 1.95/1.26  Timing (in seconds)
% 1.95/1.26  ----------------------
% 1.95/1.27  Preprocessing        : 0.31
% 1.95/1.27  Parsing              : 0.17
% 1.95/1.27  CNF conversion       : 0.02
% 1.95/1.27  Main loop            : 0.13
% 1.95/1.27  Inferencing          : 0.06
% 1.95/1.27  Reduction            : 0.04
% 1.95/1.27  Demodulation         : 0.03
% 1.95/1.27  BG Simplification    : 0.01
% 1.95/1.27  Subsumption          : 0.01
% 1.95/1.27  Abstraction          : 0.01
% 1.95/1.27  MUC search           : 0.00
% 1.95/1.27  Cooper               : 0.00
% 1.95/1.27  Total                : 0.47
% 1.95/1.27  Index Insertion      : 0.00
% 1.95/1.27  Index Deletion       : 0.00
% 1.95/1.27  Index Matching       : 0.00
% 1.95/1.27  BG Taut test         : 0.00
%------------------------------------------------------------------------------

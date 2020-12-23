%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:15 EST 2020

% Result     : Theorem 1.87s
% Output     : CNFRefutation 1.96s
% Verified   : 
% Statistics : Number of formulae       :   50 (  62 expanded)
%              Number of leaves         :   27 (  34 expanded)
%              Depth                    :    7
%              Number of atoms          :   51 (  65 expanded)
%              Number of equality atoms :   20 (  31 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_partfun1 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k9_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_funct_1 > k1_zfmisc_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(k2_funct_1,type,(
    k2_funct_1: $i > $i )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k8_relset_1,type,(
    k8_relset_1: ( $i * $i * $i * $i ) > $i )).

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

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_62,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => k8_relset_1(A,A,k6_partfun1(A),B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t171_funct_2)).

tff(f_57,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_33,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v2_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).

tff(f_29,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_47,axiom,(
    ! [A] : k2_funct_1(k6_relat_1(A)) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_funct_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( v2_funct_1(B)
       => k10_relat_1(B,A) = k9_relat_1(k2_funct_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t155_funct_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k9_relat_1(k6_relat_1(A),B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t162_funct_1)).

tff(f_55,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_51,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(c_26,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_22,plain,(
    ! [A_13] : k6_relat_1(A_13) = k6_partfun1(A_13) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_6,plain,(
    ! [A_2] : v1_relat_1(k6_relat_1(A_2)) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_30,plain,(
    ! [A_2] : v1_relat_1(k6_partfun1(A_2)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_6])).

tff(c_4,plain,(
    ! [A_1] : v1_funct_1(k6_relat_1(A_1)) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_31,plain,(
    ! [A_1] : v1_funct_1(k6_partfun1(A_1)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_4])).

tff(c_8,plain,(
    ! [A_2] : v2_funct_1(k6_relat_1(A_2)) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_29,plain,(
    ! [A_2] : v2_funct_1(k6_partfun1(A_2)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_8])).

tff(c_14,plain,(
    ! [A_7] : k2_funct_1(k6_relat_1(A_7)) = k6_relat_1(A_7) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_27,plain,(
    ! [A_7] : k2_funct_1(k6_partfun1(A_7)) = k6_partfun1(A_7) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_22,c_14])).

tff(c_56,plain,(
    ! [B_21,A_22] :
      ( k9_relat_1(k2_funct_1(B_21),A_22) = k10_relat_1(B_21,A_22)
      | ~ v2_funct_1(B_21)
      | ~ v1_funct_1(B_21)
      | ~ v1_relat_1(B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_65,plain,(
    ! [A_7,A_22] :
      ( k9_relat_1(k6_partfun1(A_7),A_22) = k10_relat_1(k6_partfun1(A_7),A_22)
      | ~ v2_funct_1(k6_partfun1(A_7))
      | ~ v1_funct_1(k6_partfun1(A_7))
      | ~ v1_relat_1(k6_partfun1(A_7)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_27,c_56])).

tff(c_69,plain,(
    ! [A_7,A_22] : k9_relat_1(k6_partfun1(A_7),A_22) = k10_relat_1(k6_partfun1(A_7),A_22) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_31,c_29,c_65])).

tff(c_12,plain,(
    ! [A_5,B_6] :
      ( k9_relat_1(k6_relat_1(A_5),B_6) = B_6
      | ~ m1_subset_1(B_6,k1_zfmisc_1(A_5)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_28,plain,(
    ! [A_5,B_6] :
      ( k9_relat_1(k6_partfun1(A_5),B_6) = B_6
      | ~ m1_subset_1(B_6,k1_zfmisc_1(A_5)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_12])).

tff(c_80,plain,(
    ! [A_25,B_26] :
      ( k10_relat_1(k6_partfun1(A_25),B_26) = B_26
      | ~ m1_subset_1(B_26,k1_zfmisc_1(A_25)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_69,c_28])).

tff(c_88,plain,(
    k10_relat_1(k6_partfun1('#skF_1'),'#skF_2') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_26,c_80])).

tff(c_20,plain,(
    ! [A_12] : m1_subset_1(k6_partfun1(A_12),k1_zfmisc_1(k2_zfmisc_1(A_12,A_12))) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_102,plain,(
    ! [A_28,B_29,C_30,D_31] :
      ( k8_relset_1(A_28,B_29,C_30,D_31) = k10_relat_1(C_30,D_31)
      | ~ m1_subset_1(C_30,k1_zfmisc_1(k2_zfmisc_1(A_28,B_29))) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_105,plain,(
    ! [A_12,D_31] : k8_relset_1(A_12,A_12,k6_partfun1(A_12),D_31) = k10_relat_1(k6_partfun1(A_12),D_31) ),
    inference(resolution,[status(thm)],[c_20,c_102])).

tff(c_24,plain,(
    k8_relset_1('#skF_1','#skF_1',k6_partfun1('#skF_1'),'#skF_2') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_106,plain,(
    k10_relat_1(k6_partfun1('#skF_1'),'#skF_2') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_105,c_24])).

tff(c_109,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_106])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.13/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n022.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 14:02:10 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.87/1.23  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.96/1.24  
% 1.96/1.24  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.96/1.24  %$ v1_partfun1 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k9_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_funct_1 > k1_zfmisc_1 > #skF_2 > #skF_1
% 1.96/1.24  
% 1.96/1.24  %Foreground sorts:
% 1.96/1.24  
% 1.96/1.24  
% 1.96/1.24  %Background operators:
% 1.96/1.24  
% 1.96/1.24  
% 1.96/1.24  %Foreground operators:
% 1.96/1.24  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.96/1.24  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 1.96/1.24  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 1.96/1.24  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.96/1.24  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 1.96/1.24  tff('#skF_2', type, '#skF_2': $i).
% 1.96/1.24  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 1.96/1.24  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 1.96/1.24  tff('#skF_1', type, '#skF_1': $i).
% 1.96/1.24  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.96/1.24  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 1.96/1.24  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.96/1.24  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 1.96/1.24  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.96/1.24  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.96/1.24  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 1.96/1.24  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.96/1.24  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.96/1.24  
% 1.96/1.25  tff(f_62, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k8_relset_1(A, A, k6_partfun1(A), B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t171_funct_2)).
% 1.96/1.25  tff(f_57, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 1.96/1.25  tff(f_33, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v2_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc4_funct_1)).
% 1.96/1.25  tff(f_29, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc3_funct_1)).
% 1.96/1.25  tff(f_47, axiom, (![A]: (k2_funct_1(k6_relat_1(A)) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t67_funct_1)).
% 1.96/1.25  tff(f_41, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (v2_funct_1(B) => (k10_relat_1(B, A) = k9_relat_1(k2_funct_1(B), A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t155_funct_1)).
% 1.96/1.25  tff(f_45, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k9_relat_1(k6_relat_1(A), B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t162_funct_1)).
% 1.96/1.25  tff(f_55, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 1.96/1.25  tff(f_51, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 1.96/1.25  tff(c_26, plain, (m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_62])).
% 1.96/1.25  tff(c_22, plain, (![A_13]: (k6_relat_1(A_13)=k6_partfun1(A_13))), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.96/1.25  tff(c_6, plain, (![A_2]: (v1_relat_1(k6_relat_1(A_2)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.96/1.25  tff(c_30, plain, (![A_2]: (v1_relat_1(k6_partfun1(A_2)))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_6])).
% 1.96/1.25  tff(c_4, plain, (![A_1]: (v1_funct_1(k6_relat_1(A_1)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.96/1.25  tff(c_31, plain, (![A_1]: (v1_funct_1(k6_partfun1(A_1)))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_4])).
% 1.96/1.25  tff(c_8, plain, (![A_2]: (v2_funct_1(k6_relat_1(A_2)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.96/1.25  tff(c_29, plain, (![A_2]: (v2_funct_1(k6_partfun1(A_2)))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_8])).
% 1.96/1.25  tff(c_14, plain, (![A_7]: (k2_funct_1(k6_relat_1(A_7))=k6_relat_1(A_7))), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.96/1.25  tff(c_27, plain, (![A_7]: (k2_funct_1(k6_partfun1(A_7))=k6_partfun1(A_7))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_22, c_14])).
% 1.96/1.25  tff(c_56, plain, (![B_21, A_22]: (k9_relat_1(k2_funct_1(B_21), A_22)=k10_relat_1(B_21, A_22) | ~v2_funct_1(B_21) | ~v1_funct_1(B_21) | ~v1_relat_1(B_21))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.96/1.25  tff(c_65, plain, (![A_7, A_22]: (k9_relat_1(k6_partfun1(A_7), A_22)=k10_relat_1(k6_partfun1(A_7), A_22) | ~v2_funct_1(k6_partfun1(A_7)) | ~v1_funct_1(k6_partfun1(A_7)) | ~v1_relat_1(k6_partfun1(A_7)))), inference(superposition, [status(thm), theory('equality')], [c_27, c_56])).
% 1.96/1.25  tff(c_69, plain, (![A_7, A_22]: (k9_relat_1(k6_partfun1(A_7), A_22)=k10_relat_1(k6_partfun1(A_7), A_22))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_31, c_29, c_65])).
% 1.96/1.25  tff(c_12, plain, (![A_5, B_6]: (k9_relat_1(k6_relat_1(A_5), B_6)=B_6 | ~m1_subset_1(B_6, k1_zfmisc_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.96/1.25  tff(c_28, plain, (![A_5, B_6]: (k9_relat_1(k6_partfun1(A_5), B_6)=B_6 | ~m1_subset_1(B_6, k1_zfmisc_1(A_5)))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_12])).
% 1.96/1.25  tff(c_80, plain, (![A_25, B_26]: (k10_relat_1(k6_partfun1(A_25), B_26)=B_26 | ~m1_subset_1(B_26, k1_zfmisc_1(A_25)))), inference(demodulation, [status(thm), theory('equality')], [c_69, c_28])).
% 1.96/1.25  tff(c_88, plain, (k10_relat_1(k6_partfun1('#skF_1'), '#skF_2')='#skF_2'), inference(resolution, [status(thm)], [c_26, c_80])).
% 1.96/1.25  tff(c_20, plain, (![A_12]: (m1_subset_1(k6_partfun1(A_12), k1_zfmisc_1(k2_zfmisc_1(A_12, A_12))))), inference(cnfTransformation, [status(thm)], [f_55])).
% 1.96/1.25  tff(c_102, plain, (![A_28, B_29, C_30, D_31]: (k8_relset_1(A_28, B_29, C_30, D_31)=k10_relat_1(C_30, D_31) | ~m1_subset_1(C_30, k1_zfmisc_1(k2_zfmisc_1(A_28, B_29))))), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.96/1.25  tff(c_105, plain, (![A_12, D_31]: (k8_relset_1(A_12, A_12, k6_partfun1(A_12), D_31)=k10_relat_1(k6_partfun1(A_12), D_31))), inference(resolution, [status(thm)], [c_20, c_102])).
% 1.96/1.25  tff(c_24, plain, (k8_relset_1('#skF_1', '#skF_1', k6_partfun1('#skF_1'), '#skF_2')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_62])).
% 1.96/1.25  tff(c_106, plain, (k10_relat_1(k6_partfun1('#skF_1'), '#skF_2')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_105, c_24])).
% 1.96/1.25  tff(c_109, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_88, c_106])).
% 1.96/1.25  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.96/1.25  
% 1.96/1.25  Inference rules
% 1.96/1.25  ----------------------
% 1.96/1.25  #Ref     : 0
% 1.96/1.25  #Sup     : 16
% 1.96/1.25  #Fact    : 0
% 1.96/1.25  #Define  : 0
% 1.96/1.25  #Split   : 0
% 1.96/1.25  #Chain   : 0
% 1.96/1.25  #Close   : 0
% 1.96/1.25  
% 1.96/1.25  Ordering : KBO
% 1.96/1.25  
% 1.96/1.25  Simplification rules
% 1.96/1.25  ----------------------
% 1.96/1.25  #Subsume      : 0
% 1.96/1.25  #Demod        : 14
% 1.96/1.25  #Tautology    : 13
% 1.96/1.25  #SimpNegUnit  : 0
% 1.96/1.25  #BackRed      : 1
% 1.96/1.25  
% 1.96/1.25  #Partial instantiations: 0
% 1.96/1.25  #Strategies tried      : 1
% 1.96/1.25  
% 1.96/1.25  Timing (in seconds)
% 1.96/1.25  ----------------------
% 1.96/1.25  Preprocessing        : 0.30
% 1.96/1.25  Parsing              : 0.17
% 1.96/1.25  CNF conversion       : 0.02
% 1.96/1.25  Main loop            : 0.10
% 1.96/1.25  Inferencing          : 0.04
% 1.96/1.25  Reduction            : 0.04
% 1.96/1.25  Demodulation         : 0.03
% 1.96/1.25  BG Simplification    : 0.01
% 1.96/1.25  Subsumption          : 0.01
% 1.96/1.25  Abstraction          : 0.01
% 1.96/1.25  MUC search           : 0.00
% 1.96/1.25  Cooper               : 0.00
% 1.96/1.25  Total                : 0.44
% 1.96/1.25  Index Insertion      : 0.00
% 1.96/1.25  Index Deletion       : 0.00
% 1.96/1.25  Index Matching       : 0.00
% 1.96/1.25  BG Taut test         : 0.00
%------------------------------------------------------------------------------

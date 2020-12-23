%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:17 EST 2020

% Result     : Theorem 1.91s
% Output     : CNFRefutation 1.91s
% Verified   : 
% Statistics : Number of formulae       :   50 (  64 expanded)
%              Number of leaves         :   26 (  34 expanded)
%              Depth                    :    6
%              Number of atoms          :   50 (  66 expanded)
%              Number of equality atoms :   20 (  33 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k9_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_funct_1 > k1_zfmisc_1 > #skF_2 > #skF_1

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

tff(f_55,axiom,(
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
       => k9_relat_1(B,A) = k10_relat_1(k2_funct_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t154_funct_1)).

tff(f_60,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => k8_relset_1(A,A,k6_partfun1(A),B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t171_funct_2)).

tff(f_45,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k9_relat_1(k6_relat_1(A),B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t162_funct_1)).

tff(f_53,axiom,(
    ! [A] : m1_subset_1(k6_relat_1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_relset_1)).

tff(f_51,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(c_20,plain,(
    ! [A_13] : k6_relat_1(A_13) = k6_partfun1(A_13) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_6,plain,(
    ! [A_2] : v1_relat_1(k6_relat_1(A_2)) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_29,plain,(
    ! [A_2] : v1_relat_1(k6_partfun1(A_2)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_6])).

tff(c_4,plain,(
    ! [A_1] : v1_funct_1(k6_relat_1(A_1)) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_30,plain,(
    ! [A_1] : v1_funct_1(k6_partfun1(A_1)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_4])).

tff(c_8,plain,(
    ! [A_2] : v2_funct_1(k6_relat_1(A_2)) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_28,plain,(
    ! [A_2] : v2_funct_1(k6_partfun1(A_2)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_8])).

tff(c_14,plain,(
    ! [A_7] : k2_funct_1(k6_relat_1(A_7)) = k6_relat_1(A_7) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_26,plain,(
    ! [A_7] : k2_funct_1(k6_partfun1(A_7)) = k6_partfun1(A_7) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_20,c_14])).

tff(c_76,plain,(
    ! [B_23,A_24] :
      ( k10_relat_1(k2_funct_1(B_23),A_24) = k9_relat_1(B_23,A_24)
      | ~ v2_funct_1(B_23)
      | ~ v1_funct_1(B_23)
      | ~ v1_relat_1(B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_85,plain,(
    ! [A_7,A_24] :
      ( k9_relat_1(k6_partfun1(A_7),A_24) = k10_relat_1(k6_partfun1(A_7),A_24)
      | ~ v2_funct_1(k6_partfun1(A_7))
      | ~ v1_funct_1(k6_partfun1(A_7))
      | ~ v1_relat_1(k6_partfun1(A_7)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_76])).

tff(c_91,plain,(
    ! [A_25,A_26] : k9_relat_1(k6_partfun1(A_25),A_26) = k10_relat_1(k6_partfun1(A_25),A_26) ),
    inference(demodulation,[status(thm),theory(equality)],[c_29,c_30,c_28,c_85])).

tff(c_24,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_12,plain,(
    ! [A_5,B_6] :
      ( k9_relat_1(k6_relat_1(A_5),B_6) = B_6
      | ~ m1_subset_1(B_6,k1_zfmisc_1(A_5)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_54,plain,(
    ! [A_20,B_21] :
      ( k9_relat_1(k6_partfun1(A_20),B_21) = B_21
      | ~ m1_subset_1(B_21,k1_zfmisc_1(A_20)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_12])).

tff(c_62,plain,(
    k9_relat_1(k6_partfun1('#skF_1'),'#skF_2') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_24,c_54])).

tff(c_100,plain,(
    k10_relat_1(k6_partfun1('#skF_1'),'#skF_2') = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_91,c_62])).

tff(c_18,plain,(
    ! [A_12] : m1_subset_1(k6_relat_1(A_12),k1_zfmisc_1(k2_zfmisc_1(A_12,A_12))) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_25,plain,(
    ! [A_12] : m1_subset_1(k6_partfun1(A_12),k1_zfmisc_1(k2_zfmisc_1(A_12,A_12))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_18])).

tff(c_117,plain,(
    ! [A_27,B_28,C_29,D_30] :
      ( k8_relset_1(A_27,B_28,C_29,D_30) = k10_relat_1(C_29,D_30)
      | ~ m1_subset_1(C_29,k1_zfmisc_1(k2_zfmisc_1(A_27,B_28))) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_120,plain,(
    ! [A_12,D_30] : k8_relset_1(A_12,A_12,k6_partfun1(A_12),D_30) = k10_relat_1(k6_partfun1(A_12),D_30) ),
    inference(resolution,[status(thm)],[c_25,c_117])).

tff(c_22,plain,(
    k8_relset_1('#skF_1','#skF_1',k6_partfun1('#skF_1'),'#skF_2') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_141,plain,(
    k10_relat_1(k6_partfun1('#skF_1'),'#skF_2') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_120,c_22])).

tff(c_144,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_141])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.35  % Computer   : n007.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 20:06:21 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.91/1.32  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.91/1.32  
% 1.91/1.32  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.91/1.32  %$ m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k9_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_funct_1 > k1_zfmisc_1 > #skF_2 > #skF_1
% 1.91/1.32  
% 1.91/1.32  %Foreground sorts:
% 1.91/1.32  
% 1.91/1.32  
% 1.91/1.32  %Background operators:
% 1.91/1.32  
% 1.91/1.32  
% 1.91/1.32  %Foreground operators:
% 1.91/1.32  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.91/1.32  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 1.91/1.32  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 1.91/1.32  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.91/1.32  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 1.91/1.32  tff('#skF_2', type, '#skF_2': $i).
% 1.91/1.32  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 1.91/1.32  tff('#skF_1', type, '#skF_1': $i).
% 1.91/1.32  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.91/1.32  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 1.91/1.32  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.91/1.32  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 1.91/1.32  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.91/1.32  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.91/1.32  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 1.91/1.32  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.91/1.32  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.91/1.32  
% 1.91/1.34  tff(f_55, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 1.91/1.34  tff(f_33, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v2_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc4_funct_1)).
% 1.91/1.34  tff(f_29, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc3_funct_1)).
% 1.91/1.34  tff(f_47, axiom, (![A]: (k2_funct_1(k6_relat_1(A)) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t67_funct_1)).
% 1.91/1.34  tff(f_41, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (v2_funct_1(B) => (k9_relat_1(B, A) = k10_relat_1(k2_funct_1(B), A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t154_funct_1)).
% 1.91/1.34  tff(f_60, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k8_relset_1(A, A, k6_partfun1(A), B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t171_funct_2)).
% 1.91/1.34  tff(f_45, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k9_relat_1(k6_relat_1(A), B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t162_funct_1)).
% 1.91/1.34  tff(f_53, axiom, (![A]: m1_subset_1(k6_relat_1(A), k1_zfmisc_1(k2_zfmisc_1(A, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_relset_1)).
% 1.91/1.34  tff(f_51, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 1.91/1.34  tff(c_20, plain, (![A_13]: (k6_relat_1(A_13)=k6_partfun1(A_13))), inference(cnfTransformation, [status(thm)], [f_55])).
% 1.91/1.34  tff(c_6, plain, (![A_2]: (v1_relat_1(k6_relat_1(A_2)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.91/1.34  tff(c_29, plain, (![A_2]: (v1_relat_1(k6_partfun1(A_2)))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_6])).
% 1.91/1.34  tff(c_4, plain, (![A_1]: (v1_funct_1(k6_relat_1(A_1)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.91/1.34  tff(c_30, plain, (![A_1]: (v1_funct_1(k6_partfun1(A_1)))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_4])).
% 1.91/1.34  tff(c_8, plain, (![A_2]: (v2_funct_1(k6_relat_1(A_2)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.91/1.34  tff(c_28, plain, (![A_2]: (v2_funct_1(k6_partfun1(A_2)))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_8])).
% 1.91/1.34  tff(c_14, plain, (![A_7]: (k2_funct_1(k6_relat_1(A_7))=k6_relat_1(A_7))), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.91/1.34  tff(c_26, plain, (![A_7]: (k2_funct_1(k6_partfun1(A_7))=k6_partfun1(A_7))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_20, c_14])).
% 1.91/1.34  tff(c_76, plain, (![B_23, A_24]: (k10_relat_1(k2_funct_1(B_23), A_24)=k9_relat_1(B_23, A_24) | ~v2_funct_1(B_23) | ~v1_funct_1(B_23) | ~v1_relat_1(B_23))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.91/1.34  tff(c_85, plain, (![A_7, A_24]: (k9_relat_1(k6_partfun1(A_7), A_24)=k10_relat_1(k6_partfun1(A_7), A_24) | ~v2_funct_1(k6_partfun1(A_7)) | ~v1_funct_1(k6_partfun1(A_7)) | ~v1_relat_1(k6_partfun1(A_7)))), inference(superposition, [status(thm), theory('equality')], [c_26, c_76])).
% 1.91/1.34  tff(c_91, plain, (![A_25, A_26]: (k9_relat_1(k6_partfun1(A_25), A_26)=k10_relat_1(k6_partfun1(A_25), A_26))), inference(demodulation, [status(thm), theory('equality')], [c_29, c_30, c_28, c_85])).
% 1.91/1.34  tff(c_24, plain, (m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_60])).
% 1.91/1.34  tff(c_12, plain, (![A_5, B_6]: (k9_relat_1(k6_relat_1(A_5), B_6)=B_6 | ~m1_subset_1(B_6, k1_zfmisc_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.91/1.34  tff(c_54, plain, (![A_20, B_21]: (k9_relat_1(k6_partfun1(A_20), B_21)=B_21 | ~m1_subset_1(B_21, k1_zfmisc_1(A_20)))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_12])).
% 1.91/1.34  tff(c_62, plain, (k9_relat_1(k6_partfun1('#skF_1'), '#skF_2')='#skF_2'), inference(resolution, [status(thm)], [c_24, c_54])).
% 1.91/1.34  tff(c_100, plain, (k10_relat_1(k6_partfun1('#skF_1'), '#skF_2')='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_91, c_62])).
% 1.91/1.34  tff(c_18, plain, (![A_12]: (m1_subset_1(k6_relat_1(A_12), k1_zfmisc_1(k2_zfmisc_1(A_12, A_12))))), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.91/1.34  tff(c_25, plain, (![A_12]: (m1_subset_1(k6_partfun1(A_12), k1_zfmisc_1(k2_zfmisc_1(A_12, A_12))))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_18])).
% 1.91/1.34  tff(c_117, plain, (![A_27, B_28, C_29, D_30]: (k8_relset_1(A_27, B_28, C_29, D_30)=k10_relat_1(C_29, D_30) | ~m1_subset_1(C_29, k1_zfmisc_1(k2_zfmisc_1(A_27, B_28))))), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.91/1.34  tff(c_120, plain, (![A_12, D_30]: (k8_relset_1(A_12, A_12, k6_partfun1(A_12), D_30)=k10_relat_1(k6_partfun1(A_12), D_30))), inference(resolution, [status(thm)], [c_25, c_117])).
% 1.91/1.34  tff(c_22, plain, (k8_relset_1('#skF_1', '#skF_1', k6_partfun1('#skF_1'), '#skF_2')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_60])).
% 1.91/1.34  tff(c_141, plain, (k10_relat_1(k6_partfun1('#skF_1'), '#skF_2')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_120, c_22])).
% 1.91/1.34  tff(c_144, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_100, c_141])).
% 1.91/1.34  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.91/1.34  
% 1.91/1.34  Inference rules
% 1.91/1.34  ----------------------
% 1.91/1.34  #Ref     : 0
% 1.91/1.34  #Sup     : 26
% 1.91/1.34  #Fact    : 0
% 1.91/1.34  #Define  : 0
% 1.91/1.34  #Split   : 0
% 1.91/1.34  #Chain   : 0
% 1.91/1.34  #Close   : 0
% 1.91/1.34  
% 1.91/1.34  Ordering : KBO
% 1.91/1.34  
% 1.91/1.34  Simplification rules
% 1.91/1.34  ----------------------
% 1.91/1.34  #Subsume      : 0
% 1.91/1.34  #Demod        : 18
% 1.91/1.34  #Tautology    : 20
% 1.91/1.34  #SimpNegUnit  : 0
% 1.91/1.34  #BackRed      : 2
% 1.91/1.34  
% 1.91/1.34  #Partial instantiations: 0
% 1.91/1.34  #Strategies tried      : 1
% 1.91/1.34  
% 1.91/1.34  Timing (in seconds)
% 1.91/1.34  ----------------------
% 1.91/1.34  Preprocessing        : 0.31
% 1.91/1.34  Parsing              : 0.16
% 1.91/1.34  CNF conversion       : 0.02
% 1.91/1.34  Main loop            : 0.12
% 1.91/1.34  Inferencing          : 0.05
% 1.91/1.34  Reduction            : 0.04
% 1.91/1.34  Demodulation         : 0.03
% 1.91/1.34  BG Simplification    : 0.01
% 1.91/1.34  Subsumption          : 0.01
% 1.91/1.34  Abstraction          : 0.01
% 1.91/1.34  MUC search           : 0.00
% 1.91/1.34  Cooper               : 0.00
% 1.91/1.34  Total                : 0.47
% 1.91/1.34  Index Insertion      : 0.00
% 1.91/1.34  Index Deletion       : 0.00
% 1.91/1.34  Index Matching       : 0.00
% 1.91/1.34  BG Taut test         : 0.00
%------------------------------------------------------------------------------

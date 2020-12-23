%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:15 EST 2020

% Result     : Theorem 2.25s
% Output     : CNFRefutation 2.46s
% Verified   : 
% Statistics : Number of formulae       :   51 (  76 expanded)
%              Number of leaves         :   27 (  38 expanded)
%              Depth                    :    8
%              Number of atoms          :   59 (  87 expanded)
%              Number of equality atoms :   23 (  44 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_partfun1 > r1_tarski > m1_subset_1 > v1_relat_1 > k8_relset_1 > k5_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k8_relset_1,type,(
    k8_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

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

tff(f_63,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => k8_relset_1(A,A,k6_partfun1(A),B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t171_funct_2)).

tff(f_29,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_58,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_31,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_42,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k5_relat_1(k6_relat_1(A),B) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_relat_1)).

tff(f_38,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k1_relat_1(k5_relat_1(A,B)) = k10_relat_1(A,k1_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t182_relat_1)).

tff(f_56,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_52,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(c_26,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_62,plain,(
    ! [A_24,B_25] :
      ( r1_tarski(A_24,B_25)
      | ~ m1_subset_1(A_24,k1_zfmisc_1(B_25)) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_74,plain,(
    r1_tarski('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_26,c_62])).

tff(c_22,plain,(
    ! [A_15] : k6_relat_1(A_15) = k6_partfun1(A_15) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_6,plain,(
    ! [A_3] : v1_relat_1(k6_relat_1(A_3)) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_30,plain,(
    ! [A_3] : v1_relat_1(k6_partfun1(A_3)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_6])).

tff(c_10,plain,(
    ! [A_7] : k1_relat_1(k6_relat_1(A_7)) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_29,plain,(
    ! [A_7] : k1_relat_1(k6_partfun1(A_7)) = A_7 ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_10])).

tff(c_14,plain,(
    ! [A_8,B_9] :
      ( k5_relat_1(k6_relat_1(A_8),B_9) = B_9
      | ~ r1_tarski(k1_relat_1(B_9),A_8)
      | ~ v1_relat_1(B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_76,plain,(
    ! [A_27,B_28] :
      ( k5_relat_1(k6_partfun1(A_27),B_28) = B_28
      | ~ r1_tarski(k1_relat_1(B_28),A_27)
      | ~ v1_relat_1(B_28) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_14])).

tff(c_79,plain,(
    ! [A_27,A_7] :
      ( k5_relat_1(k6_partfun1(A_27),k6_partfun1(A_7)) = k6_partfun1(A_7)
      | ~ r1_tarski(A_7,A_27)
      | ~ v1_relat_1(k6_partfun1(A_7)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_29,c_76])).

tff(c_81,plain,(
    ! [A_27,A_7] :
      ( k5_relat_1(k6_partfun1(A_27),k6_partfun1(A_7)) = k6_partfun1(A_7)
      | ~ r1_tarski(A_7,A_27) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_79])).

tff(c_91,plain,(
    ! [A_31,B_32] :
      ( k10_relat_1(A_31,k1_relat_1(B_32)) = k1_relat_1(k5_relat_1(A_31,B_32))
      | ~ v1_relat_1(B_32)
      | ~ v1_relat_1(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_100,plain,(
    ! [A_31,A_7] :
      ( k1_relat_1(k5_relat_1(A_31,k6_partfun1(A_7))) = k10_relat_1(A_31,A_7)
      | ~ v1_relat_1(k6_partfun1(A_7))
      | ~ v1_relat_1(A_31) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_29,c_91])).

tff(c_113,plain,(
    ! [A_37,A_38] :
      ( k1_relat_1(k5_relat_1(A_37,k6_partfun1(A_38))) = k10_relat_1(A_37,A_38)
      | ~ v1_relat_1(A_37) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_100])).

tff(c_128,plain,(
    ! [A_27,A_7] :
      ( k10_relat_1(k6_partfun1(A_27),A_7) = k1_relat_1(k6_partfun1(A_7))
      | ~ v1_relat_1(k6_partfun1(A_27))
      | ~ r1_tarski(A_7,A_27) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_81,c_113])).

tff(c_132,plain,(
    ! [A_27,A_7] :
      ( k10_relat_1(k6_partfun1(A_27),A_7) = A_7
      | ~ r1_tarski(A_7,A_27) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_29,c_128])).

tff(c_20,plain,(
    ! [A_14] : m1_subset_1(k6_partfun1(A_14),k1_zfmisc_1(k2_zfmisc_1(A_14,A_14))) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_105,plain,(
    ! [A_33,B_34,C_35,D_36] :
      ( k8_relset_1(A_33,B_34,C_35,D_36) = k10_relat_1(C_35,D_36)
      | ~ m1_subset_1(C_35,k1_zfmisc_1(k2_zfmisc_1(A_33,B_34))) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_111,plain,(
    ! [A_14,D_36] : k8_relset_1(A_14,A_14,k6_partfun1(A_14),D_36) = k10_relat_1(k6_partfun1(A_14),D_36) ),
    inference(resolution,[status(thm)],[c_20,c_105])).

tff(c_24,plain,(
    k8_relset_1('#skF_1','#skF_1',k6_partfun1('#skF_1'),'#skF_2') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_154,plain,(
    k10_relat_1(k6_partfun1('#skF_1'),'#skF_2') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_111,c_24])).

tff(c_166,plain,(
    ~ r1_tarski('#skF_2','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_132,c_154])).

tff(c_170,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_166])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n022.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 15:57:56 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.25/1.64  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.46/1.65  
% 2.46/1.65  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.46/1.65  %$ v1_partfun1 > r1_tarski > m1_subset_1 > v1_relat_1 > k8_relset_1 > k5_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_1
% 2.46/1.65  
% 2.46/1.65  %Foreground sorts:
% 2.46/1.65  
% 2.46/1.65  
% 2.46/1.65  %Background operators:
% 2.46/1.65  
% 2.46/1.65  
% 2.46/1.65  %Foreground operators:
% 2.46/1.65  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.46/1.65  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 2.46/1.65  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.46/1.65  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.46/1.65  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.46/1.65  tff('#skF_2', type, '#skF_2': $i).
% 2.46/1.65  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 2.46/1.65  tff('#skF_1', type, '#skF_1': $i).
% 2.46/1.65  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.46/1.65  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 2.46/1.65  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.46/1.65  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.46/1.65  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.46/1.65  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.46/1.65  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.46/1.65  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.46/1.65  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.46/1.65  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.46/1.65  
% 2.46/1.67  tff(f_63, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k8_relset_1(A, A, k6_partfun1(A), B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t171_funct_2)).
% 2.46/1.67  tff(f_29, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 2.46/1.67  tff(f_58, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 2.46/1.67  tff(f_31, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 2.46/1.67  tff(f_42, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 2.46/1.67  tff(f_48, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k5_relat_1(k6_relat_1(A), B) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t77_relat_1)).
% 2.46/1.67  tff(f_38, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k1_relat_1(k5_relat_1(A, B)) = k10_relat_1(A, k1_relat_1(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t182_relat_1)).
% 2.46/1.67  tff(f_56, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 2.46/1.67  tff(f_52, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 2.46/1.67  tff(c_26, plain, (m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.46/1.67  tff(c_62, plain, (![A_24, B_25]: (r1_tarski(A_24, B_25) | ~m1_subset_1(A_24, k1_zfmisc_1(B_25)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.46/1.67  tff(c_74, plain, (r1_tarski('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_26, c_62])).
% 2.46/1.67  tff(c_22, plain, (![A_15]: (k6_relat_1(A_15)=k6_partfun1(A_15))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.46/1.67  tff(c_6, plain, (![A_3]: (v1_relat_1(k6_relat_1(A_3)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.46/1.67  tff(c_30, plain, (![A_3]: (v1_relat_1(k6_partfun1(A_3)))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_6])).
% 2.46/1.67  tff(c_10, plain, (![A_7]: (k1_relat_1(k6_relat_1(A_7))=A_7)), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.46/1.67  tff(c_29, plain, (![A_7]: (k1_relat_1(k6_partfun1(A_7))=A_7)), inference(demodulation, [status(thm), theory('equality')], [c_22, c_10])).
% 2.46/1.67  tff(c_14, plain, (![A_8, B_9]: (k5_relat_1(k6_relat_1(A_8), B_9)=B_9 | ~r1_tarski(k1_relat_1(B_9), A_8) | ~v1_relat_1(B_9))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.46/1.67  tff(c_76, plain, (![A_27, B_28]: (k5_relat_1(k6_partfun1(A_27), B_28)=B_28 | ~r1_tarski(k1_relat_1(B_28), A_27) | ~v1_relat_1(B_28))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_14])).
% 2.46/1.67  tff(c_79, plain, (![A_27, A_7]: (k5_relat_1(k6_partfun1(A_27), k6_partfun1(A_7))=k6_partfun1(A_7) | ~r1_tarski(A_7, A_27) | ~v1_relat_1(k6_partfun1(A_7)))), inference(superposition, [status(thm), theory('equality')], [c_29, c_76])).
% 2.46/1.67  tff(c_81, plain, (![A_27, A_7]: (k5_relat_1(k6_partfun1(A_27), k6_partfun1(A_7))=k6_partfun1(A_7) | ~r1_tarski(A_7, A_27))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_79])).
% 2.46/1.67  tff(c_91, plain, (![A_31, B_32]: (k10_relat_1(A_31, k1_relat_1(B_32))=k1_relat_1(k5_relat_1(A_31, B_32)) | ~v1_relat_1(B_32) | ~v1_relat_1(A_31))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.46/1.67  tff(c_100, plain, (![A_31, A_7]: (k1_relat_1(k5_relat_1(A_31, k6_partfun1(A_7)))=k10_relat_1(A_31, A_7) | ~v1_relat_1(k6_partfun1(A_7)) | ~v1_relat_1(A_31))), inference(superposition, [status(thm), theory('equality')], [c_29, c_91])).
% 2.46/1.67  tff(c_113, plain, (![A_37, A_38]: (k1_relat_1(k5_relat_1(A_37, k6_partfun1(A_38)))=k10_relat_1(A_37, A_38) | ~v1_relat_1(A_37))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_100])).
% 2.46/1.67  tff(c_128, plain, (![A_27, A_7]: (k10_relat_1(k6_partfun1(A_27), A_7)=k1_relat_1(k6_partfun1(A_7)) | ~v1_relat_1(k6_partfun1(A_27)) | ~r1_tarski(A_7, A_27))), inference(superposition, [status(thm), theory('equality')], [c_81, c_113])).
% 2.46/1.67  tff(c_132, plain, (![A_27, A_7]: (k10_relat_1(k6_partfun1(A_27), A_7)=A_7 | ~r1_tarski(A_7, A_27))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_29, c_128])).
% 2.46/1.67  tff(c_20, plain, (![A_14]: (m1_subset_1(k6_partfun1(A_14), k1_zfmisc_1(k2_zfmisc_1(A_14, A_14))))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.46/1.67  tff(c_105, plain, (![A_33, B_34, C_35, D_36]: (k8_relset_1(A_33, B_34, C_35, D_36)=k10_relat_1(C_35, D_36) | ~m1_subset_1(C_35, k1_zfmisc_1(k2_zfmisc_1(A_33, B_34))))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.46/1.67  tff(c_111, plain, (![A_14, D_36]: (k8_relset_1(A_14, A_14, k6_partfun1(A_14), D_36)=k10_relat_1(k6_partfun1(A_14), D_36))), inference(resolution, [status(thm)], [c_20, c_105])).
% 2.46/1.67  tff(c_24, plain, (k8_relset_1('#skF_1', '#skF_1', k6_partfun1('#skF_1'), '#skF_2')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.46/1.67  tff(c_154, plain, (k10_relat_1(k6_partfun1('#skF_1'), '#skF_2')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_111, c_24])).
% 2.46/1.67  tff(c_166, plain, (~r1_tarski('#skF_2', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_132, c_154])).
% 2.46/1.67  tff(c_170, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_74, c_166])).
% 2.46/1.67  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.46/1.67  
% 2.46/1.67  Inference rules
% 2.46/1.67  ----------------------
% 2.46/1.67  #Ref     : 0
% 2.46/1.67  #Sup     : 29
% 2.46/1.67  #Fact    : 0
% 2.46/1.67  #Define  : 0
% 2.46/1.67  #Split   : 0
% 2.46/1.67  #Chain   : 0
% 2.46/1.67  #Close   : 0
% 2.46/1.67  
% 2.46/1.67  Ordering : KBO
% 2.46/1.67  
% 2.46/1.67  Simplification rules
% 2.46/1.67  ----------------------
% 2.46/1.67  #Subsume      : 0
% 2.46/1.67  #Demod        : 12
% 2.46/1.67  #Tautology    : 17
% 2.46/1.67  #SimpNegUnit  : 0
% 2.46/1.67  #BackRed      : 1
% 2.46/1.67  
% 2.46/1.67  #Partial instantiations: 0
% 2.46/1.67  #Strategies tried      : 1
% 2.46/1.67  
% 2.46/1.67  Timing (in seconds)
% 2.46/1.67  ----------------------
% 2.46/1.68  Preprocessing        : 0.50
% 2.46/1.68  Parsing              : 0.26
% 2.46/1.68  CNF conversion       : 0.03
% 2.46/1.68  Main loop            : 0.24
% 2.46/1.68  Inferencing          : 0.10
% 2.46/1.68  Reduction            : 0.07
% 2.46/1.68  Demodulation         : 0.06
% 2.46/1.68  BG Simplification    : 0.02
% 2.46/1.68  Subsumption          : 0.03
% 2.46/1.68  Abstraction          : 0.02
% 2.46/1.68  MUC search           : 0.00
% 2.46/1.68  Cooper               : 0.00
% 2.46/1.68  Total                : 0.79
% 2.46/1.68  Index Insertion      : 0.00
% 2.46/1.68  Index Deletion       : 0.00
% 2.46/1.68  Index Matching       : 0.00
% 2.46/1.68  BG Taut test         : 0.00
%------------------------------------------------------------------------------

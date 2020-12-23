%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:17 EST 2020

% Result     : Theorem 1.79s
% Output     : CNFRefutation 1.97s
% Verified   : 
% Statistics : Number of formulae       :   51 (  78 expanded)
%              Number of leaves         :   26 (  38 expanded)
%              Depth                    :    8
%              Number of atoms          :   59 (  89 expanded)
%              Number of equality atoms :   23 (  46 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > v1_relat_1 > k8_relset_1 > k5_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_1

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

tff(f_61,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => k8_relset_1(A,A,k6_partfun1(A),B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t171_funct_2)).

tff(f_29,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_56,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_31,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_42,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k5_relat_1(k6_relat_1(A),B) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_relat_1)).

tff(f_38,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k1_relat_1(k5_relat_1(A,B)) = k10_relat_1(A,k1_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t182_relat_1)).

tff(f_54,axiom,(
    ! [A] : m1_subset_1(k6_relat_1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_relset_1)).

tff(f_52,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(c_24,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_58,plain,(
    ! [A_20,B_21] :
      ( r1_tarski(A_20,B_21)
      | ~ m1_subset_1(A_20,k1_zfmisc_1(B_21)) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_62,plain,(
    r1_tarski('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_24,c_58])).

tff(c_20,plain,(
    ! [A_15] : k6_relat_1(A_15) = k6_partfun1(A_15) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_6,plain,(
    ! [A_3] : v1_relat_1(k6_relat_1(A_3)) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_29,plain,(
    ! [A_3] : v1_relat_1(k6_partfun1(A_3)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_6])).

tff(c_10,plain,(
    ! [A_7] : k1_relat_1(k6_relat_1(A_7)) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_28,plain,(
    ! [A_7] : k1_relat_1(k6_partfun1(A_7)) = A_7 ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_10])).

tff(c_14,plain,(
    ! [A_8,B_9] :
      ( k5_relat_1(k6_relat_1(A_8),B_9) = B_9
      | ~ r1_tarski(k1_relat_1(B_9),A_8)
      | ~ v1_relat_1(B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_74,plain,(
    ! [A_26,B_27] :
      ( k5_relat_1(k6_partfun1(A_26),B_27) = B_27
      | ~ r1_tarski(k1_relat_1(B_27),A_26)
      | ~ v1_relat_1(B_27) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_14])).

tff(c_77,plain,(
    ! [A_26,A_7] :
      ( k5_relat_1(k6_partfun1(A_26),k6_partfun1(A_7)) = k6_partfun1(A_7)
      | ~ r1_tarski(A_7,A_26)
      | ~ v1_relat_1(k6_partfun1(A_7)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_74])).

tff(c_79,plain,(
    ! [A_26,A_7] :
      ( k5_relat_1(k6_partfun1(A_26),k6_partfun1(A_7)) = k6_partfun1(A_7)
      | ~ r1_tarski(A_7,A_26) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_29,c_77])).

tff(c_89,plain,(
    ! [A_30,B_31] :
      ( k10_relat_1(A_30,k1_relat_1(B_31)) = k1_relat_1(k5_relat_1(A_30,B_31))
      | ~ v1_relat_1(B_31)
      | ~ v1_relat_1(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_98,plain,(
    ! [A_30,A_7] :
      ( k1_relat_1(k5_relat_1(A_30,k6_partfun1(A_7))) = k10_relat_1(A_30,A_7)
      | ~ v1_relat_1(k6_partfun1(A_7))
      | ~ v1_relat_1(A_30) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_89])).

tff(c_103,plain,(
    ! [A_32,A_33] :
      ( k1_relat_1(k5_relat_1(A_32,k6_partfun1(A_33))) = k10_relat_1(A_32,A_33)
      | ~ v1_relat_1(A_32) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_29,c_98])).

tff(c_118,plain,(
    ! [A_26,A_7] :
      ( k10_relat_1(k6_partfun1(A_26),A_7) = k1_relat_1(k6_partfun1(A_7))
      | ~ v1_relat_1(k6_partfun1(A_26))
      | ~ r1_tarski(A_7,A_26) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_79,c_103])).

tff(c_122,plain,(
    ! [A_26,A_7] :
      ( k10_relat_1(k6_partfun1(A_26),A_7) = A_7
      | ~ r1_tarski(A_7,A_26) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_29,c_28,c_118])).

tff(c_18,plain,(
    ! [A_14] : m1_subset_1(k6_relat_1(A_14),k1_zfmisc_1(k2_zfmisc_1(A_14,A_14))) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_25,plain,(
    ! [A_14] : m1_subset_1(k6_partfun1(A_14),k1_zfmisc_1(k2_zfmisc_1(A_14,A_14))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_18])).

tff(c_123,plain,(
    ! [A_34,B_35,C_36,D_37] :
      ( k8_relset_1(A_34,B_35,C_36,D_37) = k10_relat_1(C_36,D_37)
      | ~ m1_subset_1(C_36,k1_zfmisc_1(k2_zfmisc_1(A_34,B_35))) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_130,plain,(
    ! [A_14,D_37] : k8_relset_1(A_14,A_14,k6_partfun1(A_14),D_37) = k10_relat_1(k6_partfun1(A_14),D_37) ),
    inference(resolution,[status(thm)],[c_25,c_123])).

tff(c_22,plain,(
    k8_relset_1('#skF_1','#skF_1',k6_partfun1('#skF_1'),'#skF_2') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_152,plain,(
    k10_relat_1(k6_partfun1('#skF_1'),'#skF_2') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_130,c_22])).

tff(c_164,plain,(
    ~ r1_tarski('#skF_2','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_122,c_152])).

tff(c_168,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_164])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 12:40:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.79/1.19  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.97/1.20  
% 1.97/1.20  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.97/1.20  %$ r1_tarski > m1_subset_1 > v1_relat_1 > k8_relset_1 > k5_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_1
% 1.97/1.20  
% 1.97/1.20  %Foreground sorts:
% 1.97/1.20  
% 1.97/1.20  
% 1.97/1.20  %Background operators:
% 1.97/1.20  
% 1.97/1.20  
% 1.97/1.20  %Foreground operators:
% 1.97/1.20  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.97/1.20  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 1.97/1.20  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 1.97/1.20  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.97/1.20  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.97/1.20  tff('#skF_2', type, '#skF_2': $i).
% 1.97/1.20  tff('#skF_1', type, '#skF_1': $i).
% 1.97/1.20  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.97/1.20  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 1.97/1.20  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.97/1.20  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 1.97/1.20  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.97/1.20  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.97/1.20  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 1.97/1.20  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.97/1.20  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.97/1.20  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.97/1.20  
% 1.97/1.21  tff(f_61, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k8_relset_1(A, A, k6_partfun1(A), B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t171_funct_2)).
% 1.97/1.21  tff(f_29, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 1.97/1.21  tff(f_56, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 1.97/1.21  tff(f_31, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 1.97/1.21  tff(f_42, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 1.97/1.21  tff(f_48, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k5_relat_1(k6_relat_1(A), B) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t77_relat_1)).
% 1.97/1.21  tff(f_38, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k1_relat_1(k5_relat_1(A, B)) = k10_relat_1(A, k1_relat_1(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t182_relat_1)).
% 1.97/1.21  tff(f_54, axiom, (![A]: m1_subset_1(k6_relat_1(A), k1_zfmisc_1(k2_zfmisc_1(A, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_relset_1)).
% 1.97/1.21  tff(f_52, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 1.97/1.21  tff(c_24, plain, (m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_61])).
% 1.97/1.21  tff(c_58, plain, (![A_20, B_21]: (r1_tarski(A_20, B_21) | ~m1_subset_1(A_20, k1_zfmisc_1(B_21)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.97/1.21  tff(c_62, plain, (r1_tarski('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_24, c_58])).
% 1.97/1.21  tff(c_20, plain, (![A_15]: (k6_relat_1(A_15)=k6_partfun1(A_15))), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.97/1.21  tff(c_6, plain, (![A_3]: (v1_relat_1(k6_relat_1(A_3)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.97/1.21  tff(c_29, plain, (![A_3]: (v1_relat_1(k6_partfun1(A_3)))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_6])).
% 1.97/1.21  tff(c_10, plain, (![A_7]: (k1_relat_1(k6_relat_1(A_7))=A_7)), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.97/1.21  tff(c_28, plain, (![A_7]: (k1_relat_1(k6_partfun1(A_7))=A_7)), inference(demodulation, [status(thm), theory('equality')], [c_20, c_10])).
% 1.97/1.21  tff(c_14, plain, (![A_8, B_9]: (k5_relat_1(k6_relat_1(A_8), B_9)=B_9 | ~r1_tarski(k1_relat_1(B_9), A_8) | ~v1_relat_1(B_9))), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.97/1.21  tff(c_74, plain, (![A_26, B_27]: (k5_relat_1(k6_partfun1(A_26), B_27)=B_27 | ~r1_tarski(k1_relat_1(B_27), A_26) | ~v1_relat_1(B_27))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_14])).
% 1.97/1.21  tff(c_77, plain, (![A_26, A_7]: (k5_relat_1(k6_partfun1(A_26), k6_partfun1(A_7))=k6_partfun1(A_7) | ~r1_tarski(A_7, A_26) | ~v1_relat_1(k6_partfun1(A_7)))), inference(superposition, [status(thm), theory('equality')], [c_28, c_74])).
% 1.97/1.21  tff(c_79, plain, (![A_26, A_7]: (k5_relat_1(k6_partfun1(A_26), k6_partfun1(A_7))=k6_partfun1(A_7) | ~r1_tarski(A_7, A_26))), inference(demodulation, [status(thm), theory('equality')], [c_29, c_77])).
% 1.97/1.21  tff(c_89, plain, (![A_30, B_31]: (k10_relat_1(A_30, k1_relat_1(B_31))=k1_relat_1(k5_relat_1(A_30, B_31)) | ~v1_relat_1(B_31) | ~v1_relat_1(A_30))), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.97/1.21  tff(c_98, plain, (![A_30, A_7]: (k1_relat_1(k5_relat_1(A_30, k6_partfun1(A_7)))=k10_relat_1(A_30, A_7) | ~v1_relat_1(k6_partfun1(A_7)) | ~v1_relat_1(A_30))), inference(superposition, [status(thm), theory('equality')], [c_28, c_89])).
% 1.97/1.21  tff(c_103, plain, (![A_32, A_33]: (k1_relat_1(k5_relat_1(A_32, k6_partfun1(A_33)))=k10_relat_1(A_32, A_33) | ~v1_relat_1(A_32))), inference(demodulation, [status(thm), theory('equality')], [c_29, c_98])).
% 1.97/1.21  tff(c_118, plain, (![A_26, A_7]: (k10_relat_1(k6_partfun1(A_26), A_7)=k1_relat_1(k6_partfun1(A_7)) | ~v1_relat_1(k6_partfun1(A_26)) | ~r1_tarski(A_7, A_26))), inference(superposition, [status(thm), theory('equality')], [c_79, c_103])).
% 1.97/1.21  tff(c_122, plain, (![A_26, A_7]: (k10_relat_1(k6_partfun1(A_26), A_7)=A_7 | ~r1_tarski(A_7, A_26))), inference(demodulation, [status(thm), theory('equality')], [c_29, c_28, c_118])).
% 1.97/1.21  tff(c_18, plain, (![A_14]: (m1_subset_1(k6_relat_1(A_14), k1_zfmisc_1(k2_zfmisc_1(A_14, A_14))))), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.97/1.21  tff(c_25, plain, (![A_14]: (m1_subset_1(k6_partfun1(A_14), k1_zfmisc_1(k2_zfmisc_1(A_14, A_14))))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_18])).
% 1.97/1.21  tff(c_123, plain, (![A_34, B_35, C_36, D_37]: (k8_relset_1(A_34, B_35, C_36, D_37)=k10_relat_1(C_36, D_37) | ~m1_subset_1(C_36, k1_zfmisc_1(k2_zfmisc_1(A_34, B_35))))), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.97/1.21  tff(c_130, plain, (![A_14, D_37]: (k8_relset_1(A_14, A_14, k6_partfun1(A_14), D_37)=k10_relat_1(k6_partfun1(A_14), D_37))), inference(resolution, [status(thm)], [c_25, c_123])).
% 1.97/1.21  tff(c_22, plain, (k8_relset_1('#skF_1', '#skF_1', k6_partfun1('#skF_1'), '#skF_2')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_61])).
% 1.97/1.21  tff(c_152, plain, (k10_relat_1(k6_partfun1('#skF_1'), '#skF_2')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_130, c_22])).
% 1.97/1.21  tff(c_164, plain, (~r1_tarski('#skF_2', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_122, c_152])).
% 1.97/1.21  tff(c_168, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_62, c_164])).
% 1.97/1.21  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.97/1.21  
% 1.97/1.21  Inference rules
% 1.97/1.21  ----------------------
% 1.97/1.21  #Ref     : 0
% 1.97/1.21  #Sup     : 29
% 1.97/1.21  #Fact    : 0
% 1.97/1.21  #Define  : 0
% 1.97/1.21  #Split   : 0
% 1.97/1.21  #Chain   : 0
% 1.97/1.21  #Close   : 0
% 1.97/1.21  
% 1.97/1.21  Ordering : KBO
% 1.97/1.21  
% 1.97/1.21  Simplification rules
% 1.97/1.21  ----------------------
% 1.97/1.21  #Subsume      : 0
% 1.97/1.21  #Demod        : 13
% 1.97/1.21  #Tautology    : 17
% 1.97/1.21  #SimpNegUnit  : 0
% 1.97/1.21  #BackRed      : 1
% 1.97/1.21  
% 1.97/1.21  #Partial instantiations: 0
% 1.97/1.21  #Strategies tried      : 1
% 1.97/1.21  
% 1.97/1.21  Timing (in seconds)
% 1.97/1.21  ----------------------
% 1.97/1.22  Preprocessing        : 0.28
% 1.97/1.22  Parsing              : 0.15
% 1.97/1.22  CNF conversion       : 0.02
% 1.97/1.22  Main loop            : 0.13
% 1.97/1.22  Inferencing          : 0.06
% 1.97/1.22  Reduction            : 0.04
% 1.97/1.22  Demodulation         : 0.03
% 1.97/1.22  BG Simplification    : 0.01
% 1.97/1.22  Subsumption          : 0.02
% 1.97/1.22  Abstraction          : 0.01
% 1.97/1.22  MUC search           : 0.00
% 1.97/1.22  Cooper               : 0.00
% 1.97/1.22  Total                : 0.44
% 1.97/1.22  Index Insertion      : 0.00
% 1.97/1.22  Index Deletion       : 0.00
% 1.97/1.22  Index Matching       : 0.00
% 1.97/1.22  BG Taut test         : 0.00
%------------------------------------------------------------------------------

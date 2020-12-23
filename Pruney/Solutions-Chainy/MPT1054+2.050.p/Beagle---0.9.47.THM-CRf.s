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
% DateTime   : Thu Dec  3 10:17:18 EST 2020

% Result     : Theorem 1.93s
% Output     : CNFRefutation 1.93s
% Verified   : 
% Statistics : Number of formulae       :   52 (  79 expanded)
%              Number of leaves         :   27 (  39 expanded)
%              Depth                    :    8
%              Number of atoms          :   60 (  92 expanded)
%              Number of equality atoms :   23 (  46 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k5_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

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

tff(f_63,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => k8_relset_1(A,A,k6_partfun1(A),B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t171_funct_2)).

tff(f_29,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_58,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_50,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_40,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k5_relat_1(k6_relat_1(A),B) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_relat_1)).

tff(f_36,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k1_relat_1(k5_relat_1(A,B)) = k10_relat_1(A,k1_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t182_relat_1)).

tff(f_56,axiom,(
    ! [A] : m1_subset_1(k6_relat_1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_relset_1)).

tff(f_54,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(c_26,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_62,plain,(
    ! [A_21,B_22] :
      ( r1_tarski(A_21,B_22)
      | ~ m1_subset_1(A_21,k1_zfmisc_1(B_22)) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_66,plain,(
    r1_tarski('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_26,c_62])).

tff(c_22,plain,(
    ! [A_15] : k6_relat_1(A_15) = k6_partfun1(A_15) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_14,plain,(
    ! [A_9] : v1_relat_1(k6_relat_1(A_9)) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_29,plain,(
    ! [A_9] : v1_relat_1(k6_partfun1(A_9)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_14])).

tff(c_8,plain,(
    ! [A_6] : k1_relat_1(k6_relat_1(A_6)) = A_6 ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_32,plain,(
    ! [A_6] : k1_relat_1(k6_partfun1(A_6)) = A_6 ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_8])).

tff(c_12,plain,(
    ! [A_7,B_8] :
      ( k5_relat_1(k6_relat_1(A_7),B_8) = B_8
      | ~ r1_tarski(k1_relat_1(B_8),A_7)
      | ~ v1_relat_1(B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_78,plain,(
    ! [A_27,B_28] :
      ( k5_relat_1(k6_partfun1(A_27),B_28) = B_28
      | ~ r1_tarski(k1_relat_1(B_28),A_27)
      | ~ v1_relat_1(B_28) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_12])).

tff(c_81,plain,(
    ! [A_27,A_6] :
      ( k5_relat_1(k6_partfun1(A_27),k6_partfun1(A_6)) = k6_partfun1(A_6)
      | ~ r1_tarski(A_6,A_27)
      | ~ v1_relat_1(k6_partfun1(A_6)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_78])).

tff(c_83,plain,(
    ! [A_27,A_6] :
      ( k5_relat_1(k6_partfun1(A_27),k6_partfun1(A_6)) = k6_partfun1(A_6)
      | ~ r1_tarski(A_6,A_27) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_29,c_81])).

tff(c_93,plain,(
    ! [A_31,B_32] :
      ( k10_relat_1(A_31,k1_relat_1(B_32)) = k1_relat_1(k5_relat_1(A_31,B_32))
      | ~ v1_relat_1(B_32)
      | ~ v1_relat_1(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_102,plain,(
    ! [A_31,A_6] :
      ( k1_relat_1(k5_relat_1(A_31,k6_partfun1(A_6))) = k10_relat_1(A_31,A_6)
      | ~ v1_relat_1(k6_partfun1(A_6))
      | ~ v1_relat_1(A_31) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_93])).

tff(c_115,plain,(
    ! [A_37,A_38] :
      ( k1_relat_1(k5_relat_1(A_37,k6_partfun1(A_38))) = k10_relat_1(A_37,A_38)
      | ~ v1_relat_1(A_37) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_29,c_102])).

tff(c_130,plain,(
    ! [A_27,A_6] :
      ( k10_relat_1(k6_partfun1(A_27),A_6) = k1_relat_1(k6_partfun1(A_6))
      | ~ v1_relat_1(k6_partfun1(A_27))
      | ~ r1_tarski(A_6,A_27) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_83,c_115])).

tff(c_134,plain,(
    ! [A_27,A_6] :
      ( k10_relat_1(k6_partfun1(A_27),A_6) = A_6
      | ~ r1_tarski(A_6,A_27) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_29,c_32,c_130])).

tff(c_20,plain,(
    ! [A_14] : m1_subset_1(k6_relat_1(A_14),k1_zfmisc_1(k2_zfmisc_1(A_14,A_14))) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_27,plain,(
    ! [A_14] : m1_subset_1(k6_partfun1(A_14),k1_zfmisc_1(k2_zfmisc_1(A_14,A_14))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_20])).

tff(c_107,plain,(
    ! [A_33,B_34,C_35,D_36] :
      ( k8_relset_1(A_33,B_34,C_35,D_36) = k10_relat_1(C_35,D_36)
      | ~ m1_subset_1(C_35,k1_zfmisc_1(k2_zfmisc_1(A_33,B_34))) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_114,plain,(
    ! [A_14,D_36] : k8_relset_1(A_14,A_14,k6_partfun1(A_14),D_36) = k10_relat_1(k6_partfun1(A_14),D_36) ),
    inference(resolution,[status(thm)],[c_27,c_107])).

tff(c_24,plain,(
    k8_relset_1('#skF_1','#skF_1',k6_partfun1('#skF_1'),'#skF_2') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_156,plain,(
    k10_relat_1(k6_partfun1('#skF_1'),'#skF_2') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_114,c_24])).

tff(c_168,plain,(
    ~ r1_tarski('#skF_2','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_134,c_156])).

tff(c_172,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_168])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:59:16 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.93/1.24  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.93/1.24  
% 1.93/1.24  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.93/1.25  %$ r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k5_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_1
% 1.93/1.25  
% 1.93/1.25  %Foreground sorts:
% 1.93/1.25  
% 1.93/1.25  
% 1.93/1.25  %Background operators:
% 1.93/1.25  
% 1.93/1.25  
% 1.93/1.25  %Foreground operators:
% 1.93/1.25  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.93/1.25  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.93/1.25  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 1.93/1.25  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 1.93/1.25  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.93/1.25  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.93/1.25  tff('#skF_2', type, '#skF_2': $i).
% 1.93/1.25  tff('#skF_1', type, '#skF_1': $i).
% 1.93/1.25  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.93/1.25  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 1.93/1.25  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.93/1.25  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 1.93/1.25  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.93/1.25  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.93/1.25  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 1.93/1.25  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.93/1.25  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.93/1.25  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.93/1.25  
% 1.93/1.26  tff(f_63, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k8_relset_1(A, A, k6_partfun1(A), B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t171_funct_2)).
% 1.93/1.26  tff(f_29, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 1.93/1.26  tff(f_58, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 1.93/1.26  tff(f_50, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc3_funct_1)).
% 1.93/1.26  tff(f_40, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 1.93/1.26  tff(f_46, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k5_relat_1(k6_relat_1(A), B) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t77_relat_1)).
% 1.93/1.26  tff(f_36, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k1_relat_1(k5_relat_1(A, B)) = k10_relat_1(A, k1_relat_1(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t182_relat_1)).
% 1.93/1.26  tff(f_56, axiom, (![A]: m1_subset_1(k6_relat_1(A), k1_zfmisc_1(k2_zfmisc_1(A, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_relset_1)).
% 1.93/1.26  tff(f_54, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 1.93/1.26  tff(c_26, plain, (m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_63])).
% 1.93/1.26  tff(c_62, plain, (![A_21, B_22]: (r1_tarski(A_21, B_22) | ~m1_subset_1(A_21, k1_zfmisc_1(B_22)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.93/1.26  tff(c_66, plain, (r1_tarski('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_26, c_62])).
% 1.93/1.26  tff(c_22, plain, (![A_15]: (k6_relat_1(A_15)=k6_partfun1(A_15))), inference(cnfTransformation, [status(thm)], [f_58])).
% 1.93/1.26  tff(c_14, plain, (![A_9]: (v1_relat_1(k6_relat_1(A_9)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.93/1.26  tff(c_29, plain, (![A_9]: (v1_relat_1(k6_partfun1(A_9)))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_14])).
% 1.93/1.26  tff(c_8, plain, (![A_6]: (k1_relat_1(k6_relat_1(A_6))=A_6)), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.93/1.26  tff(c_32, plain, (![A_6]: (k1_relat_1(k6_partfun1(A_6))=A_6)), inference(demodulation, [status(thm), theory('equality')], [c_22, c_8])).
% 1.93/1.26  tff(c_12, plain, (![A_7, B_8]: (k5_relat_1(k6_relat_1(A_7), B_8)=B_8 | ~r1_tarski(k1_relat_1(B_8), A_7) | ~v1_relat_1(B_8))), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.93/1.26  tff(c_78, plain, (![A_27, B_28]: (k5_relat_1(k6_partfun1(A_27), B_28)=B_28 | ~r1_tarski(k1_relat_1(B_28), A_27) | ~v1_relat_1(B_28))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_12])).
% 1.93/1.26  tff(c_81, plain, (![A_27, A_6]: (k5_relat_1(k6_partfun1(A_27), k6_partfun1(A_6))=k6_partfun1(A_6) | ~r1_tarski(A_6, A_27) | ~v1_relat_1(k6_partfun1(A_6)))), inference(superposition, [status(thm), theory('equality')], [c_32, c_78])).
% 1.93/1.26  tff(c_83, plain, (![A_27, A_6]: (k5_relat_1(k6_partfun1(A_27), k6_partfun1(A_6))=k6_partfun1(A_6) | ~r1_tarski(A_6, A_27))), inference(demodulation, [status(thm), theory('equality')], [c_29, c_81])).
% 1.93/1.26  tff(c_93, plain, (![A_31, B_32]: (k10_relat_1(A_31, k1_relat_1(B_32))=k1_relat_1(k5_relat_1(A_31, B_32)) | ~v1_relat_1(B_32) | ~v1_relat_1(A_31))), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.93/1.26  tff(c_102, plain, (![A_31, A_6]: (k1_relat_1(k5_relat_1(A_31, k6_partfun1(A_6)))=k10_relat_1(A_31, A_6) | ~v1_relat_1(k6_partfun1(A_6)) | ~v1_relat_1(A_31))), inference(superposition, [status(thm), theory('equality')], [c_32, c_93])).
% 1.93/1.26  tff(c_115, plain, (![A_37, A_38]: (k1_relat_1(k5_relat_1(A_37, k6_partfun1(A_38)))=k10_relat_1(A_37, A_38) | ~v1_relat_1(A_37))), inference(demodulation, [status(thm), theory('equality')], [c_29, c_102])).
% 1.93/1.26  tff(c_130, plain, (![A_27, A_6]: (k10_relat_1(k6_partfun1(A_27), A_6)=k1_relat_1(k6_partfun1(A_6)) | ~v1_relat_1(k6_partfun1(A_27)) | ~r1_tarski(A_6, A_27))), inference(superposition, [status(thm), theory('equality')], [c_83, c_115])).
% 1.93/1.26  tff(c_134, plain, (![A_27, A_6]: (k10_relat_1(k6_partfun1(A_27), A_6)=A_6 | ~r1_tarski(A_6, A_27))), inference(demodulation, [status(thm), theory('equality')], [c_29, c_32, c_130])).
% 1.93/1.26  tff(c_20, plain, (![A_14]: (m1_subset_1(k6_relat_1(A_14), k1_zfmisc_1(k2_zfmisc_1(A_14, A_14))))), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.93/1.26  tff(c_27, plain, (![A_14]: (m1_subset_1(k6_partfun1(A_14), k1_zfmisc_1(k2_zfmisc_1(A_14, A_14))))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_20])).
% 1.93/1.26  tff(c_107, plain, (![A_33, B_34, C_35, D_36]: (k8_relset_1(A_33, B_34, C_35, D_36)=k10_relat_1(C_35, D_36) | ~m1_subset_1(C_35, k1_zfmisc_1(k2_zfmisc_1(A_33, B_34))))), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.93/1.26  tff(c_114, plain, (![A_14, D_36]: (k8_relset_1(A_14, A_14, k6_partfun1(A_14), D_36)=k10_relat_1(k6_partfun1(A_14), D_36))), inference(resolution, [status(thm)], [c_27, c_107])).
% 1.93/1.26  tff(c_24, plain, (k8_relset_1('#skF_1', '#skF_1', k6_partfun1('#skF_1'), '#skF_2')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_63])).
% 1.93/1.26  tff(c_156, plain, (k10_relat_1(k6_partfun1('#skF_1'), '#skF_2')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_114, c_24])).
% 1.93/1.26  tff(c_168, plain, (~r1_tarski('#skF_2', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_134, c_156])).
% 1.93/1.26  tff(c_172, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_66, c_168])).
% 1.93/1.26  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.93/1.26  
% 1.93/1.26  Inference rules
% 1.93/1.26  ----------------------
% 1.93/1.26  #Ref     : 0
% 1.93/1.26  #Sup     : 29
% 1.93/1.26  #Fact    : 0
% 1.93/1.26  #Define  : 0
% 1.93/1.26  #Split   : 0
% 1.93/1.26  #Chain   : 0
% 1.93/1.26  #Close   : 0
% 1.93/1.26  
% 1.93/1.26  Ordering : KBO
% 1.93/1.26  
% 1.93/1.26  Simplification rules
% 1.93/1.26  ----------------------
% 1.93/1.26  #Subsume      : 0
% 1.93/1.26  #Demod        : 14
% 1.93/1.26  #Tautology    : 17
% 1.93/1.26  #SimpNegUnit  : 0
% 1.93/1.26  #BackRed      : 1
% 1.93/1.26  
% 1.93/1.26  #Partial instantiations: 0
% 1.93/1.26  #Strategies tried      : 1
% 1.93/1.26  
% 1.93/1.26  Timing (in seconds)
% 1.93/1.26  ----------------------
% 1.93/1.26  Preprocessing        : 0.28
% 1.93/1.26  Parsing              : 0.15
% 1.93/1.26  CNF conversion       : 0.02
% 1.93/1.26  Main loop            : 0.15
% 1.93/1.26  Inferencing          : 0.07
% 1.93/1.26  Reduction            : 0.04
% 1.93/1.26  Demodulation         : 0.03
% 1.93/1.26  BG Simplification    : 0.01
% 1.93/1.26  Subsumption          : 0.02
% 1.93/1.26  Abstraction          : 0.01
% 1.93/1.26  MUC search           : 0.00
% 1.93/1.26  Cooper               : 0.00
% 1.93/1.26  Total                : 0.45
% 1.93/1.26  Index Insertion      : 0.00
% 1.93/1.26  Index Deletion       : 0.00
% 1.93/1.26  Index Matching       : 0.00
% 1.93/1.26  BG Taut test         : 0.00
%------------------------------------------------------------------------------

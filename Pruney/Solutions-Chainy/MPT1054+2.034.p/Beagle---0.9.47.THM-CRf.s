%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:16 EST 2020

% Result     : Theorem 1.85s
% Output     : CNFRefutation 1.85s
% Verified   : 
% Statistics : Number of formulae       :   54 (  73 expanded)
%              Number of leaves         :   30 (  39 expanded)
%              Depth                    :    9
%              Number of atoms          :   52 (  74 expanded)
%              Number of equality atoms :   25 (  42 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_partfun1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k5_relat_1 > k3_xboole_0 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_1

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_65,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => k8_relset_1(A,A,k6_partfun1(A),B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t171_funct_2)).

tff(f_33,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_60,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_48,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_44,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_50,axiom,(
    ! [A,B] : k5_relat_1(k6_relat_1(B),k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_funct_1)).

tff(f_40,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k1_relat_1(k5_relat_1(A,B)) = k10_relat_1(A,k1_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t182_relat_1)).

tff(f_58,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_54,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(c_30,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_68,plain,(
    ! [A_27,B_28] :
      ( r1_tarski(A_27,B_28)
      | ~ m1_subset_1(A_27,k1_zfmisc_1(B_28)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_80,plain,(
    r1_tarski('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_68])).

tff(c_82,plain,(
    ! [A_30,B_31] :
      ( k3_xboole_0(A_30,B_31) = A_30
      | ~ r1_tarski(A_30,B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_90,plain,(
    k3_xboole_0('#skF_2','#skF_1') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_80,c_82])).

tff(c_26,plain,(
    ! [A_17] : k6_relat_1(A_17) = k6_partfun1(A_17) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_14,plain,(
    ! [A_9] : v1_relat_1(k6_relat_1(A_9)) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_33,plain,(
    ! [A_9] : v1_relat_1(k6_partfun1(A_9)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_14])).

tff(c_10,plain,(
    ! [A_8] : k1_relat_1(k6_relat_1(A_8)) = A_8 ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_35,plain,(
    ! [A_8] : k1_relat_1(k6_partfun1(A_8)) = A_8 ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_10])).

tff(c_18,plain,(
    ! [B_11,A_10] : k5_relat_1(k6_relat_1(B_11),k6_relat_1(A_10)) = k6_relat_1(k3_xboole_0(A_10,B_11)) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_31,plain,(
    ! [B_11,A_10] : k5_relat_1(k6_partfun1(B_11),k6_partfun1(A_10)) = k6_partfun1(k3_xboole_0(A_10,B_11)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_26,c_26,c_18])).

tff(c_113,plain,(
    ! [A_35,B_36] :
      ( k10_relat_1(A_35,k1_relat_1(B_36)) = k1_relat_1(k5_relat_1(A_35,B_36))
      | ~ v1_relat_1(B_36)
      | ~ v1_relat_1(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_122,plain,(
    ! [A_35,A_8] :
      ( k1_relat_1(k5_relat_1(A_35,k6_partfun1(A_8))) = k10_relat_1(A_35,A_8)
      | ~ v1_relat_1(k6_partfun1(A_8))
      | ~ v1_relat_1(A_35) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_35,c_113])).

tff(c_127,plain,(
    ! [A_37,A_38] :
      ( k1_relat_1(k5_relat_1(A_37,k6_partfun1(A_38))) = k10_relat_1(A_37,A_38)
      | ~ v1_relat_1(A_37) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_33,c_122])).

tff(c_139,plain,(
    ! [A_10,B_11] :
      ( k1_relat_1(k6_partfun1(k3_xboole_0(A_10,B_11))) = k10_relat_1(k6_partfun1(B_11),A_10)
      | ~ v1_relat_1(k6_partfun1(B_11)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_31,c_127])).

tff(c_143,plain,(
    ! [B_11,A_10] : k10_relat_1(k6_partfun1(B_11),A_10) = k3_xboole_0(A_10,B_11) ),
    inference(demodulation,[status(thm),theory(equality)],[c_33,c_35,c_139])).

tff(c_24,plain,(
    ! [A_16] : m1_subset_1(k6_partfun1(A_16),k1_zfmisc_1(k2_zfmisc_1(A_16,A_16))) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_144,plain,(
    ! [A_39,B_40,C_41,D_42] :
      ( k8_relset_1(A_39,B_40,C_41,D_42) = k10_relat_1(C_41,D_42)
      | ~ m1_subset_1(C_41,k1_zfmisc_1(k2_zfmisc_1(A_39,B_40))) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_151,plain,(
    ! [A_16,D_42] : k8_relset_1(A_16,A_16,k6_partfun1(A_16),D_42) = k10_relat_1(k6_partfun1(A_16),D_42) ),
    inference(resolution,[status(thm)],[c_24,c_144])).

tff(c_173,plain,(
    ! [A_16,D_42] : k8_relset_1(A_16,A_16,k6_partfun1(A_16),D_42) = k3_xboole_0(D_42,A_16) ),
    inference(demodulation,[status(thm),theory(equality)],[c_143,c_151])).

tff(c_28,plain,(
    k8_relset_1('#skF_1','#skF_1',k6_partfun1('#skF_1'),'#skF_2') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_174,plain,(
    k3_xboole_0('#skF_2','#skF_1') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_173,c_28])).

tff(c_177,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_174])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:02:04 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.85/1.16  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.85/1.17  
% 1.85/1.17  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.85/1.17  %$ v1_partfun1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k5_relat_1 > k3_xboole_0 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_1
% 1.85/1.17  
% 1.85/1.17  %Foreground sorts:
% 1.85/1.17  
% 1.85/1.17  
% 1.85/1.17  %Background operators:
% 1.85/1.17  
% 1.85/1.17  
% 1.85/1.17  %Foreground operators:
% 1.85/1.17  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.85/1.17  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.85/1.17  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 1.85/1.17  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 1.85/1.17  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.85/1.17  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.85/1.17  tff('#skF_2', type, '#skF_2': $i).
% 1.85/1.17  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 1.85/1.17  tff('#skF_1', type, '#skF_1': $i).
% 1.85/1.17  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.85/1.17  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 1.85/1.17  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.85/1.17  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 1.85/1.17  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.85/1.17  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.85/1.17  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 1.85/1.17  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.85/1.17  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.85/1.17  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.85/1.17  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.85/1.17  
% 1.85/1.18  tff(f_65, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k8_relset_1(A, A, k6_partfun1(A), B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t171_funct_2)).
% 1.85/1.18  tff(f_33, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 1.85/1.18  tff(f_29, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 1.85/1.18  tff(f_60, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 1.85/1.18  tff(f_48, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc3_funct_1)).
% 1.85/1.18  tff(f_44, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 1.85/1.18  tff(f_50, axiom, (![A, B]: (k5_relat_1(k6_relat_1(B), k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_funct_1)).
% 1.85/1.18  tff(f_40, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k1_relat_1(k5_relat_1(A, B)) = k10_relat_1(A, k1_relat_1(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t182_relat_1)).
% 1.85/1.18  tff(f_58, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 1.85/1.18  tff(f_54, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 1.85/1.18  tff(c_30, plain, (m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_65])).
% 1.85/1.18  tff(c_68, plain, (![A_27, B_28]: (r1_tarski(A_27, B_28) | ~m1_subset_1(A_27, k1_zfmisc_1(B_28)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.85/1.18  tff(c_80, plain, (r1_tarski('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_30, c_68])).
% 1.85/1.18  tff(c_82, plain, (![A_30, B_31]: (k3_xboole_0(A_30, B_31)=A_30 | ~r1_tarski(A_30, B_31))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.85/1.18  tff(c_90, plain, (k3_xboole_0('#skF_2', '#skF_1')='#skF_2'), inference(resolution, [status(thm)], [c_80, c_82])).
% 1.85/1.18  tff(c_26, plain, (![A_17]: (k6_relat_1(A_17)=k6_partfun1(A_17))), inference(cnfTransformation, [status(thm)], [f_60])).
% 1.85/1.18  tff(c_14, plain, (![A_9]: (v1_relat_1(k6_relat_1(A_9)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.85/1.18  tff(c_33, plain, (![A_9]: (v1_relat_1(k6_partfun1(A_9)))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_14])).
% 1.85/1.18  tff(c_10, plain, (![A_8]: (k1_relat_1(k6_relat_1(A_8))=A_8)), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.85/1.18  tff(c_35, plain, (![A_8]: (k1_relat_1(k6_partfun1(A_8))=A_8)), inference(demodulation, [status(thm), theory('equality')], [c_26, c_10])).
% 1.85/1.18  tff(c_18, plain, (![B_11, A_10]: (k5_relat_1(k6_relat_1(B_11), k6_relat_1(A_10))=k6_relat_1(k3_xboole_0(A_10, B_11)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.85/1.18  tff(c_31, plain, (![B_11, A_10]: (k5_relat_1(k6_partfun1(B_11), k6_partfun1(A_10))=k6_partfun1(k3_xboole_0(A_10, B_11)))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_26, c_26, c_18])).
% 1.85/1.18  tff(c_113, plain, (![A_35, B_36]: (k10_relat_1(A_35, k1_relat_1(B_36))=k1_relat_1(k5_relat_1(A_35, B_36)) | ~v1_relat_1(B_36) | ~v1_relat_1(A_35))), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.85/1.18  tff(c_122, plain, (![A_35, A_8]: (k1_relat_1(k5_relat_1(A_35, k6_partfun1(A_8)))=k10_relat_1(A_35, A_8) | ~v1_relat_1(k6_partfun1(A_8)) | ~v1_relat_1(A_35))), inference(superposition, [status(thm), theory('equality')], [c_35, c_113])).
% 1.85/1.18  tff(c_127, plain, (![A_37, A_38]: (k1_relat_1(k5_relat_1(A_37, k6_partfun1(A_38)))=k10_relat_1(A_37, A_38) | ~v1_relat_1(A_37))), inference(demodulation, [status(thm), theory('equality')], [c_33, c_122])).
% 1.85/1.18  tff(c_139, plain, (![A_10, B_11]: (k1_relat_1(k6_partfun1(k3_xboole_0(A_10, B_11)))=k10_relat_1(k6_partfun1(B_11), A_10) | ~v1_relat_1(k6_partfun1(B_11)))), inference(superposition, [status(thm), theory('equality')], [c_31, c_127])).
% 1.85/1.18  tff(c_143, plain, (![B_11, A_10]: (k10_relat_1(k6_partfun1(B_11), A_10)=k3_xboole_0(A_10, B_11))), inference(demodulation, [status(thm), theory('equality')], [c_33, c_35, c_139])).
% 1.85/1.18  tff(c_24, plain, (![A_16]: (m1_subset_1(k6_partfun1(A_16), k1_zfmisc_1(k2_zfmisc_1(A_16, A_16))))), inference(cnfTransformation, [status(thm)], [f_58])).
% 1.85/1.18  tff(c_144, plain, (![A_39, B_40, C_41, D_42]: (k8_relset_1(A_39, B_40, C_41, D_42)=k10_relat_1(C_41, D_42) | ~m1_subset_1(C_41, k1_zfmisc_1(k2_zfmisc_1(A_39, B_40))))), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.85/1.18  tff(c_151, plain, (![A_16, D_42]: (k8_relset_1(A_16, A_16, k6_partfun1(A_16), D_42)=k10_relat_1(k6_partfun1(A_16), D_42))), inference(resolution, [status(thm)], [c_24, c_144])).
% 1.85/1.18  tff(c_173, plain, (![A_16, D_42]: (k8_relset_1(A_16, A_16, k6_partfun1(A_16), D_42)=k3_xboole_0(D_42, A_16))), inference(demodulation, [status(thm), theory('equality')], [c_143, c_151])).
% 1.85/1.18  tff(c_28, plain, (k8_relset_1('#skF_1', '#skF_1', k6_partfun1('#skF_1'), '#skF_2')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_65])).
% 1.85/1.18  tff(c_174, plain, (k3_xboole_0('#skF_2', '#skF_1')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_173, c_28])).
% 1.85/1.18  tff(c_177, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_90, c_174])).
% 1.85/1.18  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.85/1.18  
% 1.85/1.18  Inference rules
% 1.85/1.18  ----------------------
% 1.85/1.18  #Ref     : 0
% 1.85/1.18  #Sup     : 30
% 1.85/1.18  #Fact    : 0
% 1.85/1.18  #Define  : 0
% 1.85/1.18  #Split   : 0
% 1.85/1.18  #Chain   : 0
% 1.85/1.18  #Close   : 0
% 1.85/1.18  
% 1.85/1.18  Ordering : KBO
% 1.85/1.18  
% 1.85/1.18  Simplification rules
% 1.85/1.18  ----------------------
% 1.85/1.18  #Subsume      : 0
% 1.85/1.18  #Demod        : 15
% 1.85/1.18  #Tautology    : 19
% 1.85/1.18  #SimpNegUnit  : 0
% 1.85/1.18  #BackRed      : 1
% 1.85/1.18  
% 1.85/1.18  #Partial instantiations: 0
% 1.85/1.18  #Strategies tried      : 1
% 1.85/1.18  
% 1.85/1.18  Timing (in seconds)
% 1.85/1.18  ----------------------
% 1.95/1.18  Preprocessing        : 0.29
% 1.95/1.18  Parsing              : 0.16
% 1.95/1.18  CNF conversion       : 0.02
% 1.95/1.18  Main loop            : 0.13
% 1.95/1.18  Inferencing          : 0.05
% 1.95/1.18  Reduction            : 0.04
% 1.95/1.18  Demodulation         : 0.03
% 1.95/1.18  BG Simplification    : 0.01
% 1.95/1.18  Subsumption          : 0.01
% 1.95/1.18  Abstraction          : 0.01
% 1.95/1.18  MUC search           : 0.00
% 1.95/1.18  Cooper               : 0.00
% 1.95/1.18  Total                : 0.45
% 1.95/1.18  Index Insertion      : 0.00
% 1.95/1.18  Index Deletion       : 0.00
% 1.95/1.18  Index Matching       : 0.00
% 1.95/1.18  BG Taut test         : 0.00
%------------------------------------------------------------------------------

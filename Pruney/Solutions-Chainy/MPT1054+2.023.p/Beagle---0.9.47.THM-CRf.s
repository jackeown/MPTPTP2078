%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:14 EST 2020

% Result     : Theorem 1.67s
% Output     : CNFRefutation 1.95s
% Verified   : 
% Statistics : Number of formulae       :   53 (  72 expanded)
%              Number of leaves         :   29 (  38 expanded)
%              Depth                    :    9
%              Number of atoms          :   51 (  72 expanded)
%              Number of equality atoms :   25 (  42 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_partfun1 > r1_tarski > m1_subset_1 > v1_relat_1 > k8_relset_1 > k5_relat_1 > k3_xboole_0 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_1

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_63,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => k8_relset_1(A,A,k6_partfun1(A),B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t171_funct_2)).

tff(f_33,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_58,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_35,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_46,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_48,axiom,(
    ! [A,B] : k5_relat_1(k6_relat_1(B),k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_funct_1)).

tff(f_42,axiom,(
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

tff(c_28,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_64,plain,(
    ! [A_26,B_27] :
      ( r1_tarski(A_26,B_27)
      | ~ m1_subset_1(A_26,k1_zfmisc_1(B_27)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_76,plain,(
    r1_tarski('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_28,c_64])).

tff(c_78,plain,(
    ! [A_29,B_30] :
      ( k3_xboole_0(A_29,B_30) = A_29
      | ~ r1_tarski(A_29,B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_86,plain,(
    k3_xboole_0('#skF_2','#skF_1') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_76,c_78])).

tff(c_24,plain,(
    ! [A_17] : k6_relat_1(A_17) = k6_partfun1(A_17) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_8,plain,(
    ! [A_5] : v1_relat_1(k6_relat_1(A_5)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_32,plain,(
    ! [A_5] : v1_relat_1(k6_partfun1(A_5)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_8])).

tff(c_12,plain,(
    ! [A_9] : k1_relat_1(k6_relat_1(A_9)) = A_9 ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_31,plain,(
    ! [A_9] : k1_relat_1(k6_partfun1(A_9)) = A_9 ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_12])).

tff(c_16,plain,(
    ! [B_11,A_10] : k5_relat_1(k6_relat_1(B_11),k6_relat_1(A_10)) = k6_relat_1(k3_xboole_0(A_10,B_11)) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_29,plain,(
    ! [B_11,A_10] : k5_relat_1(k6_partfun1(B_11),k6_partfun1(A_10)) = k6_partfun1(k3_xboole_0(A_10,B_11)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_24,c_24,c_16])).

tff(c_109,plain,(
    ! [A_34,B_35] :
      ( k10_relat_1(A_34,k1_relat_1(B_35)) = k1_relat_1(k5_relat_1(A_34,B_35))
      | ~ v1_relat_1(B_35)
      | ~ v1_relat_1(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_118,plain,(
    ! [A_34,A_9] :
      ( k1_relat_1(k5_relat_1(A_34,k6_partfun1(A_9))) = k10_relat_1(A_34,A_9)
      | ~ v1_relat_1(k6_partfun1(A_9))
      | ~ v1_relat_1(A_34) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_31,c_109])).

tff(c_123,plain,(
    ! [A_36,A_37] :
      ( k1_relat_1(k5_relat_1(A_36,k6_partfun1(A_37))) = k10_relat_1(A_36,A_37)
      | ~ v1_relat_1(A_36) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_118])).

tff(c_135,plain,(
    ! [A_10,B_11] :
      ( k1_relat_1(k6_partfun1(k3_xboole_0(A_10,B_11))) = k10_relat_1(k6_partfun1(B_11),A_10)
      | ~ v1_relat_1(k6_partfun1(B_11)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_29,c_123])).

tff(c_139,plain,(
    ! [B_11,A_10] : k10_relat_1(k6_partfun1(B_11),A_10) = k3_xboole_0(A_10,B_11) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_31,c_135])).

tff(c_22,plain,(
    ! [A_16] : m1_subset_1(k6_partfun1(A_16),k1_zfmisc_1(k2_zfmisc_1(A_16,A_16))) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_161,plain,(
    ! [A_40,B_41,C_42,D_43] :
      ( k8_relset_1(A_40,B_41,C_42,D_43) = k10_relat_1(C_42,D_43)
      | ~ m1_subset_1(C_42,k1_zfmisc_1(k2_zfmisc_1(A_40,B_41))) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_163,plain,(
    ! [A_16,D_43] : k8_relset_1(A_16,A_16,k6_partfun1(A_16),D_43) = k10_relat_1(k6_partfun1(A_16),D_43) ),
    inference(resolution,[status(thm)],[c_22,c_161])).

tff(c_168,plain,(
    ! [A_16,D_43] : k8_relset_1(A_16,A_16,k6_partfun1(A_16),D_43) = k3_xboole_0(D_43,A_16) ),
    inference(demodulation,[status(thm),theory(equality)],[c_139,c_163])).

tff(c_26,plain,(
    k8_relset_1('#skF_1','#skF_1',k6_partfun1('#skF_1'),'#skF_2') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_170,plain,(
    k3_xboole_0('#skF_2','#skF_1') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_168,c_26])).

tff(c_173,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_170])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n005.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 17:50:02 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.67/1.15  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.67/1.16  
% 1.67/1.16  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.67/1.16  %$ v1_partfun1 > r1_tarski > m1_subset_1 > v1_relat_1 > k8_relset_1 > k5_relat_1 > k3_xboole_0 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_1
% 1.67/1.16  
% 1.67/1.16  %Foreground sorts:
% 1.67/1.16  
% 1.67/1.16  
% 1.67/1.16  %Background operators:
% 1.67/1.16  
% 1.67/1.16  
% 1.67/1.16  %Foreground operators:
% 1.67/1.16  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.67/1.16  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 1.67/1.16  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 1.67/1.16  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.67/1.16  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.67/1.16  tff('#skF_2', type, '#skF_2': $i).
% 1.67/1.16  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 1.67/1.16  tff('#skF_1', type, '#skF_1': $i).
% 1.67/1.16  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.67/1.16  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 1.67/1.16  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.67/1.16  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 1.67/1.16  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.67/1.16  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.67/1.16  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 1.67/1.16  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.67/1.16  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.67/1.16  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.67/1.16  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.67/1.16  
% 1.95/1.17  tff(f_63, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k8_relset_1(A, A, k6_partfun1(A), B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t171_funct_2)).
% 1.95/1.17  tff(f_33, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 1.95/1.17  tff(f_29, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 1.95/1.17  tff(f_58, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 1.95/1.17  tff(f_35, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 1.95/1.17  tff(f_46, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 1.95/1.17  tff(f_48, axiom, (![A, B]: (k5_relat_1(k6_relat_1(B), k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_funct_1)).
% 1.95/1.17  tff(f_42, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k1_relat_1(k5_relat_1(A, B)) = k10_relat_1(A, k1_relat_1(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t182_relat_1)).
% 1.95/1.17  tff(f_56, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 1.95/1.17  tff(f_52, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 1.95/1.17  tff(c_28, plain, (m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_63])).
% 1.95/1.17  tff(c_64, plain, (![A_26, B_27]: (r1_tarski(A_26, B_27) | ~m1_subset_1(A_26, k1_zfmisc_1(B_27)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.95/1.17  tff(c_76, plain, (r1_tarski('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_28, c_64])).
% 1.95/1.17  tff(c_78, plain, (![A_29, B_30]: (k3_xboole_0(A_29, B_30)=A_29 | ~r1_tarski(A_29, B_30))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.95/1.17  tff(c_86, plain, (k3_xboole_0('#skF_2', '#skF_1')='#skF_2'), inference(resolution, [status(thm)], [c_76, c_78])).
% 1.95/1.17  tff(c_24, plain, (![A_17]: (k6_relat_1(A_17)=k6_partfun1(A_17))), inference(cnfTransformation, [status(thm)], [f_58])).
% 1.95/1.17  tff(c_8, plain, (![A_5]: (v1_relat_1(k6_relat_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.95/1.17  tff(c_32, plain, (![A_5]: (v1_relat_1(k6_partfun1(A_5)))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_8])).
% 1.95/1.17  tff(c_12, plain, (![A_9]: (k1_relat_1(k6_relat_1(A_9))=A_9)), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.95/1.17  tff(c_31, plain, (![A_9]: (k1_relat_1(k6_partfun1(A_9))=A_9)), inference(demodulation, [status(thm), theory('equality')], [c_24, c_12])).
% 1.95/1.17  tff(c_16, plain, (![B_11, A_10]: (k5_relat_1(k6_relat_1(B_11), k6_relat_1(A_10))=k6_relat_1(k3_xboole_0(A_10, B_11)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.95/1.17  tff(c_29, plain, (![B_11, A_10]: (k5_relat_1(k6_partfun1(B_11), k6_partfun1(A_10))=k6_partfun1(k3_xboole_0(A_10, B_11)))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_24, c_24, c_16])).
% 1.95/1.17  tff(c_109, plain, (![A_34, B_35]: (k10_relat_1(A_34, k1_relat_1(B_35))=k1_relat_1(k5_relat_1(A_34, B_35)) | ~v1_relat_1(B_35) | ~v1_relat_1(A_34))), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.95/1.17  tff(c_118, plain, (![A_34, A_9]: (k1_relat_1(k5_relat_1(A_34, k6_partfun1(A_9)))=k10_relat_1(A_34, A_9) | ~v1_relat_1(k6_partfun1(A_9)) | ~v1_relat_1(A_34))), inference(superposition, [status(thm), theory('equality')], [c_31, c_109])).
% 1.95/1.17  tff(c_123, plain, (![A_36, A_37]: (k1_relat_1(k5_relat_1(A_36, k6_partfun1(A_37)))=k10_relat_1(A_36, A_37) | ~v1_relat_1(A_36))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_118])).
% 1.95/1.17  tff(c_135, plain, (![A_10, B_11]: (k1_relat_1(k6_partfun1(k3_xboole_0(A_10, B_11)))=k10_relat_1(k6_partfun1(B_11), A_10) | ~v1_relat_1(k6_partfun1(B_11)))), inference(superposition, [status(thm), theory('equality')], [c_29, c_123])).
% 1.95/1.17  tff(c_139, plain, (![B_11, A_10]: (k10_relat_1(k6_partfun1(B_11), A_10)=k3_xboole_0(A_10, B_11))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_31, c_135])).
% 1.95/1.17  tff(c_22, plain, (![A_16]: (m1_subset_1(k6_partfun1(A_16), k1_zfmisc_1(k2_zfmisc_1(A_16, A_16))))), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.95/1.17  tff(c_161, plain, (![A_40, B_41, C_42, D_43]: (k8_relset_1(A_40, B_41, C_42, D_43)=k10_relat_1(C_42, D_43) | ~m1_subset_1(C_42, k1_zfmisc_1(k2_zfmisc_1(A_40, B_41))))), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.95/1.17  tff(c_163, plain, (![A_16, D_43]: (k8_relset_1(A_16, A_16, k6_partfun1(A_16), D_43)=k10_relat_1(k6_partfun1(A_16), D_43))), inference(resolution, [status(thm)], [c_22, c_161])).
% 1.95/1.17  tff(c_168, plain, (![A_16, D_43]: (k8_relset_1(A_16, A_16, k6_partfun1(A_16), D_43)=k3_xboole_0(D_43, A_16))), inference(demodulation, [status(thm), theory('equality')], [c_139, c_163])).
% 1.95/1.17  tff(c_26, plain, (k8_relset_1('#skF_1', '#skF_1', k6_partfun1('#skF_1'), '#skF_2')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_63])).
% 1.95/1.17  tff(c_170, plain, (k3_xboole_0('#skF_2', '#skF_1')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_168, c_26])).
% 1.95/1.17  tff(c_173, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_86, c_170])).
% 1.95/1.17  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.95/1.17  
% 1.95/1.17  Inference rules
% 1.95/1.17  ----------------------
% 1.95/1.17  #Ref     : 0
% 1.95/1.17  #Sup     : 30
% 1.95/1.17  #Fact    : 0
% 1.95/1.17  #Define  : 0
% 1.95/1.17  #Split   : 0
% 1.95/1.17  #Chain   : 0
% 1.95/1.17  #Close   : 0
% 1.95/1.17  
% 1.95/1.17  Ordering : KBO
% 1.95/1.17  
% 1.95/1.17  Simplification rules
% 1.95/1.17  ----------------------
% 1.95/1.17  #Subsume      : 0
% 1.95/1.17  #Demod        : 14
% 1.95/1.17  #Tautology    : 19
% 1.95/1.17  #SimpNegUnit  : 0
% 1.95/1.17  #BackRed      : 1
% 1.95/1.17  
% 1.95/1.17  #Partial instantiations: 0
% 1.95/1.17  #Strategies tried      : 1
% 1.95/1.17  
% 1.95/1.17  Timing (in seconds)
% 1.95/1.17  ----------------------
% 1.95/1.18  Preprocessing        : 0.29
% 1.95/1.18  Parsing              : 0.15
% 1.95/1.18  CNF conversion       : 0.02
% 1.95/1.18  Main loop            : 0.14
% 1.95/1.18  Inferencing          : 0.05
% 1.95/1.18  Reduction            : 0.04
% 1.95/1.18  Demodulation         : 0.03
% 1.95/1.18  BG Simplification    : 0.01
% 1.95/1.18  Subsumption          : 0.01
% 1.95/1.18  Abstraction          : 0.01
% 1.95/1.18  MUC search           : 0.00
% 1.95/1.18  Cooper               : 0.00
% 1.95/1.18  Total                : 0.46
% 1.95/1.18  Index Insertion      : 0.00
% 1.95/1.18  Index Deletion       : 0.00
% 1.95/1.18  Index Matching       : 0.00
% 1.95/1.18  BG Taut test         : 0.00
%------------------------------------------------------------------------------

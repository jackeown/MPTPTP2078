%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:18 EST 2020

% Result     : Theorem 1.92s
% Output     : CNFRefutation 1.92s
% Verified   : 
% Statistics : Number of formulae       :   54 (  75 expanded)
%              Number of leaves         :   29 (  39 expanded)
%              Depth                    :    9
%              Number of atoms          :   52 (  76 expanded)
%              Number of equality atoms :   25 (  44 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > k8_relset_1 > k5_relat_1 > k3_xboole_0 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

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

tff(f_48,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v2_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_funct_1)).

tff(f_44,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_50,axiom,(
    ! [A,B] : k5_relat_1(k6_relat_1(B),k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_funct_1)).

tff(f_40,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k1_relat_1(k5_relat_1(A,B)) = k10_relat_1(A,k1_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t182_relat_1)).

tff(f_56,axiom,(
    ! [A] : m1_subset_1(k6_relat_1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_relset_1)).

tff(f_54,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(c_28,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_65,plain,(
    ! [A_25,B_26] :
      ( r1_tarski(A_25,B_26)
      | ~ m1_subset_1(A_25,k1_zfmisc_1(B_26)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_73,plain,(
    r1_tarski('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_28,c_65])).

tff(c_74,plain,(
    ! [A_27,B_28] :
      ( k3_xboole_0(A_27,B_28) = A_27
      | ~ r1_tarski(A_27,B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_78,plain,(
    k3_xboole_0('#skF_2','#skF_1') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_73,c_74])).

tff(c_24,plain,(
    ! [A_17] : k6_relat_1(A_17) = k6_partfun1(A_17) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_14,plain,(
    ! [A_9] : v1_relat_1(k6_relat_1(A_9)) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_32,plain,(
    ! [A_9] : v1_relat_1(k6_partfun1(A_9)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_14])).

tff(c_10,plain,(
    ! [A_8] : k1_relat_1(k6_relat_1(A_8)) = A_8 ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_34,plain,(
    ! [A_8] : k1_relat_1(k6_partfun1(A_8)) = A_8 ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_10])).

tff(c_18,plain,(
    ! [B_11,A_10] : k5_relat_1(k6_relat_1(B_11),k6_relat_1(A_10)) = k6_relat_1(k3_xboole_0(A_10,B_11)) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_30,plain,(
    ! [B_11,A_10] : k5_relat_1(k6_partfun1(B_11),k6_partfun1(A_10)) = k6_partfun1(k3_xboole_0(A_10,B_11)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_24,c_24,c_18])).

tff(c_111,plain,(
    ! [A_34,B_35] :
      ( k10_relat_1(A_34,k1_relat_1(B_35)) = k1_relat_1(k5_relat_1(A_34,B_35))
      | ~ v1_relat_1(B_35)
      | ~ v1_relat_1(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_120,plain,(
    ! [A_34,A_8] :
      ( k1_relat_1(k5_relat_1(A_34,k6_partfun1(A_8))) = k10_relat_1(A_34,A_8)
      | ~ v1_relat_1(k6_partfun1(A_8))
      | ~ v1_relat_1(A_34) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_111])).

tff(c_125,plain,(
    ! [A_36,A_37] :
      ( k1_relat_1(k5_relat_1(A_36,k6_partfun1(A_37))) = k10_relat_1(A_36,A_37)
      | ~ v1_relat_1(A_36) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_120])).

tff(c_137,plain,(
    ! [A_10,B_11] :
      ( k1_relat_1(k6_partfun1(k3_xboole_0(A_10,B_11))) = k10_relat_1(k6_partfun1(B_11),A_10)
      | ~ v1_relat_1(k6_partfun1(B_11)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_125])).

tff(c_141,plain,(
    ! [B_11,A_10] : k10_relat_1(k6_partfun1(B_11),A_10) = k3_xboole_0(A_10,B_11) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_34,c_137])).

tff(c_22,plain,(
    ! [A_16] : m1_subset_1(k6_relat_1(A_16),k1_zfmisc_1(k2_zfmisc_1(A_16,A_16))) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_29,plain,(
    ! [A_16] : m1_subset_1(k6_partfun1(A_16),k1_zfmisc_1(k2_zfmisc_1(A_16,A_16))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_22])).

tff(c_163,plain,(
    ! [A_40,B_41,C_42,D_43] :
      ( k8_relset_1(A_40,B_41,C_42,D_43) = k10_relat_1(C_42,D_43)
      | ~ m1_subset_1(C_42,k1_zfmisc_1(k2_zfmisc_1(A_40,B_41))) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_165,plain,(
    ! [A_16,D_43] : k8_relset_1(A_16,A_16,k6_partfun1(A_16),D_43) = k10_relat_1(k6_partfun1(A_16),D_43) ),
    inference(resolution,[status(thm)],[c_29,c_163])).

tff(c_170,plain,(
    ! [A_16,D_43] : k8_relset_1(A_16,A_16,k6_partfun1(A_16),D_43) = k3_xboole_0(D_43,A_16) ),
    inference(demodulation,[status(thm),theory(equality)],[c_141,c_165])).

tff(c_26,plain,(
    k8_relset_1('#skF_1','#skF_1',k6_partfun1('#skF_1'),'#skF_2') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_172,plain,(
    k3_xboole_0('#skF_2','#skF_1') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_170,c_26])).

tff(c_175,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_172])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:12:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.92/1.26  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.92/1.27  
% 1.92/1.27  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.92/1.27  %$ r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > k8_relset_1 > k5_relat_1 > k3_xboole_0 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_1
% 1.92/1.27  
% 1.92/1.27  %Foreground sorts:
% 1.92/1.27  
% 1.92/1.27  
% 1.92/1.27  %Background operators:
% 1.92/1.27  
% 1.92/1.27  
% 1.92/1.27  %Foreground operators:
% 1.92/1.27  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 1.92/1.27  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.92/1.27  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 1.92/1.27  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 1.92/1.27  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.92/1.27  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.92/1.27  tff('#skF_2', type, '#skF_2': $i).
% 1.92/1.27  tff('#skF_1', type, '#skF_1': $i).
% 1.92/1.27  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.92/1.27  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 1.92/1.27  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.92/1.27  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 1.92/1.27  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.92/1.27  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.92/1.27  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 1.92/1.27  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.92/1.27  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.92/1.27  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.92/1.27  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.92/1.27  
% 1.92/1.28  tff(f_63, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k8_relset_1(A, A, k6_partfun1(A), B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t171_funct_2)).
% 1.92/1.28  tff(f_33, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 1.92/1.28  tff(f_29, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 1.92/1.28  tff(f_58, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 1.92/1.28  tff(f_48, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v2_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc4_funct_1)).
% 1.92/1.28  tff(f_44, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 1.92/1.28  tff(f_50, axiom, (![A, B]: (k5_relat_1(k6_relat_1(B), k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_funct_1)).
% 1.92/1.28  tff(f_40, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k1_relat_1(k5_relat_1(A, B)) = k10_relat_1(A, k1_relat_1(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t182_relat_1)).
% 1.92/1.28  tff(f_56, axiom, (![A]: m1_subset_1(k6_relat_1(A), k1_zfmisc_1(k2_zfmisc_1(A, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_relset_1)).
% 1.92/1.28  tff(f_54, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 1.92/1.28  tff(c_28, plain, (m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_63])).
% 1.92/1.28  tff(c_65, plain, (![A_25, B_26]: (r1_tarski(A_25, B_26) | ~m1_subset_1(A_25, k1_zfmisc_1(B_26)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.92/1.28  tff(c_73, plain, (r1_tarski('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_28, c_65])).
% 1.92/1.28  tff(c_74, plain, (![A_27, B_28]: (k3_xboole_0(A_27, B_28)=A_27 | ~r1_tarski(A_27, B_28))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.92/1.28  tff(c_78, plain, (k3_xboole_0('#skF_2', '#skF_1')='#skF_2'), inference(resolution, [status(thm)], [c_73, c_74])).
% 1.92/1.28  tff(c_24, plain, (![A_17]: (k6_relat_1(A_17)=k6_partfun1(A_17))), inference(cnfTransformation, [status(thm)], [f_58])).
% 1.92/1.28  tff(c_14, plain, (![A_9]: (v1_relat_1(k6_relat_1(A_9)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.92/1.28  tff(c_32, plain, (![A_9]: (v1_relat_1(k6_partfun1(A_9)))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_14])).
% 1.92/1.28  tff(c_10, plain, (![A_8]: (k1_relat_1(k6_relat_1(A_8))=A_8)), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.92/1.28  tff(c_34, plain, (![A_8]: (k1_relat_1(k6_partfun1(A_8))=A_8)), inference(demodulation, [status(thm), theory('equality')], [c_24, c_10])).
% 1.92/1.28  tff(c_18, plain, (![B_11, A_10]: (k5_relat_1(k6_relat_1(B_11), k6_relat_1(A_10))=k6_relat_1(k3_xboole_0(A_10, B_11)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.92/1.28  tff(c_30, plain, (![B_11, A_10]: (k5_relat_1(k6_partfun1(B_11), k6_partfun1(A_10))=k6_partfun1(k3_xboole_0(A_10, B_11)))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_24, c_24, c_18])).
% 1.92/1.28  tff(c_111, plain, (![A_34, B_35]: (k10_relat_1(A_34, k1_relat_1(B_35))=k1_relat_1(k5_relat_1(A_34, B_35)) | ~v1_relat_1(B_35) | ~v1_relat_1(A_34))), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.92/1.28  tff(c_120, plain, (![A_34, A_8]: (k1_relat_1(k5_relat_1(A_34, k6_partfun1(A_8)))=k10_relat_1(A_34, A_8) | ~v1_relat_1(k6_partfun1(A_8)) | ~v1_relat_1(A_34))), inference(superposition, [status(thm), theory('equality')], [c_34, c_111])).
% 1.92/1.28  tff(c_125, plain, (![A_36, A_37]: (k1_relat_1(k5_relat_1(A_36, k6_partfun1(A_37)))=k10_relat_1(A_36, A_37) | ~v1_relat_1(A_36))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_120])).
% 1.92/1.28  tff(c_137, plain, (![A_10, B_11]: (k1_relat_1(k6_partfun1(k3_xboole_0(A_10, B_11)))=k10_relat_1(k6_partfun1(B_11), A_10) | ~v1_relat_1(k6_partfun1(B_11)))), inference(superposition, [status(thm), theory('equality')], [c_30, c_125])).
% 1.92/1.28  tff(c_141, plain, (![B_11, A_10]: (k10_relat_1(k6_partfun1(B_11), A_10)=k3_xboole_0(A_10, B_11))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_34, c_137])).
% 1.92/1.28  tff(c_22, plain, (![A_16]: (m1_subset_1(k6_relat_1(A_16), k1_zfmisc_1(k2_zfmisc_1(A_16, A_16))))), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.92/1.28  tff(c_29, plain, (![A_16]: (m1_subset_1(k6_partfun1(A_16), k1_zfmisc_1(k2_zfmisc_1(A_16, A_16))))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_22])).
% 1.92/1.28  tff(c_163, plain, (![A_40, B_41, C_42, D_43]: (k8_relset_1(A_40, B_41, C_42, D_43)=k10_relat_1(C_42, D_43) | ~m1_subset_1(C_42, k1_zfmisc_1(k2_zfmisc_1(A_40, B_41))))), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.92/1.28  tff(c_165, plain, (![A_16, D_43]: (k8_relset_1(A_16, A_16, k6_partfun1(A_16), D_43)=k10_relat_1(k6_partfun1(A_16), D_43))), inference(resolution, [status(thm)], [c_29, c_163])).
% 1.92/1.28  tff(c_170, plain, (![A_16, D_43]: (k8_relset_1(A_16, A_16, k6_partfun1(A_16), D_43)=k3_xboole_0(D_43, A_16))), inference(demodulation, [status(thm), theory('equality')], [c_141, c_165])).
% 1.92/1.28  tff(c_26, plain, (k8_relset_1('#skF_1', '#skF_1', k6_partfun1('#skF_1'), '#skF_2')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_63])).
% 1.92/1.28  tff(c_172, plain, (k3_xboole_0('#skF_2', '#skF_1')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_170, c_26])).
% 1.92/1.28  tff(c_175, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_78, c_172])).
% 1.92/1.28  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.92/1.28  
% 1.92/1.28  Inference rules
% 1.92/1.28  ----------------------
% 1.92/1.28  #Ref     : 0
% 1.92/1.28  #Sup     : 30
% 1.92/1.28  #Fact    : 0
% 1.92/1.28  #Define  : 0
% 1.92/1.28  #Split   : 0
% 1.92/1.28  #Chain   : 0
% 1.92/1.28  #Close   : 0
% 1.92/1.28  
% 1.92/1.28  Ordering : KBO
% 1.92/1.28  
% 1.92/1.28  Simplification rules
% 1.92/1.28  ----------------------
% 1.92/1.28  #Subsume      : 0
% 1.92/1.28  #Demod        : 16
% 1.92/1.28  #Tautology    : 19
% 1.92/1.28  #SimpNegUnit  : 0
% 1.92/1.28  #BackRed      : 1
% 1.92/1.28  
% 1.92/1.28  #Partial instantiations: 0
% 1.92/1.28  #Strategies tried      : 1
% 1.92/1.28  
% 1.92/1.28  Timing (in seconds)
% 1.92/1.28  ----------------------
% 1.92/1.29  Preprocessing        : 0.32
% 1.92/1.29  Parsing              : 0.17
% 1.92/1.29  CNF conversion       : 0.02
% 1.92/1.29  Main loop            : 0.13
% 1.92/1.29  Inferencing          : 0.05
% 1.92/1.29  Reduction            : 0.04
% 1.92/1.29  Demodulation         : 0.03
% 1.92/1.29  BG Simplification    : 0.01
% 1.92/1.29  Subsumption          : 0.01
% 1.92/1.29  Abstraction          : 0.01
% 1.92/1.29  MUC search           : 0.00
% 1.92/1.29  Cooper               : 0.00
% 1.92/1.29  Total                : 0.48
% 1.92/1.29  Index Insertion      : 0.00
% 1.92/1.29  Index Deletion       : 0.00
% 1.92/1.29  Index Matching       : 0.00
% 1.92/1.29  BG Taut test         : 0.00
%------------------------------------------------------------------------------

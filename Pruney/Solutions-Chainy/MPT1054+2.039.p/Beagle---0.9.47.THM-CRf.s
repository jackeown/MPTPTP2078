%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:17 EST 2020

% Result     : Theorem 1.93s
% Output     : CNFRefutation 1.93s
% Verified   : 
% Statistics : Number of formulae       :   53 (  74 expanded)
%              Number of leaves         :   28 (  38 expanded)
%              Depth                    :    9
%              Number of atoms          :   51 (  74 expanded)
%              Number of equality atoms :   25 (  44 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > v1_relat_1 > k8_relset_1 > k5_relat_1 > k3_xboole_0 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_1

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_61,negated_conjecture,(
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

tff(f_56,axiom,(
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

tff(f_54,axiom,(
    ! [A] : m1_subset_1(k6_relat_1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_relset_1)).

tff(f_52,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(c_26,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_60,plain,(
    ! [A_22,B_23] :
      ( r1_tarski(A_22,B_23)
      | ~ m1_subset_1(A_22,k1_zfmisc_1(B_23)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_64,plain,(
    r1_tarski('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_26,c_60])).

tff(c_70,plain,(
    ! [A_26,B_27] :
      ( k3_xboole_0(A_26,B_27) = A_26
      | ~ r1_tarski(A_26,B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_74,plain,(
    k3_xboole_0('#skF_2','#skF_1') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_64,c_70])).

tff(c_22,plain,(
    ! [A_17] : k6_relat_1(A_17) = k6_partfun1(A_17) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_8,plain,(
    ! [A_5] : v1_relat_1(k6_relat_1(A_5)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_31,plain,(
    ! [A_5] : v1_relat_1(k6_partfun1(A_5)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_8])).

tff(c_12,plain,(
    ! [A_9] : k1_relat_1(k6_relat_1(A_9)) = A_9 ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_30,plain,(
    ! [A_9] : k1_relat_1(k6_partfun1(A_9)) = A_9 ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_12])).

tff(c_16,plain,(
    ! [B_11,A_10] : k5_relat_1(k6_relat_1(B_11),k6_relat_1(A_10)) = k6_relat_1(k3_xboole_0(A_10,B_11)) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_28,plain,(
    ! [B_11,A_10] : k5_relat_1(k6_partfun1(B_11),k6_partfun1(A_10)) = k6_partfun1(k3_xboole_0(A_10,B_11)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_22,c_22,c_16])).

tff(c_107,plain,(
    ! [A_33,B_34] :
      ( k10_relat_1(A_33,k1_relat_1(B_34)) = k1_relat_1(k5_relat_1(A_33,B_34))
      | ~ v1_relat_1(B_34)
      | ~ v1_relat_1(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_116,plain,(
    ! [A_33,A_9] :
      ( k1_relat_1(k5_relat_1(A_33,k6_partfun1(A_9))) = k10_relat_1(A_33,A_9)
      | ~ v1_relat_1(k6_partfun1(A_9))
      | ~ v1_relat_1(A_33) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_107])).

tff(c_121,plain,(
    ! [A_35,A_36] :
      ( k1_relat_1(k5_relat_1(A_35,k6_partfun1(A_36))) = k10_relat_1(A_35,A_36)
      | ~ v1_relat_1(A_35) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_31,c_116])).

tff(c_133,plain,(
    ! [A_10,B_11] :
      ( k1_relat_1(k6_partfun1(k3_xboole_0(A_10,B_11))) = k10_relat_1(k6_partfun1(B_11),A_10)
      | ~ v1_relat_1(k6_partfun1(B_11)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_121])).

tff(c_137,plain,(
    ! [B_11,A_10] : k10_relat_1(k6_partfun1(B_11),A_10) = k3_xboole_0(A_10,B_11) ),
    inference(demodulation,[status(thm),theory(equality)],[c_31,c_30,c_133])).

tff(c_20,plain,(
    ! [A_16] : m1_subset_1(k6_relat_1(A_16),k1_zfmisc_1(k2_zfmisc_1(A_16,A_16))) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_27,plain,(
    ! [A_16] : m1_subset_1(k6_partfun1(A_16),k1_zfmisc_1(k2_zfmisc_1(A_16,A_16))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_20])).

tff(c_188,plain,(
    ! [A_41,B_42,C_43,D_44] :
      ( k8_relset_1(A_41,B_42,C_43,D_44) = k10_relat_1(C_43,D_44)
      | ~ m1_subset_1(C_43,k1_zfmisc_1(k2_zfmisc_1(A_41,B_42))) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_190,plain,(
    ! [A_16,D_44] : k8_relset_1(A_16,A_16,k6_partfun1(A_16),D_44) = k10_relat_1(k6_partfun1(A_16),D_44) ),
    inference(resolution,[status(thm)],[c_27,c_188])).

tff(c_195,plain,(
    ! [A_16,D_44] : k8_relset_1(A_16,A_16,k6_partfun1(A_16),D_44) = k3_xboole_0(D_44,A_16) ),
    inference(demodulation,[status(thm),theory(equality)],[c_137,c_190])).

tff(c_24,plain,(
    k8_relset_1('#skF_1','#skF_1',k6_partfun1('#skF_1'),'#skF_2') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_197,plain,(
    k3_xboole_0('#skF_2','#skF_1') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_195,c_24])).

tff(c_200,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_197])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:01:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.93/1.19  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.93/1.19  
% 1.93/1.19  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.93/1.20  %$ r1_tarski > m1_subset_1 > v1_relat_1 > k8_relset_1 > k5_relat_1 > k3_xboole_0 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_1
% 1.93/1.20  
% 1.93/1.20  %Foreground sorts:
% 1.93/1.20  
% 1.93/1.20  
% 1.93/1.20  %Background operators:
% 1.93/1.20  
% 1.93/1.20  
% 1.93/1.20  %Foreground operators:
% 1.93/1.20  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.93/1.20  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 1.93/1.20  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 1.93/1.20  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.93/1.20  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.93/1.20  tff('#skF_2', type, '#skF_2': $i).
% 1.93/1.20  tff('#skF_1', type, '#skF_1': $i).
% 1.93/1.20  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.93/1.20  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 1.93/1.20  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.93/1.20  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 1.93/1.20  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.93/1.20  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.93/1.20  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 1.93/1.20  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.93/1.20  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.93/1.20  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.93/1.20  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.93/1.20  
% 1.93/1.21  tff(f_61, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k8_relset_1(A, A, k6_partfun1(A), B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t171_funct_2)).
% 1.93/1.21  tff(f_33, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 1.93/1.21  tff(f_29, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 1.93/1.21  tff(f_56, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 1.93/1.21  tff(f_35, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 1.93/1.21  tff(f_46, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 1.93/1.21  tff(f_48, axiom, (![A, B]: (k5_relat_1(k6_relat_1(B), k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_funct_1)).
% 1.93/1.21  tff(f_42, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k1_relat_1(k5_relat_1(A, B)) = k10_relat_1(A, k1_relat_1(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t182_relat_1)).
% 1.93/1.21  tff(f_54, axiom, (![A]: m1_subset_1(k6_relat_1(A), k1_zfmisc_1(k2_zfmisc_1(A, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_relset_1)).
% 1.93/1.21  tff(f_52, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 1.93/1.21  tff(c_26, plain, (m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_61])).
% 1.93/1.21  tff(c_60, plain, (![A_22, B_23]: (r1_tarski(A_22, B_23) | ~m1_subset_1(A_22, k1_zfmisc_1(B_23)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.93/1.21  tff(c_64, plain, (r1_tarski('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_26, c_60])).
% 1.93/1.21  tff(c_70, plain, (![A_26, B_27]: (k3_xboole_0(A_26, B_27)=A_26 | ~r1_tarski(A_26, B_27))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.93/1.21  tff(c_74, plain, (k3_xboole_0('#skF_2', '#skF_1')='#skF_2'), inference(resolution, [status(thm)], [c_64, c_70])).
% 1.93/1.21  tff(c_22, plain, (![A_17]: (k6_relat_1(A_17)=k6_partfun1(A_17))), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.93/1.21  tff(c_8, plain, (![A_5]: (v1_relat_1(k6_relat_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.93/1.21  tff(c_31, plain, (![A_5]: (v1_relat_1(k6_partfun1(A_5)))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_8])).
% 1.93/1.21  tff(c_12, plain, (![A_9]: (k1_relat_1(k6_relat_1(A_9))=A_9)), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.93/1.21  tff(c_30, plain, (![A_9]: (k1_relat_1(k6_partfun1(A_9))=A_9)), inference(demodulation, [status(thm), theory('equality')], [c_22, c_12])).
% 1.93/1.21  tff(c_16, plain, (![B_11, A_10]: (k5_relat_1(k6_relat_1(B_11), k6_relat_1(A_10))=k6_relat_1(k3_xboole_0(A_10, B_11)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.93/1.21  tff(c_28, plain, (![B_11, A_10]: (k5_relat_1(k6_partfun1(B_11), k6_partfun1(A_10))=k6_partfun1(k3_xboole_0(A_10, B_11)))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_22, c_22, c_16])).
% 1.93/1.21  tff(c_107, plain, (![A_33, B_34]: (k10_relat_1(A_33, k1_relat_1(B_34))=k1_relat_1(k5_relat_1(A_33, B_34)) | ~v1_relat_1(B_34) | ~v1_relat_1(A_33))), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.93/1.21  tff(c_116, plain, (![A_33, A_9]: (k1_relat_1(k5_relat_1(A_33, k6_partfun1(A_9)))=k10_relat_1(A_33, A_9) | ~v1_relat_1(k6_partfun1(A_9)) | ~v1_relat_1(A_33))), inference(superposition, [status(thm), theory('equality')], [c_30, c_107])).
% 1.93/1.21  tff(c_121, plain, (![A_35, A_36]: (k1_relat_1(k5_relat_1(A_35, k6_partfun1(A_36)))=k10_relat_1(A_35, A_36) | ~v1_relat_1(A_35))), inference(demodulation, [status(thm), theory('equality')], [c_31, c_116])).
% 1.93/1.21  tff(c_133, plain, (![A_10, B_11]: (k1_relat_1(k6_partfun1(k3_xboole_0(A_10, B_11)))=k10_relat_1(k6_partfun1(B_11), A_10) | ~v1_relat_1(k6_partfun1(B_11)))), inference(superposition, [status(thm), theory('equality')], [c_28, c_121])).
% 1.93/1.21  tff(c_137, plain, (![B_11, A_10]: (k10_relat_1(k6_partfun1(B_11), A_10)=k3_xboole_0(A_10, B_11))), inference(demodulation, [status(thm), theory('equality')], [c_31, c_30, c_133])).
% 1.93/1.21  tff(c_20, plain, (![A_16]: (m1_subset_1(k6_relat_1(A_16), k1_zfmisc_1(k2_zfmisc_1(A_16, A_16))))), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.93/1.21  tff(c_27, plain, (![A_16]: (m1_subset_1(k6_partfun1(A_16), k1_zfmisc_1(k2_zfmisc_1(A_16, A_16))))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_20])).
% 1.93/1.21  tff(c_188, plain, (![A_41, B_42, C_43, D_44]: (k8_relset_1(A_41, B_42, C_43, D_44)=k10_relat_1(C_43, D_44) | ~m1_subset_1(C_43, k1_zfmisc_1(k2_zfmisc_1(A_41, B_42))))), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.93/1.21  tff(c_190, plain, (![A_16, D_44]: (k8_relset_1(A_16, A_16, k6_partfun1(A_16), D_44)=k10_relat_1(k6_partfun1(A_16), D_44))), inference(resolution, [status(thm)], [c_27, c_188])).
% 1.93/1.21  tff(c_195, plain, (![A_16, D_44]: (k8_relset_1(A_16, A_16, k6_partfun1(A_16), D_44)=k3_xboole_0(D_44, A_16))), inference(demodulation, [status(thm), theory('equality')], [c_137, c_190])).
% 1.93/1.21  tff(c_24, plain, (k8_relset_1('#skF_1', '#skF_1', k6_partfun1('#skF_1'), '#skF_2')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_61])).
% 1.93/1.21  tff(c_197, plain, (k3_xboole_0('#skF_2', '#skF_1')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_195, c_24])).
% 1.93/1.21  tff(c_200, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_74, c_197])).
% 1.93/1.21  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.93/1.21  
% 1.93/1.21  Inference rules
% 1.93/1.21  ----------------------
% 1.93/1.21  #Ref     : 0
% 1.93/1.21  #Sup     : 36
% 1.93/1.21  #Fact    : 0
% 1.93/1.21  #Define  : 0
% 1.93/1.21  #Split   : 0
% 1.93/1.21  #Chain   : 0
% 1.93/1.21  #Close   : 0
% 1.93/1.21  
% 1.93/1.21  Ordering : KBO
% 1.93/1.21  
% 1.93/1.21  Simplification rules
% 1.93/1.21  ----------------------
% 1.93/1.21  #Subsume      : 0
% 1.93/1.21  #Demod        : 26
% 1.93/1.21  #Tautology    : 24
% 1.93/1.21  #SimpNegUnit  : 0
% 1.93/1.21  #BackRed      : 1
% 1.93/1.21  
% 1.93/1.21  #Partial instantiations: 0
% 1.93/1.21  #Strategies tried      : 1
% 1.93/1.21  
% 1.93/1.21  Timing (in seconds)
% 1.93/1.21  ----------------------
% 2.05/1.21  Preprocessing        : 0.30
% 2.05/1.21  Parsing              : 0.16
% 2.05/1.21  CNF conversion       : 0.02
% 2.05/1.21  Main loop            : 0.15
% 2.05/1.21  Inferencing          : 0.06
% 2.05/1.21  Reduction            : 0.05
% 2.05/1.21  Demodulation         : 0.04
% 2.05/1.21  BG Simplification    : 0.01
% 2.05/1.21  Subsumption          : 0.02
% 2.05/1.21  Abstraction          : 0.01
% 2.05/1.21  MUC search           : 0.00
% 2.05/1.21  Cooper               : 0.00
% 2.05/1.21  Total                : 0.48
% 2.05/1.21  Index Insertion      : 0.00
% 2.05/1.21  Index Deletion       : 0.00
% 2.05/1.21  Index Matching       : 0.00
% 2.05/1.21  BG Taut test         : 0.00
%------------------------------------------------------------------------------

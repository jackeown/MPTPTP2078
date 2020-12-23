%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:18 EST 2020

% Result     : Theorem 2.05s
% Output     : CNFRefutation 2.05s
% Verified   : 
% Statistics : Number of formulae       :   60 (  79 expanded)
%              Number of leaves         :   28 (  39 expanded)
%              Depth                    :    8
%              Number of atoms          :   70 (  94 expanded)
%              Number of equality atoms :   24 (  39 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k9_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

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

tff(f_66,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => k8_relset_1(A,A,k6_partfun1(A),B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t171_funct_2)).

tff(f_29,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_61,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_41,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_37,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k10_relat_1(B,A),k1_relat_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t167_relat_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r1_tarski(A,k2_relat_1(B))
       => k9_relat_1(B,k10_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t147_funct_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k9_relat_1(k6_relat_1(A),B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t162_funct_1)).

tff(f_59,axiom,(
    ! [A] : m1_subset_1(k6_relat_1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_relset_1)).

tff(f_57,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(c_28,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_66,plain,(
    ! [A_25,B_26] :
      ( r1_tarski(A_25,B_26)
      | ~ m1_subset_1(A_25,k1_zfmisc_1(B_26)) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_78,plain,(
    r1_tarski('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_28,c_66])).

tff(c_24,plain,(
    ! [A_16] : k6_relat_1(A_16) = k6_partfun1(A_16) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_12,plain,(
    ! [A_6] : v1_relat_1(k6_relat_1(A_6)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_32,plain,(
    ! [A_6] : v1_relat_1(k6_partfun1(A_6)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_12])).

tff(c_8,plain,(
    ! [A_5] : k1_relat_1(k6_relat_1(A_5)) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_34,plain,(
    ! [A_5] : k1_relat_1(k6_partfun1(A_5)) = A_5 ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_8])).

tff(c_80,plain,(
    ! [B_28,A_29] :
      ( r1_tarski(k10_relat_1(B_28,A_29),k1_relat_1(B_28))
      | ~ v1_relat_1(B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_83,plain,(
    ! [A_5,A_29] :
      ( r1_tarski(k10_relat_1(k6_partfun1(A_5),A_29),A_5)
      | ~ v1_relat_1(k6_partfun1(A_5)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_80])).

tff(c_85,plain,(
    ! [A_5,A_29] : r1_tarski(k10_relat_1(k6_partfun1(A_5),A_29),A_5) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_83])).

tff(c_14,plain,(
    ! [A_6] : v1_funct_1(k6_relat_1(A_6)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_31,plain,(
    ! [A_6] : v1_funct_1(k6_partfun1(A_6)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_14])).

tff(c_10,plain,(
    ! [A_5] : k2_relat_1(k6_relat_1(A_5)) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_33,plain,(
    ! [A_5] : k2_relat_1(k6_partfun1(A_5)) = A_5 ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_10])).

tff(c_154,plain,(
    ! [B_41,A_42] :
      ( k9_relat_1(B_41,k10_relat_1(B_41,A_42)) = A_42
      | ~ r1_tarski(A_42,k2_relat_1(B_41))
      | ~ v1_funct_1(B_41)
      | ~ v1_relat_1(B_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_159,plain,(
    ! [A_5,A_42] :
      ( k9_relat_1(k6_partfun1(A_5),k10_relat_1(k6_partfun1(A_5),A_42)) = A_42
      | ~ r1_tarski(A_42,A_5)
      | ~ v1_funct_1(k6_partfun1(A_5))
      | ~ v1_relat_1(k6_partfun1(A_5)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_33,c_154])).

tff(c_173,plain,(
    ! [A_45,A_46] :
      ( k9_relat_1(k6_partfun1(A_45),k10_relat_1(k6_partfun1(A_45),A_46)) = A_46
      | ~ r1_tarski(A_46,A_45) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_31,c_159])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( m1_subset_1(A_1,k1_zfmisc_1(B_2))
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_18,plain,(
    ! [A_9,B_10] :
      ( k9_relat_1(k6_relat_1(A_9),B_10) = B_10
      | ~ m1_subset_1(B_10,k1_zfmisc_1(A_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_87,plain,(
    ! [A_32,B_33] :
      ( k9_relat_1(k6_partfun1(A_32),B_33) = B_33
      | ~ m1_subset_1(B_33,k1_zfmisc_1(A_32)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_18])).

tff(c_98,plain,(
    ! [B_2,A_1] :
      ( k9_relat_1(k6_partfun1(B_2),A_1) = A_1
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(resolution,[status(thm)],[c_4,c_87])).

tff(c_179,plain,(
    ! [A_45,A_46] :
      ( k10_relat_1(k6_partfun1(A_45),A_46) = A_46
      | ~ r1_tarski(k10_relat_1(k6_partfun1(A_45),A_46),A_45)
      | ~ r1_tarski(A_46,A_45) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_173,c_98])).

tff(c_193,plain,(
    ! [A_47,A_48] :
      ( k10_relat_1(k6_partfun1(A_47),A_48) = A_48
      | ~ r1_tarski(A_48,A_47) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_179])).

tff(c_22,plain,(
    ! [A_15] : m1_subset_1(k6_relat_1(A_15),k1_zfmisc_1(k2_zfmisc_1(A_15,A_15))) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_29,plain,(
    ! [A_15] : m1_subset_1(k6_partfun1(A_15),k1_zfmisc_1(k2_zfmisc_1(A_15,A_15))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_22])).

tff(c_100,plain,(
    ! [A_34,B_35,C_36,D_37] :
      ( k8_relset_1(A_34,B_35,C_36,D_37) = k10_relat_1(C_36,D_37)
      | ~ m1_subset_1(C_36,k1_zfmisc_1(k2_zfmisc_1(A_34,B_35))) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_106,plain,(
    ! [A_15,D_37] : k8_relset_1(A_15,A_15,k6_partfun1(A_15),D_37) = k10_relat_1(k6_partfun1(A_15),D_37) ),
    inference(resolution,[status(thm)],[c_29,c_100])).

tff(c_26,plain,(
    k8_relset_1('#skF_1','#skF_1',k6_partfun1('#skF_1'),'#skF_2') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_163,plain,(
    k10_relat_1(k6_partfun1('#skF_1'),'#skF_2') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_26])).

tff(c_202,plain,(
    ~ r1_tarski('#skF_2','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_193,c_163])).

tff(c_216,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_202])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 09:52:52 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.05/1.33  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.05/1.33  
% 2.05/1.33  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.05/1.34  %$ r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k9_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_1
% 2.05/1.34  
% 2.05/1.34  %Foreground sorts:
% 2.05/1.34  
% 2.05/1.34  
% 2.05/1.34  %Background operators:
% 2.05/1.34  
% 2.05/1.34  
% 2.05/1.34  %Foreground operators:
% 2.05/1.34  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.05/1.34  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.05/1.34  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 2.05/1.34  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.05/1.34  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.05/1.34  tff('#skF_2', type, '#skF_2': $i).
% 2.05/1.34  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.05/1.34  tff('#skF_1', type, '#skF_1': $i).
% 2.05/1.34  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.05/1.34  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 2.05/1.34  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.05/1.34  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.05/1.34  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.05/1.34  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.05/1.34  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.05/1.34  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.05/1.34  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.05/1.34  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.05/1.34  
% 2.05/1.35  tff(f_66, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k8_relset_1(A, A, k6_partfun1(A), B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t171_funct_2)).
% 2.05/1.35  tff(f_29, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 2.05/1.35  tff(f_61, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 2.05/1.35  tff(f_41, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc3_funct_1)).
% 2.05/1.35  tff(f_37, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 2.05/1.35  tff(f_33, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k10_relat_1(B, A), k1_relat_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t167_relat_1)).
% 2.05/1.35  tff(f_49, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(A, k2_relat_1(B)) => (k9_relat_1(B, k10_relat_1(B, A)) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t147_funct_1)).
% 2.05/1.35  tff(f_53, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k9_relat_1(k6_relat_1(A), B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t162_funct_1)).
% 2.05/1.35  tff(f_59, axiom, (![A]: m1_subset_1(k6_relat_1(A), k1_zfmisc_1(k2_zfmisc_1(A, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_relset_1)).
% 2.05/1.35  tff(f_57, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 2.05/1.35  tff(c_28, plain, (m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.05/1.35  tff(c_66, plain, (![A_25, B_26]: (r1_tarski(A_25, B_26) | ~m1_subset_1(A_25, k1_zfmisc_1(B_26)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.05/1.35  tff(c_78, plain, (r1_tarski('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_28, c_66])).
% 2.05/1.35  tff(c_24, plain, (![A_16]: (k6_relat_1(A_16)=k6_partfun1(A_16))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.05/1.35  tff(c_12, plain, (![A_6]: (v1_relat_1(k6_relat_1(A_6)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.05/1.35  tff(c_32, plain, (![A_6]: (v1_relat_1(k6_partfun1(A_6)))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_12])).
% 2.05/1.35  tff(c_8, plain, (![A_5]: (k1_relat_1(k6_relat_1(A_5))=A_5)), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.05/1.35  tff(c_34, plain, (![A_5]: (k1_relat_1(k6_partfun1(A_5))=A_5)), inference(demodulation, [status(thm), theory('equality')], [c_24, c_8])).
% 2.05/1.35  tff(c_80, plain, (![B_28, A_29]: (r1_tarski(k10_relat_1(B_28, A_29), k1_relat_1(B_28)) | ~v1_relat_1(B_28))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.05/1.35  tff(c_83, plain, (![A_5, A_29]: (r1_tarski(k10_relat_1(k6_partfun1(A_5), A_29), A_5) | ~v1_relat_1(k6_partfun1(A_5)))), inference(superposition, [status(thm), theory('equality')], [c_34, c_80])).
% 2.05/1.35  tff(c_85, plain, (![A_5, A_29]: (r1_tarski(k10_relat_1(k6_partfun1(A_5), A_29), A_5))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_83])).
% 2.05/1.35  tff(c_14, plain, (![A_6]: (v1_funct_1(k6_relat_1(A_6)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.05/1.35  tff(c_31, plain, (![A_6]: (v1_funct_1(k6_partfun1(A_6)))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_14])).
% 2.05/1.35  tff(c_10, plain, (![A_5]: (k2_relat_1(k6_relat_1(A_5))=A_5)), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.05/1.35  tff(c_33, plain, (![A_5]: (k2_relat_1(k6_partfun1(A_5))=A_5)), inference(demodulation, [status(thm), theory('equality')], [c_24, c_10])).
% 2.05/1.35  tff(c_154, plain, (![B_41, A_42]: (k9_relat_1(B_41, k10_relat_1(B_41, A_42))=A_42 | ~r1_tarski(A_42, k2_relat_1(B_41)) | ~v1_funct_1(B_41) | ~v1_relat_1(B_41))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.05/1.35  tff(c_159, plain, (![A_5, A_42]: (k9_relat_1(k6_partfun1(A_5), k10_relat_1(k6_partfun1(A_5), A_42))=A_42 | ~r1_tarski(A_42, A_5) | ~v1_funct_1(k6_partfun1(A_5)) | ~v1_relat_1(k6_partfun1(A_5)))), inference(superposition, [status(thm), theory('equality')], [c_33, c_154])).
% 2.05/1.35  tff(c_173, plain, (![A_45, A_46]: (k9_relat_1(k6_partfun1(A_45), k10_relat_1(k6_partfun1(A_45), A_46))=A_46 | ~r1_tarski(A_46, A_45))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_31, c_159])).
% 2.05/1.35  tff(c_4, plain, (![A_1, B_2]: (m1_subset_1(A_1, k1_zfmisc_1(B_2)) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.05/1.35  tff(c_18, plain, (![A_9, B_10]: (k9_relat_1(k6_relat_1(A_9), B_10)=B_10 | ~m1_subset_1(B_10, k1_zfmisc_1(A_9)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.05/1.35  tff(c_87, plain, (![A_32, B_33]: (k9_relat_1(k6_partfun1(A_32), B_33)=B_33 | ~m1_subset_1(B_33, k1_zfmisc_1(A_32)))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_18])).
% 2.05/1.35  tff(c_98, plain, (![B_2, A_1]: (k9_relat_1(k6_partfun1(B_2), A_1)=A_1 | ~r1_tarski(A_1, B_2))), inference(resolution, [status(thm)], [c_4, c_87])).
% 2.05/1.35  tff(c_179, plain, (![A_45, A_46]: (k10_relat_1(k6_partfun1(A_45), A_46)=A_46 | ~r1_tarski(k10_relat_1(k6_partfun1(A_45), A_46), A_45) | ~r1_tarski(A_46, A_45))), inference(superposition, [status(thm), theory('equality')], [c_173, c_98])).
% 2.05/1.35  tff(c_193, plain, (![A_47, A_48]: (k10_relat_1(k6_partfun1(A_47), A_48)=A_48 | ~r1_tarski(A_48, A_47))), inference(demodulation, [status(thm), theory('equality')], [c_85, c_179])).
% 2.05/1.35  tff(c_22, plain, (![A_15]: (m1_subset_1(k6_relat_1(A_15), k1_zfmisc_1(k2_zfmisc_1(A_15, A_15))))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.05/1.35  tff(c_29, plain, (![A_15]: (m1_subset_1(k6_partfun1(A_15), k1_zfmisc_1(k2_zfmisc_1(A_15, A_15))))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_22])).
% 2.05/1.35  tff(c_100, plain, (![A_34, B_35, C_36, D_37]: (k8_relset_1(A_34, B_35, C_36, D_37)=k10_relat_1(C_36, D_37) | ~m1_subset_1(C_36, k1_zfmisc_1(k2_zfmisc_1(A_34, B_35))))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.05/1.35  tff(c_106, plain, (![A_15, D_37]: (k8_relset_1(A_15, A_15, k6_partfun1(A_15), D_37)=k10_relat_1(k6_partfun1(A_15), D_37))), inference(resolution, [status(thm)], [c_29, c_100])).
% 2.05/1.35  tff(c_26, plain, (k8_relset_1('#skF_1', '#skF_1', k6_partfun1('#skF_1'), '#skF_2')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.05/1.35  tff(c_163, plain, (k10_relat_1(k6_partfun1('#skF_1'), '#skF_2')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_106, c_26])).
% 2.05/1.35  tff(c_202, plain, (~r1_tarski('#skF_2', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_193, c_163])).
% 2.05/1.35  tff(c_216, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_78, c_202])).
% 2.05/1.35  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.05/1.35  
% 2.05/1.35  Inference rules
% 2.05/1.35  ----------------------
% 2.05/1.35  #Ref     : 0
% 2.05/1.35  #Sup     : 39
% 2.05/1.35  #Fact    : 0
% 2.05/1.35  #Define  : 0
% 2.05/1.35  #Split   : 0
% 2.05/1.35  #Chain   : 0
% 2.05/1.35  #Close   : 0
% 2.05/1.35  
% 2.05/1.35  Ordering : KBO
% 2.05/1.35  
% 2.05/1.35  Simplification rules
% 2.05/1.35  ----------------------
% 2.05/1.35  #Subsume      : 1
% 2.05/1.35  #Demod        : 17
% 2.05/1.35  #Tautology    : 22
% 2.05/1.35  #SimpNegUnit  : 0
% 2.05/1.35  #BackRed      : 1
% 2.05/1.35  
% 2.05/1.35  #Partial instantiations: 0
% 2.05/1.35  #Strategies tried      : 1
% 2.05/1.35  
% 2.05/1.35  Timing (in seconds)
% 2.05/1.35  ----------------------
% 2.05/1.35  Preprocessing        : 0.36
% 2.05/1.35  Parsing              : 0.20
% 2.05/1.35  CNF conversion       : 0.02
% 2.05/1.35  Main loop            : 0.16
% 2.05/1.35  Inferencing          : 0.07
% 2.05/1.35  Reduction            : 0.05
% 2.05/1.35  Demodulation         : 0.04
% 2.05/1.35  BG Simplification    : 0.01
% 2.05/1.36  Subsumption          : 0.02
% 2.05/1.36  Abstraction          : 0.01
% 2.05/1.36  MUC search           : 0.00
% 2.05/1.36  Cooper               : 0.00
% 2.05/1.36  Total                : 0.56
% 2.05/1.36  Index Insertion      : 0.00
% 2.05/1.36  Index Deletion       : 0.00
% 2.05/1.36  Index Matching       : 0.00
% 2.05/1.36  BG Taut test         : 0.00
%------------------------------------------------------------------------------

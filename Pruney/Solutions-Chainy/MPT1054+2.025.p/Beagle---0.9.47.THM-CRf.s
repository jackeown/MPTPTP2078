%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:15 EST 2020

% Result     : Theorem 2.49s
% Output     : CNFRefutation 2.49s
% Verified   : 
% Statistics : Number of formulae       :   56 (  71 expanded)
%              Number of leaves         :   29 (  37 expanded)
%              Depth                    :    8
%              Number of atoms          :   62 (  83 expanded)
%              Number of equality atoms :   21 (  31 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_partfun1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k9_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_1

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

tff(f_68,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => k8_relset_1(A,A,k6_partfun1(A),B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t171_funct_2)).

tff(f_29,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_61,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_57,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(f_53,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k8_relset_1(A,B,C,D),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_relset_1)).

tff(f_63,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k9_relat_1(k6_relat_1(A),B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t162_funct_1)).

tff(f_37,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_33,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r1_tarski(A,k2_relat_1(B))
       => k9_relat_1(B,k10_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t147_funct_1)).

tff(c_30,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_66,plain,(
    ! [A_25,B_26] :
      ( r1_tarski(A_25,B_26)
      | ~ m1_subset_1(A_25,k1_zfmisc_1(B_26)) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_70,plain,(
    r1_tarski('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_66])).

tff(c_24,plain,(
    ! [A_17] : m1_subset_1(k6_partfun1(A_17),k1_zfmisc_1(k2_zfmisc_1(A_17,A_17))) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_162,plain,(
    ! [A_40,B_41,C_42,D_43] :
      ( k8_relset_1(A_40,B_41,C_42,D_43) = k10_relat_1(C_42,D_43)
      | ~ m1_subset_1(C_42,k1_zfmisc_1(k2_zfmisc_1(A_40,B_41))) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_168,plain,(
    ! [A_17,D_43] : k8_relset_1(A_17,A_17,k6_partfun1(A_17),D_43) = k10_relat_1(k6_partfun1(A_17),D_43) ),
    inference(resolution,[status(thm)],[c_24,c_162])).

tff(c_185,plain,(
    ! [A_50,B_51,C_52,D_53] :
      ( m1_subset_1(k8_relset_1(A_50,B_51,C_52,D_53),k1_zfmisc_1(A_50))
      | ~ m1_subset_1(C_52,k1_zfmisc_1(k2_zfmisc_1(A_50,B_51))) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_197,plain,(
    ! [A_17,D_43] :
      ( m1_subset_1(k10_relat_1(k6_partfun1(A_17),D_43),k1_zfmisc_1(A_17))
      | ~ m1_subset_1(k6_partfun1(A_17),k1_zfmisc_1(k2_zfmisc_1(A_17,A_17))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_168,c_185])).

tff(c_203,plain,(
    ! [A_54,D_55] : m1_subset_1(k10_relat_1(k6_partfun1(A_54),D_55),k1_zfmisc_1(A_54)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_197])).

tff(c_26,plain,(
    ! [A_18] : k6_relat_1(A_18) = k6_partfun1(A_18) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_16,plain,(
    ! [A_7,B_8] :
      ( k9_relat_1(k6_relat_1(A_7),B_8) = B_8
      | ~ m1_subset_1(B_8,k1_zfmisc_1(A_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_31,plain,(
    ! [A_7,B_8] :
      ( k9_relat_1(k6_partfun1(A_7),B_8) = B_8
      | ~ m1_subset_1(B_8,k1_zfmisc_1(A_7)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_16])).

tff(c_214,plain,(
    ! [A_54,D_55] : k9_relat_1(k6_partfun1(A_54),k10_relat_1(k6_partfun1(A_54),D_55)) = k10_relat_1(k6_partfun1(A_54),D_55) ),
    inference(resolution,[status(thm)],[c_203,c_31])).

tff(c_10,plain,(
    ! [A_4] : v1_relat_1(k6_relat_1(A_4)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_33,plain,(
    ! [A_4] : v1_relat_1(k6_partfun1(A_4)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_10])).

tff(c_12,plain,(
    ! [A_4] : v1_funct_1(k6_relat_1(A_4)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_32,plain,(
    ! [A_4] : v1_funct_1(k6_partfun1(A_4)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_12])).

tff(c_8,plain,(
    ! [A_3] : k2_relat_1(k6_relat_1(A_3)) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_34,plain,(
    ! [A_3] : k2_relat_1(k6_partfun1(A_3)) = A_3 ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_8])).

tff(c_99,plain,(
    ! [B_33,A_34] :
      ( k9_relat_1(B_33,k10_relat_1(B_33,A_34)) = A_34
      | ~ r1_tarski(A_34,k2_relat_1(B_33))
      | ~ v1_funct_1(B_33)
      | ~ v1_relat_1(B_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_101,plain,(
    ! [A_3,A_34] :
      ( k9_relat_1(k6_partfun1(A_3),k10_relat_1(k6_partfun1(A_3),A_34)) = A_34
      | ~ r1_tarski(A_34,A_3)
      | ~ v1_funct_1(k6_partfun1(A_3))
      | ~ v1_relat_1(k6_partfun1(A_3)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_99])).

tff(c_103,plain,(
    ! [A_3,A_34] :
      ( k9_relat_1(k6_partfun1(A_3),k10_relat_1(k6_partfun1(A_3),A_34)) = A_34
      | ~ r1_tarski(A_34,A_3) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_33,c_32,c_101])).

tff(c_280,plain,(
    ! [A_68,A_69] :
      ( k10_relat_1(k6_partfun1(A_68),A_69) = A_69
      | ~ r1_tarski(A_69,A_68) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_214,c_103])).

tff(c_28,plain,(
    k8_relset_1('#skF_1','#skF_1',k6_partfun1('#skF_1'),'#skF_2') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_170,plain,(
    k10_relat_1(k6_partfun1('#skF_1'),'#skF_2') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_168,c_28])).

tff(c_295,plain,(
    ~ r1_tarski('#skF_2','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_280,c_170])).

tff(c_303,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_295])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:19:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.49/1.66  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.49/1.67  
% 2.49/1.67  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.49/1.68  %$ v1_partfun1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k9_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_1
% 2.49/1.68  
% 2.49/1.68  %Foreground sorts:
% 2.49/1.68  
% 2.49/1.68  
% 2.49/1.68  %Background operators:
% 2.49/1.68  
% 2.49/1.68  
% 2.49/1.68  %Foreground operators:
% 2.49/1.68  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.49/1.68  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.49/1.68  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 2.49/1.68  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.49/1.68  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.49/1.68  tff('#skF_2', type, '#skF_2': $i).
% 2.49/1.68  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.49/1.68  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 2.49/1.68  tff('#skF_1', type, '#skF_1': $i).
% 2.49/1.68  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.49/1.68  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 2.49/1.68  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.49/1.68  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.49/1.68  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.49/1.68  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.49/1.68  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.49/1.68  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.49/1.68  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.49/1.68  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.49/1.68  
% 2.49/1.70  tff(f_68, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k8_relset_1(A, A, k6_partfun1(A), B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t171_funct_2)).
% 2.49/1.70  tff(f_29, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 2.49/1.70  tff(f_61, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 2.49/1.70  tff(f_57, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 2.49/1.70  tff(f_53, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k8_relset_1(A, B, C, D), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k8_relset_1)).
% 2.49/1.70  tff(f_63, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 2.49/1.70  tff(f_49, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k9_relat_1(k6_relat_1(A), B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t162_funct_1)).
% 2.49/1.70  tff(f_37, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc3_funct_1)).
% 2.49/1.70  tff(f_33, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 2.49/1.70  tff(f_45, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(A, k2_relat_1(B)) => (k9_relat_1(B, k10_relat_1(B, A)) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t147_funct_1)).
% 2.49/1.70  tff(c_30, plain, (m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.49/1.70  tff(c_66, plain, (![A_25, B_26]: (r1_tarski(A_25, B_26) | ~m1_subset_1(A_25, k1_zfmisc_1(B_26)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.49/1.70  tff(c_70, plain, (r1_tarski('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_30, c_66])).
% 2.49/1.70  tff(c_24, plain, (![A_17]: (m1_subset_1(k6_partfun1(A_17), k1_zfmisc_1(k2_zfmisc_1(A_17, A_17))))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.49/1.70  tff(c_162, plain, (![A_40, B_41, C_42, D_43]: (k8_relset_1(A_40, B_41, C_42, D_43)=k10_relat_1(C_42, D_43) | ~m1_subset_1(C_42, k1_zfmisc_1(k2_zfmisc_1(A_40, B_41))))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.49/1.70  tff(c_168, plain, (![A_17, D_43]: (k8_relset_1(A_17, A_17, k6_partfun1(A_17), D_43)=k10_relat_1(k6_partfun1(A_17), D_43))), inference(resolution, [status(thm)], [c_24, c_162])).
% 2.49/1.70  tff(c_185, plain, (![A_50, B_51, C_52, D_53]: (m1_subset_1(k8_relset_1(A_50, B_51, C_52, D_53), k1_zfmisc_1(A_50)) | ~m1_subset_1(C_52, k1_zfmisc_1(k2_zfmisc_1(A_50, B_51))))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.49/1.70  tff(c_197, plain, (![A_17, D_43]: (m1_subset_1(k10_relat_1(k6_partfun1(A_17), D_43), k1_zfmisc_1(A_17)) | ~m1_subset_1(k6_partfun1(A_17), k1_zfmisc_1(k2_zfmisc_1(A_17, A_17))))), inference(superposition, [status(thm), theory('equality')], [c_168, c_185])).
% 2.49/1.70  tff(c_203, plain, (![A_54, D_55]: (m1_subset_1(k10_relat_1(k6_partfun1(A_54), D_55), k1_zfmisc_1(A_54)))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_197])).
% 2.49/1.70  tff(c_26, plain, (![A_18]: (k6_relat_1(A_18)=k6_partfun1(A_18))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.49/1.70  tff(c_16, plain, (![A_7, B_8]: (k9_relat_1(k6_relat_1(A_7), B_8)=B_8 | ~m1_subset_1(B_8, k1_zfmisc_1(A_7)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.49/1.70  tff(c_31, plain, (![A_7, B_8]: (k9_relat_1(k6_partfun1(A_7), B_8)=B_8 | ~m1_subset_1(B_8, k1_zfmisc_1(A_7)))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_16])).
% 2.49/1.70  tff(c_214, plain, (![A_54, D_55]: (k9_relat_1(k6_partfun1(A_54), k10_relat_1(k6_partfun1(A_54), D_55))=k10_relat_1(k6_partfun1(A_54), D_55))), inference(resolution, [status(thm)], [c_203, c_31])).
% 2.49/1.70  tff(c_10, plain, (![A_4]: (v1_relat_1(k6_relat_1(A_4)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.49/1.70  tff(c_33, plain, (![A_4]: (v1_relat_1(k6_partfun1(A_4)))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_10])).
% 2.49/1.70  tff(c_12, plain, (![A_4]: (v1_funct_1(k6_relat_1(A_4)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.49/1.70  tff(c_32, plain, (![A_4]: (v1_funct_1(k6_partfun1(A_4)))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_12])).
% 2.49/1.70  tff(c_8, plain, (![A_3]: (k2_relat_1(k6_relat_1(A_3))=A_3)), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.49/1.70  tff(c_34, plain, (![A_3]: (k2_relat_1(k6_partfun1(A_3))=A_3)), inference(demodulation, [status(thm), theory('equality')], [c_26, c_8])).
% 2.49/1.70  tff(c_99, plain, (![B_33, A_34]: (k9_relat_1(B_33, k10_relat_1(B_33, A_34))=A_34 | ~r1_tarski(A_34, k2_relat_1(B_33)) | ~v1_funct_1(B_33) | ~v1_relat_1(B_33))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.49/1.70  tff(c_101, plain, (![A_3, A_34]: (k9_relat_1(k6_partfun1(A_3), k10_relat_1(k6_partfun1(A_3), A_34))=A_34 | ~r1_tarski(A_34, A_3) | ~v1_funct_1(k6_partfun1(A_3)) | ~v1_relat_1(k6_partfun1(A_3)))), inference(superposition, [status(thm), theory('equality')], [c_34, c_99])).
% 2.49/1.70  tff(c_103, plain, (![A_3, A_34]: (k9_relat_1(k6_partfun1(A_3), k10_relat_1(k6_partfun1(A_3), A_34))=A_34 | ~r1_tarski(A_34, A_3))), inference(demodulation, [status(thm), theory('equality')], [c_33, c_32, c_101])).
% 2.49/1.70  tff(c_280, plain, (![A_68, A_69]: (k10_relat_1(k6_partfun1(A_68), A_69)=A_69 | ~r1_tarski(A_69, A_68))), inference(demodulation, [status(thm), theory('equality')], [c_214, c_103])).
% 2.49/1.70  tff(c_28, plain, (k8_relset_1('#skF_1', '#skF_1', k6_partfun1('#skF_1'), '#skF_2')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.49/1.70  tff(c_170, plain, (k10_relat_1(k6_partfun1('#skF_1'), '#skF_2')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_168, c_28])).
% 2.49/1.70  tff(c_295, plain, (~r1_tarski('#skF_2', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_280, c_170])).
% 2.49/1.70  tff(c_303, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_70, c_295])).
% 2.49/1.70  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.49/1.70  
% 2.49/1.70  Inference rules
% 2.49/1.70  ----------------------
% 2.49/1.70  #Ref     : 0
% 2.49/1.70  #Sup     : 58
% 2.49/1.70  #Fact    : 0
% 2.49/1.70  #Define  : 0
% 2.49/1.70  #Split   : 0
% 2.49/1.70  #Chain   : 0
% 2.49/1.70  #Close   : 0
% 2.49/1.70  
% 2.49/1.70  Ordering : KBO
% 2.49/1.70  
% 2.49/1.70  Simplification rules
% 2.49/1.70  ----------------------
% 2.49/1.70  #Subsume      : 1
% 2.49/1.70  #Demod        : 22
% 2.49/1.70  #Tautology    : 30
% 2.49/1.70  #SimpNegUnit  : 0
% 2.49/1.70  #BackRed      : 2
% 2.49/1.70  
% 2.49/1.70  #Partial instantiations: 0
% 2.49/1.70  #Strategies tried      : 1
% 2.49/1.70  
% 2.49/1.70  Timing (in seconds)
% 2.49/1.70  ----------------------
% 2.49/1.70  Preprocessing        : 0.45
% 2.49/1.70  Parsing              : 0.24
% 2.49/1.70  CNF conversion       : 0.03
% 2.49/1.70  Main loop            : 0.30
% 2.49/1.70  Inferencing          : 0.12
% 2.49/1.70  Reduction            : 0.09
% 2.49/1.70  Demodulation         : 0.07
% 2.49/1.70  BG Simplification    : 0.02
% 2.49/1.70  Subsumption          : 0.03
% 2.49/1.71  Abstraction          : 0.02
% 2.49/1.71  MUC search           : 0.00
% 2.49/1.71  Cooper               : 0.00
% 2.49/1.71  Total                : 0.80
% 2.49/1.71  Index Insertion      : 0.00
% 2.49/1.71  Index Deletion       : 0.00
% 2.49/1.71  Index Matching       : 0.00
% 2.49/1.71  BG Taut test         : 0.00
%------------------------------------------------------------------------------

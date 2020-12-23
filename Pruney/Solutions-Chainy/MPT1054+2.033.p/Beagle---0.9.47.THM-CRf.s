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

% Result     : Theorem 1.94s
% Output     : CNFRefutation 1.94s
% Verified   : 
% Statistics : Number of formulae       :   60 (  77 expanded)
%              Number of leaves         :   29 (  39 expanded)
%              Depth                    :    8
%              Number of atoms          :   70 (  92 expanded)
%              Number of equality atoms :   24 (  37 expanded)
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t171_funct_2)).

tff(f_29,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_63,axiom,(
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

tff(f_61,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_57,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(c_30,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_67,plain,(
    ! [A_25,B_26] :
      ( r1_tarski(A_25,B_26)
      | ~ m1_subset_1(A_25,k1_zfmisc_1(B_26)) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_75,plain,(
    r1_tarski('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_67])).

tff(c_26,plain,(
    ! [A_16] : k6_relat_1(A_16) = k6_partfun1(A_16) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_12,plain,(
    ! [A_6] : v1_relat_1(k6_relat_1(A_6)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_33,plain,(
    ! [A_6] : v1_relat_1(k6_partfun1(A_6)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_12])).

tff(c_8,plain,(
    ! [A_5] : k1_relat_1(k6_relat_1(A_5)) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_35,plain,(
    ! [A_5] : k1_relat_1(k6_partfun1(A_5)) = A_5 ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_8])).

tff(c_82,plain,(
    ! [B_29,A_30] :
      ( r1_tarski(k10_relat_1(B_29,A_30),k1_relat_1(B_29))
      | ~ v1_relat_1(B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_85,plain,(
    ! [A_5,A_30] :
      ( r1_tarski(k10_relat_1(k6_partfun1(A_5),A_30),A_5)
      | ~ v1_relat_1(k6_partfun1(A_5)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_35,c_82])).

tff(c_87,plain,(
    ! [A_5,A_30] : r1_tarski(k10_relat_1(k6_partfun1(A_5),A_30),A_5) ),
    inference(demodulation,[status(thm),theory(equality)],[c_33,c_85])).

tff(c_14,plain,(
    ! [A_6] : v1_funct_1(k6_relat_1(A_6)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_32,plain,(
    ! [A_6] : v1_funct_1(k6_partfun1(A_6)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_14])).

tff(c_10,plain,(
    ! [A_5] : k2_relat_1(k6_relat_1(A_5)) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_34,plain,(
    ! [A_5] : k2_relat_1(k6_partfun1(A_5)) = A_5 ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_10])).

tff(c_148,plain,(
    ! [B_38,A_39] :
      ( k9_relat_1(B_38,k10_relat_1(B_38,A_39)) = A_39
      | ~ r1_tarski(A_39,k2_relat_1(B_38))
      | ~ v1_funct_1(B_38)
      | ~ v1_relat_1(B_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_153,plain,(
    ! [A_5,A_39] :
      ( k9_relat_1(k6_partfun1(A_5),k10_relat_1(k6_partfun1(A_5),A_39)) = A_39
      | ~ r1_tarski(A_39,A_5)
      | ~ v1_funct_1(k6_partfun1(A_5))
      | ~ v1_relat_1(k6_partfun1(A_5)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_148])).

tff(c_157,plain,(
    ! [A_40,A_41] :
      ( k9_relat_1(k6_partfun1(A_40),k10_relat_1(k6_partfun1(A_40),A_41)) = A_41
      | ~ r1_tarski(A_41,A_40) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_33,c_32,c_153])).

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

tff(c_89,plain,(
    ! [A_33,B_34] :
      ( k9_relat_1(k6_partfun1(A_33),B_34) = B_34
      | ~ m1_subset_1(B_34,k1_zfmisc_1(A_33)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_18])).

tff(c_100,plain,(
    ! [B_2,A_1] :
      ( k9_relat_1(k6_partfun1(B_2),A_1) = A_1
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(resolution,[status(thm)],[c_4,c_89])).

tff(c_163,plain,(
    ! [A_40,A_41] :
      ( k10_relat_1(k6_partfun1(A_40),A_41) = A_41
      | ~ r1_tarski(k10_relat_1(k6_partfun1(A_40),A_41),A_40)
      | ~ r1_tarski(A_41,A_40) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_157,c_100])).

tff(c_173,plain,(
    ! [A_40,A_41] :
      ( k10_relat_1(k6_partfun1(A_40),A_41) = A_41
      | ~ r1_tarski(A_41,A_40) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_87,c_163])).

tff(c_24,plain,(
    ! [A_15] : m1_subset_1(k6_partfun1(A_15),k1_zfmisc_1(k2_zfmisc_1(A_15,A_15))) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_197,plain,(
    ! [A_44,B_45,C_46,D_47] :
      ( k8_relset_1(A_44,B_45,C_46,D_47) = k10_relat_1(C_46,D_47)
      | ~ m1_subset_1(C_46,k1_zfmisc_1(k2_zfmisc_1(A_44,B_45))) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_203,plain,(
    ! [A_15,D_47] : k8_relset_1(A_15,A_15,k6_partfun1(A_15),D_47) = k10_relat_1(k6_partfun1(A_15),D_47) ),
    inference(resolution,[status(thm)],[c_24,c_197])).

tff(c_28,plain,(
    k8_relset_1('#skF_1','#skF_1',k6_partfun1('#skF_1'),'#skF_2') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_205,plain,(
    k10_relat_1(k6_partfun1('#skF_1'),'#skF_2') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_203,c_28])).

tff(c_217,plain,(
    ~ r1_tarski('#skF_2','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_173,c_205])).

tff(c_221,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_75,c_217])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:25:19 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.94/1.17  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.94/1.18  
% 1.94/1.18  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.94/1.18  %$ v1_partfun1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k9_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_1
% 1.94/1.18  
% 1.94/1.18  %Foreground sorts:
% 1.94/1.18  
% 1.94/1.18  
% 1.94/1.18  %Background operators:
% 1.94/1.18  
% 1.94/1.18  
% 1.94/1.18  %Foreground operators:
% 1.94/1.18  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.94/1.18  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.94/1.18  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 1.94/1.18  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.94/1.18  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.94/1.18  tff('#skF_2', type, '#skF_2': $i).
% 1.94/1.18  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 1.94/1.18  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 1.94/1.18  tff('#skF_1', type, '#skF_1': $i).
% 1.94/1.18  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.94/1.18  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 1.94/1.18  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.94/1.18  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 1.94/1.18  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.94/1.18  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.94/1.18  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 1.94/1.18  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.94/1.18  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.94/1.18  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.94/1.18  
% 1.94/1.19  tff(f_68, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k8_relset_1(A, A, k6_partfun1(A), B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t171_funct_2)).
% 1.94/1.19  tff(f_29, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 1.94/1.19  tff(f_63, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 1.94/1.19  tff(f_41, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc3_funct_1)).
% 1.94/1.19  tff(f_37, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 1.94/1.19  tff(f_33, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k10_relat_1(B, A), k1_relat_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t167_relat_1)).
% 1.94/1.19  tff(f_49, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(A, k2_relat_1(B)) => (k9_relat_1(B, k10_relat_1(B, A)) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t147_funct_1)).
% 1.94/1.19  tff(f_53, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k9_relat_1(k6_relat_1(A), B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t162_funct_1)).
% 1.94/1.19  tff(f_61, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 1.94/1.19  tff(f_57, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 1.94/1.19  tff(c_30, plain, (m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_68])).
% 1.94/1.19  tff(c_67, plain, (![A_25, B_26]: (r1_tarski(A_25, B_26) | ~m1_subset_1(A_25, k1_zfmisc_1(B_26)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.94/1.19  tff(c_75, plain, (r1_tarski('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_30, c_67])).
% 1.94/1.19  tff(c_26, plain, (![A_16]: (k6_relat_1(A_16)=k6_partfun1(A_16))), inference(cnfTransformation, [status(thm)], [f_63])).
% 1.94/1.19  tff(c_12, plain, (![A_6]: (v1_relat_1(k6_relat_1(A_6)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.94/1.19  tff(c_33, plain, (![A_6]: (v1_relat_1(k6_partfun1(A_6)))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_12])).
% 1.94/1.19  tff(c_8, plain, (![A_5]: (k1_relat_1(k6_relat_1(A_5))=A_5)), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.94/1.19  tff(c_35, plain, (![A_5]: (k1_relat_1(k6_partfun1(A_5))=A_5)), inference(demodulation, [status(thm), theory('equality')], [c_26, c_8])).
% 1.94/1.19  tff(c_82, plain, (![B_29, A_30]: (r1_tarski(k10_relat_1(B_29, A_30), k1_relat_1(B_29)) | ~v1_relat_1(B_29))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.94/1.19  tff(c_85, plain, (![A_5, A_30]: (r1_tarski(k10_relat_1(k6_partfun1(A_5), A_30), A_5) | ~v1_relat_1(k6_partfun1(A_5)))), inference(superposition, [status(thm), theory('equality')], [c_35, c_82])).
% 1.94/1.19  tff(c_87, plain, (![A_5, A_30]: (r1_tarski(k10_relat_1(k6_partfun1(A_5), A_30), A_5))), inference(demodulation, [status(thm), theory('equality')], [c_33, c_85])).
% 1.94/1.19  tff(c_14, plain, (![A_6]: (v1_funct_1(k6_relat_1(A_6)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.94/1.19  tff(c_32, plain, (![A_6]: (v1_funct_1(k6_partfun1(A_6)))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_14])).
% 1.94/1.19  tff(c_10, plain, (![A_5]: (k2_relat_1(k6_relat_1(A_5))=A_5)), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.94/1.19  tff(c_34, plain, (![A_5]: (k2_relat_1(k6_partfun1(A_5))=A_5)), inference(demodulation, [status(thm), theory('equality')], [c_26, c_10])).
% 1.94/1.19  tff(c_148, plain, (![B_38, A_39]: (k9_relat_1(B_38, k10_relat_1(B_38, A_39))=A_39 | ~r1_tarski(A_39, k2_relat_1(B_38)) | ~v1_funct_1(B_38) | ~v1_relat_1(B_38))), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.94/1.19  tff(c_153, plain, (![A_5, A_39]: (k9_relat_1(k6_partfun1(A_5), k10_relat_1(k6_partfun1(A_5), A_39))=A_39 | ~r1_tarski(A_39, A_5) | ~v1_funct_1(k6_partfun1(A_5)) | ~v1_relat_1(k6_partfun1(A_5)))), inference(superposition, [status(thm), theory('equality')], [c_34, c_148])).
% 1.94/1.19  tff(c_157, plain, (![A_40, A_41]: (k9_relat_1(k6_partfun1(A_40), k10_relat_1(k6_partfun1(A_40), A_41))=A_41 | ~r1_tarski(A_41, A_40))), inference(demodulation, [status(thm), theory('equality')], [c_33, c_32, c_153])).
% 1.94/1.19  tff(c_4, plain, (![A_1, B_2]: (m1_subset_1(A_1, k1_zfmisc_1(B_2)) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.94/1.19  tff(c_18, plain, (![A_9, B_10]: (k9_relat_1(k6_relat_1(A_9), B_10)=B_10 | ~m1_subset_1(B_10, k1_zfmisc_1(A_9)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.94/1.19  tff(c_89, plain, (![A_33, B_34]: (k9_relat_1(k6_partfun1(A_33), B_34)=B_34 | ~m1_subset_1(B_34, k1_zfmisc_1(A_33)))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_18])).
% 1.94/1.19  tff(c_100, plain, (![B_2, A_1]: (k9_relat_1(k6_partfun1(B_2), A_1)=A_1 | ~r1_tarski(A_1, B_2))), inference(resolution, [status(thm)], [c_4, c_89])).
% 1.94/1.19  tff(c_163, plain, (![A_40, A_41]: (k10_relat_1(k6_partfun1(A_40), A_41)=A_41 | ~r1_tarski(k10_relat_1(k6_partfun1(A_40), A_41), A_40) | ~r1_tarski(A_41, A_40))), inference(superposition, [status(thm), theory('equality')], [c_157, c_100])).
% 1.94/1.19  tff(c_173, plain, (![A_40, A_41]: (k10_relat_1(k6_partfun1(A_40), A_41)=A_41 | ~r1_tarski(A_41, A_40))), inference(demodulation, [status(thm), theory('equality')], [c_87, c_163])).
% 1.94/1.19  tff(c_24, plain, (![A_15]: (m1_subset_1(k6_partfun1(A_15), k1_zfmisc_1(k2_zfmisc_1(A_15, A_15))))), inference(cnfTransformation, [status(thm)], [f_61])).
% 1.94/1.19  tff(c_197, plain, (![A_44, B_45, C_46, D_47]: (k8_relset_1(A_44, B_45, C_46, D_47)=k10_relat_1(C_46, D_47) | ~m1_subset_1(C_46, k1_zfmisc_1(k2_zfmisc_1(A_44, B_45))))), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.94/1.19  tff(c_203, plain, (![A_15, D_47]: (k8_relset_1(A_15, A_15, k6_partfun1(A_15), D_47)=k10_relat_1(k6_partfun1(A_15), D_47))), inference(resolution, [status(thm)], [c_24, c_197])).
% 1.94/1.19  tff(c_28, plain, (k8_relset_1('#skF_1', '#skF_1', k6_partfun1('#skF_1'), '#skF_2')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_68])).
% 1.94/1.19  tff(c_205, plain, (k10_relat_1(k6_partfun1('#skF_1'), '#skF_2')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_203, c_28])).
% 1.94/1.19  tff(c_217, plain, (~r1_tarski('#skF_2', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_173, c_205])).
% 1.94/1.19  tff(c_221, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_75, c_217])).
% 1.94/1.19  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.94/1.19  
% 1.94/1.19  Inference rules
% 1.94/1.19  ----------------------
% 1.94/1.19  #Ref     : 0
% 1.94/1.19  #Sup     : 39
% 1.94/1.19  #Fact    : 0
% 1.94/1.19  #Define  : 0
% 1.94/1.19  #Split   : 0
% 1.94/1.19  #Chain   : 0
% 1.94/1.19  #Close   : 0
% 1.94/1.19  
% 1.94/1.19  Ordering : KBO
% 1.94/1.19  
% 1.94/1.19  Simplification rules
% 1.94/1.19  ----------------------
% 1.94/1.19  #Subsume      : 2
% 1.94/1.19  #Demod        : 18
% 1.94/1.19  #Tautology    : 25
% 1.94/1.19  #SimpNegUnit  : 0
% 1.94/1.19  #BackRed      : 1
% 1.94/1.19  
% 1.94/1.19  #Partial instantiations: 0
% 1.94/1.19  #Strategies tried      : 1
% 1.94/1.19  
% 1.94/1.19  Timing (in seconds)
% 1.94/1.19  ----------------------
% 1.94/1.20  Preprocessing        : 0.30
% 1.94/1.20  Parsing              : 0.16
% 1.94/1.20  CNF conversion       : 0.02
% 1.94/1.20  Main loop            : 0.15
% 1.94/1.20  Inferencing          : 0.06
% 1.94/1.20  Reduction            : 0.05
% 1.94/1.20  Demodulation         : 0.03
% 1.94/1.20  BG Simplification    : 0.01
% 1.94/1.20  Subsumption          : 0.02
% 1.94/1.20  Abstraction          : 0.01
% 1.94/1.20  MUC search           : 0.00
% 1.94/1.20  Cooper               : 0.00
% 1.94/1.20  Total                : 0.47
% 1.94/1.20  Index Insertion      : 0.00
% 1.94/1.20  Index Deletion       : 0.00
% 1.94/1.20  Index Matching       : 0.00
% 1.94/1.20  BG Taut test         : 0.00
%------------------------------------------------------------------------------

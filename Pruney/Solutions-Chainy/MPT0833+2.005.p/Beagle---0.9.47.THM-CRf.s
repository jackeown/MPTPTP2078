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
% DateTime   : Thu Dec  3 10:07:45 EST 2020

% Result     : Theorem 2.10s
% Output     : CNFRefutation 2.15s
% Verified   : 
% Statistics : Number of formulae       :   48 (  78 expanded)
%              Number of leaves         :   26 (  39 expanded)
%              Depth                    :    8
%              Number of atoms          :   61 ( 125 expanded)
%              Number of equality atoms :   14 (  19 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k6_relset_1 > k8_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k8_relat_1,type,(
    k8_relat_1: ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_relset_1,type,(
    r2_relset_1: ( $i * $i * $i * $i ) > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k6_relset_1,type,(
    k6_relset_1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_72,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B)))
       => ( r1_tarski(B,C)
         => r2_relset_1(A,B,k6_relset_1(A,B,C,D),D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_relset_1)).

tff(f_65,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k2_relat_1(B),A)
       => k8_relat_1(A,B) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_relat_1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_tarski(A,B)
       => k8_relat_1(B,k8_relat_1(A,C)) = k8_relat_1(A,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t129_relat_1)).

tff(f_57,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k6_relset_1(A,B,C,D) = k8_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_relset_1)).

tff(c_26,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_64,plain,(
    ! [A_39,B_40,D_41] :
      ( r2_relset_1(A_39,B_40,D_41,D_41)
      | ~ m1_subset_1(D_41,k1_zfmisc_1(k2_zfmisc_1(A_39,B_40))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_67,plain,(
    r2_relset_1('#skF_1','#skF_2','#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_26,c_64])).

tff(c_24,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_27,plain,(
    ! [C_22,A_23,B_24] :
      ( v1_relat_1(C_22)
      | ~ m1_subset_1(C_22,k1_zfmisc_1(k2_zfmisc_1(A_23,B_24))) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_31,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_26,c_27])).

tff(c_33,plain,(
    ! [C_27,B_28,A_29] :
      ( v5_relat_1(C_27,B_28)
      | ~ m1_subset_1(C_27,k1_zfmisc_1(k2_zfmisc_1(A_29,B_28))) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_37,plain,(
    v5_relat_1('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_26,c_33])).

tff(c_4,plain,(
    ! [B_2,A_1] :
      ( r1_tarski(k2_relat_1(B_2),A_1)
      | ~ v5_relat_1(B_2,A_1)
      | ~ v1_relat_1(B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_48,plain,(
    ! [A_35,B_36] :
      ( k8_relat_1(A_35,B_36) = B_36
      | ~ r1_tarski(k2_relat_1(B_36),A_35)
      | ~ v1_relat_1(B_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_53,plain,(
    ! [A_37,B_38] :
      ( k8_relat_1(A_37,B_38) = B_38
      | ~ v5_relat_1(B_38,A_37)
      | ~ v1_relat_1(B_38) ) ),
    inference(resolution,[status(thm)],[c_4,c_48])).

tff(c_56,plain,
    ( k8_relat_1('#skF_2','#skF_4') = '#skF_4'
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_37,c_53])).

tff(c_59,plain,(
    k8_relat_1('#skF_2','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_31,c_56])).

tff(c_68,plain,(
    ! [B_42,A_43,C_44] :
      ( k8_relat_1(B_42,k8_relat_1(A_43,C_44)) = k8_relat_1(A_43,C_44)
      | ~ r1_tarski(A_43,B_42)
      | ~ v1_relat_1(C_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_83,plain,(
    ! [B_42] :
      ( k8_relat_1(B_42,'#skF_4') = k8_relat_1('#skF_2','#skF_4')
      | ~ r1_tarski('#skF_2',B_42)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_59,c_68])).

tff(c_88,plain,(
    ! [B_45] :
      ( k8_relat_1(B_45,'#skF_4') = '#skF_4'
      | ~ r1_tarski('#skF_2',B_45) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_31,c_59,c_83])).

tff(c_92,plain,(
    k8_relat_1('#skF_3','#skF_4') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_24,c_88])).

tff(c_103,plain,(
    ! [A_47,B_48,C_49,D_50] :
      ( k6_relset_1(A_47,B_48,C_49,D_50) = k8_relat_1(C_49,D_50)
      | ~ m1_subset_1(D_50,k1_zfmisc_1(k2_zfmisc_1(A_47,B_48))) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_106,plain,(
    ! [C_49] : k6_relset_1('#skF_1','#skF_2',C_49,'#skF_4') = k8_relat_1(C_49,'#skF_4') ),
    inference(resolution,[status(thm)],[c_26,c_103])).

tff(c_22,plain,(
    ~ r2_relset_1('#skF_1','#skF_2',k6_relset_1('#skF_1','#skF_2','#skF_3','#skF_4'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_107,plain,(
    ~ r2_relset_1('#skF_1','#skF_2',k8_relat_1('#skF_3','#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_22])).

tff(c_110,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_67,c_92,c_107])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n016.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:33:34 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.10/1.18  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.10/1.19  
% 2.10/1.19  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.10/1.19  %$ r2_relset_1 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k6_relset_1 > k8_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.10/1.19  
% 2.10/1.19  %Foreground sorts:
% 2.10/1.19  
% 2.10/1.19  
% 2.10/1.19  %Background operators:
% 2.10/1.19  
% 2.10/1.19  
% 2.10/1.19  %Foreground operators:
% 2.10/1.19  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 2.10/1.19  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.10/1.19  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 2.10/1.19  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.10/1.19  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.10/1.19  tff(k6_relset_1, type, k6_relset_1: ($i * $i * $i * $i) > $i).
% 2.10/1.19  tff('#skF_2', type, '#skF_2': $i).
% 2.10/1.19  tff('#skF_3', type, '#skF_3': $i).
% 2.10/1.19  tff('#skF_1', type, '#skF_1': $i).
% 2.10/1.19  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.10/1.19  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.10/1.19  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.10/1.19  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.10/1.19  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.10/1.19  tff('#skF_4', type, '#skF_4': $i).
% 2.10/1.19  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.10/1.19  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.10/1.19  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.10/1.19  
% 2.15/1.20  tff(f_72, negated_conjecture, ~(![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (r1_tarski(B, C) => r2_relset_1(A, B, k6_relset_1(A, B, C, D), D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_relset_1)).
% 2.15/1.20  tff(f_65, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 2.15/1.20  tff(f_47, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.15/1.20  tff(f_53, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.15/1.20  tff(f_31, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 2.15/1.20  tff(f_37, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k8_relat_1(A, B) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t125_relat_1)).
% 2.15/1.20  tff(f_43, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => (k8_relat_1(B, k8_relat_1(A, C)) = k8_relat_1(A, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t129_relat_1)).
% 2.15/1.20  tff(f_57, axiom, (![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k6_relset_1(A, B, C, D) = k8_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_relset_1)).
% 2.15/1.20  tff(c_26, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.15/1.20  tff(c_64, plain, (![A_39, B_40, D_41]: (r2_relset_1(A_39, B_40, D_41, D_41) | ~m1_subset_1(D_41, k1_zfmisc_1(k2_zfmisc_1(A_39, B_40))))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.15/1.20  tff(c_67, plain, (r2_relset_1('#skF_1', '#skF_2', '#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_26, c_64])).
% 2.15/1.20  tff(c_24, plain, (r1_tarski('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.15/1.20  tff(c_27, plain, (![C_22, A_23, B_24]: (v1_relat_1(C_22) | ~m1_subset_1(C_22, k1_zfmisc_1(k2_zfmisc_1(A_23, B_24))))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.15/1.20  tff(c_31, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_26, c_27])).
% 2.15/1.20  tff(c_33, plain, (![C_27, B_28, A_29]: (v5_relat_1(C_27, B_28) | ~m1_subset_1(C_27, k1_zfmisc_1(k2_zfmisc_1(A_29, B_28))))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.15/1.20  tff(c_37, plain, (v5_relat_1('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_26, c_33])).
% 2.15/1.20  tff(c_4, plain, (![B_2, A_1]: (r1_tarski(k2_relat_1(B_2), A_1) | ~v5_relat_1(B_2, A_1) | ~v1_relat_1(B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.15/1.20  tff(c_48, plain, (![A_35, B_36]: (k8_relat_1(A_35, B_36)=B_36 | ~r1_tarski(k2_relat_1(B_36), A_35) | ~v1_relat_1(B_36))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.15/1.20  tff(c_53, plain, (![A_37, B_38]: (k8_relat_1(A_37, B_38)=B_38 | ~v5_relat_1(B_38, A_37) | ~v1_relat_1(B_38))), inference(resolution, [status(thm)], [c_4, c_48])).
% 2.15/1.20  tff(c_56, plain, (k8_relat_1('#skF_2', '#skF_4')='#skF_4' | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_37, c_53])).
% 2.15/1.20  tff(c_59, plain, (k8_relat_1('#skF_2', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_31, c_56])).
% 2.15/1.20  tff(c_68, plain, (![B_42, A_43, C_44]: (k8_relat_1(B_42, k8_relat_1(A_43, C_44))=k8_relat_1(A_43, C_44) | ~r1_tarski(A_43, B_42) | ~v1_relat_1(C_44))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.15/1.20  tff(c_83, plain, (![B_42]: (k8_relat_1(B_42, '#skF_4')=k8_relat_1('#skF_2', '#skF_4') | ~r1_tarski('#skF_2', B_42) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_59, c_68])).
% 2.15/1.20  tff(c_88, plain, (![B_45]: (k8_relat_1(B_45, '#skF_4')='#skF_4' | ~r1_tarski('#skF_2', B_45))), inference(demodulation, [status(thm), theory('equality')], [c_31, c_59, c_83])).
% 2.15/1.20  tff(c_92, plain, (k8_relat_1('#skF_3', '#skF_4')='#skF_4'), inference(resolution, [status(thm)], [c_24, c_88])).
% 2.15/1.20  tff(c_103, plain, (![A_47, B_48, C_49, D_50]: (k6_relset_1(A_47, B_48, C_49, D_50)=k8_relat_1(C_49, D_50) | ~m1_subset_1(D_50, k1_zfmisc_1(k2_zfmisc_1(A_47, B_48))))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.15/1.20  tff(c_106, plain, (![C_49]: (k6_relset_1('#skF_1', '#skF_2', C_49, '#skF_4')=k8_relat_1(C_49, '#skF_4'))), inference(resolution, [status(thm)], [c_26, c_103])).
% 2.15/1.20  tff(c_22, plain, (~r2_relset_1('#skF_1', '#skF_2', k6_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.15/1.20  tff(c_107, plain, (~r2_relset_1('#skF_1', '#skF_2', k8_relat_1('#skF_3', '#skF_4'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_106, c_22])).
% 2.15/1.20  tff(c_110, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_67, c_92, c_107])).
% 2.15/1.20  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.15/1.20  
% 2.15/1.20  Inference rules
% 2.15/1.20  ----------------------
% 2.15/1.20  #Ref     : 0
% 2.15/1.20  #Sup     : 19
% 2.15/1.20  #Fact    : 0
% 2.15/1.20  #Define  : 0
% 2.15/1.20  #Split   : 0
% 2.15/1.20  #Chain   : 0
% 2.15/1.20  #Close   : 0
% 2.15/1.20  
% 2.15/1.20  Ordering : KBO
% 2.15/1.20  
% 2.15/1.20  Simplification rules
% 2.15/1.20  ----------------------
% 2.15/1.20  #Subsume      : 0
% 2.15/1.20  #Demod        : 8
% 2.15/1.20  #Tautology    : 7
% 2.15/1.20  #SimpNegUnit  : 0
% 2.15/1.20  #BackRed      : 1
% 2.15/1.20  
% 2.15/1.20  #Partial instantiations: 0
% 2.15/1.20  #Strategies tried      : 1
% 2.15/1.20  
% 2.15/1.20  Timing (in seconds)
% 2.15/1.20  ----------------------
% 2.15/1.20  Preprocessing        : 0.31
% 2.15/1.20  Parsing              : 0.17
% 2.15/1.20  CNF conversion       : 0.02
% 2.15/1.20  Main loop            : 0.12
% 2.15/1.20  Inferencing          : 0.05
% 2.15/1.20  Reduction            : 0.04
% 2.15/1.20  Demodulation         : 0.03
% 2.15/1.20  BG Simplification    : 0.01
% 2.15/1.20  Subsumption          : 0.02
% 2.15/1.20  Abstraction          : 0.01
% 2.15/1.20  MUC search           : 0.00
% 2.15/1.21  Cooper               : 0.00
% 2.15/1.21  Total                : 0.46
% 2.15/1.21  Index Insertion      : 0.00
% 2.15/1.21  Index Deletion       : 0.00
% 2.15/1.21  Index Matching       : 0.00
% 2.15/1.21  BG Taut test         : 0.00
%------------------------------------------------------------------------------

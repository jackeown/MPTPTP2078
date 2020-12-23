%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:07:46 EST 2020

% Result     : Theorem 1.88s
% Output     : CNFRefutation 1.96s
% Verified   : 
% Statistics : Number of formulae       :   50 (  82 expanded)
%              Number of leaves         :   26 (  40 expanded)
%              Depth                    :    9
%              Number of atoms          :   64 ( 132 expanded)
%              Number of equality atoms :   13 (  18 expanded)
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

tff(f_70,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B)))
       => ( r1_tarski(B,C)
         => r2_relset_1(A,B,k6_relset_1(A,B,C,D),D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_relset_1)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k2_relat_1(B),A)
       => k8_relat_1(A,B) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t125_relat_1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_tarski(A,B)
       => k8_relat_1(B,k8_relat_1(A,C)) = k8_relat_1(A,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t129_relat_1)).

tff(f_57,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k6_relset_1(A,B,C,D) = k8_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_relset_1)).

tff(f_63,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => r2_relset_1(A,B,C,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).

tff(c_22,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_24,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_25,plain,(
    ! [C_22,A_23,B_24] :
      ( v1_relat_1(C_22)
      | ~ m1_subset_1(C_22,k1_zfmisc_1(k2_zfmisc_1(A_23,B_24))) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_29,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_24,c_25])).

tff(c_41,plain,(
    ! [C_32,B_33,A_34] :
      ( v5_relat_1(C_32,B_33)
      | ~ m1_subset_1(C_32,k1_zfmisc_1(k2_zfmisc_1(A_34,B_33))) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_45,plain,(
    v5_relat_1('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_24,c_41])).

tff(c_4,plain,(
    ! [B_2,A_1] :
      ( r1_tarski(k2_relat_1(B_2),A_1)
      | ~ v5_relat_1(B_2,A_1)
      | ~ v1_relat_1(B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_46,plain,(
    ! [A_35,B_36] :
      ( k8_relat_1(A_35,B_36) = B_36
      | ~ r1_tarski(k2_relat_1(B_36),A_35)
      | ~ v1_relat_1(B_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_51,plain,(
    ! [A_37,B_38] :
      ( k8_relat_1(A_37,B_38) = B_38
      | ~ v5_relat_1(B_38,A_37)
      | ~ v1_relat_1(B_38) ) ),
    inference(resolution,[status(thm)],[c_4,c_46])).

tff(c_54,plain,
    ( k8_relat_1('#skF_2','#skF_4') = '#skF_4'
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_45,c_51])).

tff(c_57,plain,(
    k8_relat_1('#skF_2','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_29,c_54])).

tff(c_62,plain,(
    ! [B_39,A_40,C_41] :
      ( k8_relat_1(B_39,k8_relat_1(A_40,C_41)) = k8_relat_1(A_40,C_41)
      | ~ r1_tarski(A_40,B_39)
      | ~ v1_relat_1(C_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_77,plain,(
    ! [B_39] :
      ( k8_relat_1(B_39,'#skF_4') = k8_relat_1('#skF_2','#skF_4')
      | ~ r1_tarski('#skF_2',B_39)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_57,c_62])).

tff(c_86,plain,(
    ! [B_46] :
      ( k8_relat_1(B_46,'#skF_4') = '#skF_4'
      | ~ r1_tarski('#skF_2',B_46) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_29,c_57,c_77])).

tff(c_90,plain,(
    k8_relat_1('#skF_3','#skF_4') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_22,c_86])).

tff(c_82,plain,(
    ! [A_42,B_43,C_44,D_45] :
      ( k6_relset_1(A_42,B_43,C_44,D_45) = k8_relat_1(C_44,D_45)
      | ~ m1_subset_1(D_45,k1_zfmisc_1(k2_zfmisc_1(A_42,B_43))) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_85,plain,(
    ! [C_44] : k6_relset_1('#skF_1','#skF_2',C_44,'#skF_4') = k8_relat_1(C_44,'#skF_4') ),
    inference(resolution,[status(thm)],[c_24,c_82])).

tff(c_20,plain,(
    ~ r2_relset_1('#skF_1','#skF_2',k6_relset_1('#skF_1','#skF_2','#skF_3','#skF_4'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_101,plain,(
    ~ r2_relset_1('#skF_1','#skF_2',k8_relat_1('#skF_3','#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_20])).

tff(c_102,plain,(
    ~ r2_relset_1('#skF_1','#skF_2','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_101])).

tff(c_112,plain,(
    ! [A_49,B_50,C_51,D_52] :
      ( r2_relset_1(A_49,B_50,C_51,C_51)
      | ~ m1_subset_1(D_52,k1_zfmisc_1(k2_zfmisc_1(A_49,B_50)))
      | ~ m1_subset_1(C_51,k1_zfmisc_1(k2_zfmisc_1(A_49,B_50))) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_116,plain,(
    ! [C_53] :
      ( r2_relset_1('#skF_1','#skF_2',C_53,C_53)
      | ~ m1_subset_1(C_53,k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ) ),
    inference(resolution,[status(thm)],[c_24,c_112])).

tff(c_118,plain,(
    r2_relset_1('#skF_1','#skF_2','#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_24,c_116])).

tff(c_122,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_102,c_118])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:43:09 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.88/1.20  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.88/1.21  
% 1.88/1.21  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.88/1.21  %$ r2_relset_1 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k6_relset_1 > k8_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 1.88/1.21  
% 1.88/1.21  %Foreground sorts:
% 1.88/1.21  
% 1.88/1.21  
% 1.88/1.21  %Background operators:
% 1.88/1.21  
% 1.88/1.21  
% 1.88/1.21  %Foreground operators:
% 1.88/1.21  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 1.88/1.21  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.88/1.21  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 1.88/1.21  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.88/1.21  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.88/1.21  tff(k6_relset_1, type, k6_relset_1: ($i * $i * $i * $i) > $i).
% 1.88/1.21  tff('#skF_2', type, '#skF_2': $i).
% 1.88/1.21  tff('#skF_3', type, '#skF_3': $i).
% 1.88/1.21  tff('#skF_1', type, '#skF_1': $i).
% 1.88/1.21  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 1.88/1.21  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.88/1.21  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.88/1.21  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.88/1.21  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.88/1.21  tff('#skF_4', type, '#skF_4': $i).
% 1.88/1.21  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.88/1.21  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 1.88/1.21  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.88/1.21  
% 1.96/1.22  tff(f_70, negated_conjecture, ~(![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (r1_tarski(B, C) => r2_relset_1(A, B, k6_relset_1(A, B, C, D), D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_relset_1)).
% 1.96/1.22  tff(f_47, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 1.96/1.22  tff(f_53, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 1.96/1.22  tff(f_31, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 1.96/1.22  tff(f_37, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k8_relat_1(A, B) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t125_relat_1)).
% 1.96/1.22  tff(f_43, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => (k8_relat_1(B, k8_relat_1(A, C)) = k8_relat_1(A, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t129_relat_1)).
% 1.96/1.22  tff(f_57, axiom, (![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k6_relset_1(A, B, C, D) = k8_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_relset_1)).
% 1.96/1.22  tff(f_63, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => r2_relset_1(A, B, C, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', reflexivity_r2_relset_1)).
% 1.96/1.22  tff(c_22, plain, (r1_tarski('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_70])).
% 1.96/1.22  tff(c_24, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_70])).
% 1.96/1.22  tff(c_25, plain, (![C_22, A_23, B_24]: (v1_relat_1(C_22) | ~m1_subset_1(C_22, k1_zfmisc_1(k2_zfmisc_1(A_23, B_24))))), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.96/1.22  tff(c_29, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_24, c_25])).
% 1.96/1.22  tff(c_41, plain, (![C_32, B_33, A_34]: (v5_relat_1(C_32, B_33) | ~m1_subset_1(C_32, k1_zfmisc_1(k2_zfmisc_1(A_34, B_33))))), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.96/1.22  tff(c_45, plain, (v5_relat_1('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_24, c_41])).
% 1.96/1.22  tff(c_4, plain, (![B_2, A_1]: (r1_tarski(k2_relat_1(B_2), A_1) | ~v5_relat_1(B_2, A_1) | ~v1_relat_1(B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.96/1.22  tff(c_46, plain, (![A_35, B_36]: (k8_relat_1(A_35, B_36)=B_36 | ~r1_tarski(k2_relat_1(B_36), A_35) | ~v1_relat_1(B_36))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.96/1.22  tff(c_51, plain, (![A_37, B_38]: (k8_relat_1(A_37, B_38)=B_38 | ~v5_relat_1(B_38, A_37) | ~v1_relat_1(B_38))), inference(resolution, [status(thm)], [c_4, c_46])).
% 1.96/1.22  tff(c_54, plain, (k8_relat_1('#skF_2', '#skF_4')='#skF_4' | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_45, c_51])).
% 1.96/1.22  tff(c_57, plain, (k8_relat_1('#skF_2', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_29, c_54])).
% 1.96/1.22  tff(c_62, plain, (![B_39, A_40, C_41]: (k8_relat_1(B_39, k8_relat_1(A_40, C_41))=k8_relat_1(A_40, C_41) | ~r1_tarski(A_40, B_39) | ~v1_relat_1(C_41))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.96/1.22  tff(c_77, plain, (![B_39]: (k8_relat_1(B_39, '#skF_4')=k8_relat_1('#skF_2', '#skF_4') | ~r1_tarski('#skF_2', B_39) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_57, c_62])).
% 1.96/1.22  tff(c_86, plain, (![B_46]: (k8_relat_1(B_46, '#skF_4')='#skF_4' | ~r1_tarski('#skF_2', B_46))), inference(demodulation, [status(thm), theory('equality')], [c_29, c_57, c_77])).
% 1.96/1.22  tff(c_90, plain, (k8_relat_1('#skF_3', '#skF_4')='#skF_4'), inference(resolution, [status(thm)], [c_22, c_86])).
% 1.96/1.22  tff(c_82, plain, (![A_42, B_43, C_44, D_45]: (k6_relset_1(A_42, B_43, C_44, D_45)=k8_relat_1(C_44, D_45) | ~m1_subset_1(D_45, k1_zfmisc_1(k2_zfmisc_1(A_42, B_43))))), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.96/1.22  tff(c_85, plain, (![C_44]: (k6_relset_1('#skF_1', '#skF_2', C_44, '#skF_4')=k8_relat_1(C_44, '#skF_4'))), inference(resolution, [status(thm)], [c_24, c_82])).
% 1.96/1.22  tff(c_20, plain, (~r2_relset_1('#skF_1', '#skF_2', k6_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_70])).
% 1.96/1.22  tff(c_101, plain, (~r2_relset_1('#skF_1', '#skF_2', k8_relat_1('#skF_3', '#skF_4'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_85, c_20])).
% 1.96/1.22  tff(c_102, plain, (~r2_relset_1('#skF_1', '#skF_2', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_90, c_101])).
% 1.96/1.22  tff(c_112, plain, (![A_49, B_50, C_51, D_52]: (r2_relset_1(A_49, B_50, C_51, C_51) | ~m1_subset_1(D_52, k1_zfmisc_1(k2_zfmisc_1(A_49, B_50))) | ~m1_subset_1(C_51, k1_zfmisc_1(k2_zfmisc_1(A_49, B_50))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 1.96/1.22  tff(c_116, plain, (![C_53]: (r2_relset_1('#skF_1', '#skF_2', C_53, C_53) | ~m1_subset_1(C_53, k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))))), inference(resolution, [status(thm)], [c_24, c_112])).
% 1.96/1.22  tff(c_118, plain, (r2_relset_1('#skF_1', '#skF_2', '#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_24, c_116])).
% 1.96/1.22  tff(c_122, plain, $false, inference(negUnitSimplification, [status(thm)], [c_102, c_118])).
% 1.96/1.22  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.96/1.22  
% 1.96/1.22  Inference rules
% 1.96/1.22  ----------------------
% 1.96/1.22  #Ref     : 0
% 1.96/1.22  #Sup     : 22
% 1.96/1.22  #Fact    : 0
% 1.96/1.22  #Define  : 0
% 1.96/1.22  #Split   : 0
% 1.96/1.22  #Chain   : 0
% 1.96/1.22  #Close   : 0
% 1.96/1.22  
% 1.96/1.22  Ordering : KBO
% 1.96/1.22  
% 1.96/1.22  Simplification rules
% 1.96/1.22  ----------------------
% 1.96/1.22  #Subsume      : 0
% 1.96/1.22  #Demod        : 7
% 1.96/1.22  #Tautology    : 9
% 1.96/1.22  #SimpNegUnit  : 1
% 1.96/1.22  #BackRed      : 1
% 1.96/1.22  
% 1.96/1.22  #Partial instantiations: 0
% 1.96/1.22  #Strategies tried      : 1
% 1.96/1.22  
% 1.96/1.22  Timing (in seconds)
% 1.96/1.22  ----------------------
% 1.96/1.23  Preprocessing        : 0.31
% 1.96/1.23  Parsing              : 0.16
% 1.96/1.23  CNF conversion       : 0.02
% 1.96/1.23  Main loop            : 0.14
% 1.96/1.23  Inferencing          : 0.06
% 1.96/1.23  Reduction            : 0.05
% 1.96/1.23  Demodulation         : 0.04
% 1.96/1.23  BG Simplification    : 0.01
% 1.96/1.23  Subsumption          : 0.02
% 1.96/1.23  Abstraction          : 0.01
% 1.96/1.23  MUC search           : 0.00
% 1.96/1.23  Cooper               : 0.00
% 1.96/1.23  Total                : 0.48
% 1.96/1.23  Index Insertion      : 0.00
% 1.96/1.23  Index Deletion       : 0.00
% 1.96/1.23  Index Matching       : 0.00
% 1.96/1.23  BG Taut test         : 0.00
%------------------------------------------------------------------------------

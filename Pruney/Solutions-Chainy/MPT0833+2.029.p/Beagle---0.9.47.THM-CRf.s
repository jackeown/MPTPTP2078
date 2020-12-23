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
% DateTime   : Thu Dec  3 10:07:49 EST 2020

% Result     : Theorem 2.10s
% Output     : CNFRefutation 2.10s
% Verified   : 
% Statistics : Number of formulae       :   56 ( 102 expanded)
%              Number of leaves         :   27 (  46 expanded)
%              Depth                    :   12
%              Number of atoms          :   72 ( 162 expanded)
%              Number of equality atoms :   15 (  22 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k6_relset_1 > k2_relset_1 > k8_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

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

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_75,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B)))
       => ( r1_tarski(B,C)
         => r2_relset_1(A,B,k6_relset_1(A,B,C,D),D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_relset_1)).

tff(f_38,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_36,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_58,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_54,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k2_relset_1(A,B,C),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_relset_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_44,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k2_relat_1(B),A)
       => k8_relat_1(A,B) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t125_relat_1)).

tff(f_50,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_tarski(A,B)
       => k8_relat_1(B,k8_relat_1(A,C)) = k8_relat_1(A,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t129_relat_1)).

tff(f_62,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k6_relset_1(A,B,C,D) = k8_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_relset_1)).

tff(f_68,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => r2_relset_1(A,B,C,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).

tff(c_24,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_8,plain,(
    ! [A_6,B_7] : v1_relat_1(k2_zfmisc_1(A_6,B_7)) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_26,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_38,plain,(
    ! [B_33,A_34] :
      ( v1_relat_1(B_33)
      | ~ m1_subset_1(B_33,k1_zfmisc_1(A_34))
      | ~ v1_relat_1(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_44,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_26,c_38])).

tff(c_48,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_44])).

tff(c_62,plain,(
    ! [A_39,B_40,C_41] :
      ( k2_relset_1(A_39,B_40,C_41) = k2_relat_1(C_41)
      | ~ m1_subset_1(C_41,k1_zfmisc_1(k2_zfmisc_1(A_39,B_40))) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_71,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_26,c_62])).

tff(c_76,plain,(
    ! [A_42,B_43,C_44] :
      ( m1_subset_1(k2_relset_1(A_42,B_43,C_44),k1_zfmisc_1(B_43))
      | ~ m1_subset_1(C_44,k1_zfmisc_1(k2_zfmisc_1(A_42,B_43))) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_89,plain,
    ( m1_subset_1(k2_relat_1('#skF_4'),k1_zfmisc_1('#skF_2'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_71,c_76])).

tff(c_94,plain,(
    m1_subset_1(k2_relat_1('#skF_4'),k1_zfmisc_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_89])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( r1_tarski(A_1,B_2)
      | ~ m1_subset_1(A_1,k1_zfmisc_1(B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_102,plain,(
    r1_tarski(k2_relat_1('#skF_4'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_94,c_2])).

tff(c_10,plain,(
    ! [A_8,B_9] :
      ( k8_relat_1(A_8,B_9) = B_9
      | ~ r1_tarski(k2_relat_1(B_9),A_8)
      | ~ v1_relat_1(B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_105,plain,
    ( k8_relat_1('#skF_2','#skF_4') = '#skF_4'
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_102,c_10])).

tff(c_111,plain,(
    k8_relat_1('#skF_2','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_105])).

tff(c_152,plain,(
    ! [B_54,A_55,C_56] :
      ( k8_relat_1(B_54,k8_relat_1(A_55,C_56)) = k8_relat_1(A_55,C_56)
      | ~ r1_tarski(A_55,B_54)
      | ~ v1_relat_1(C_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_167,plain,(
    ! [B_54] :
      ( k8_relat_1(B_54,'#skF_4') = k8_relat_1('#skF_2','#skF_4')
      | ~ r1_tarski('#skF_2',B_54)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_111,c_152])).

tff(c_172,plain,(
    ! [B_57] :
      ( k8_relat_1(B_57,'#skF_4') = '#skF_4'
      | ~ r1_tarski('#skF_2',B_57) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_111,c_167])).

tff(c_176,plain,(
    k8_relat_1('#skF_3','#skF_4') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_24,c_172])).

tff(c_187,plain,(
    ! [A_59,B_60,C_61,D_62] :
      ( k6_relset_1(A_59,B_60,C_61,D_62) = k8_relat_1(C_61,D_62)
      | ~ m1_subset_1(D_62,k1_zfmisc_1(k2_zfmisc_1(A_59,B_60))) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_198,plain,(
    ! [C_61] : k6_relset_1('#skF_1','#skF_2',C_61,'#skF_4') = k8_relat_1(C_61,'#skF_4') ),
    inference(resolution,[status(thm)],[c_26,c_187])).

tff(c_22,plain,(
    ~ r2_relset_1('#skF_1','#skF_2',k6_relset_1('#skF_1','#skF_2','#skF_3','#skF_4'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_199,plain,(
    ~ r2_relset_1('#skF_1','#skF_2',k8_relat_1('#skF_3','#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_198,c_22])).

tff(c_200,plain,(
    ~ r2_relset_1('#skF_1','#skF_2','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_176,c_199])).

tff(c_246,plain,(
    ! [A_74,B_75,C_76,D_77] :
      ( r2_relset_1(A_74,B_75,C_76,C_76)
      | ~ m1_subset_1(D_77,k1_zfmisc_1(k2_zfmisc_1(A_74,B_75)))
      | ~ m1_subset_1(C_76,k1_zfmisc_1(k2_zfmisc_1(A_74,B_75))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_258,plain,(
    ! [C_78] :
      ( r2_relset_1('#skF_1','#skF_2',C_78,C_78)
      | ~ m1_subset_1(C_78,k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ) ),
    inference(resolution,[status(thm)],[c_26,c_246])).

tff(c_266,plain,(
    r2_relset_1('#skF_1','#skF_2','#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_26,c_258])).

tff(c_272,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_200,c_266])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n005.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 10:10:32 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.19/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.10/1.27  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.10/1.27  
% 2.10/1.27  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.10/1.27  %$ r2_relset_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k6_relset_1 > k2_relset_1 > k8_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.10/1.27  
% 2.10/1.27  %Foreground sorts:
% 2.10/1.27  
% 2.10/1.27  
% 2.10/1.27  %Background operators:
% 2.10/1.27  
% 2.10/1.27  
% 2.10/1.27  %Foreground operators:
% 2.10/1.27  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.10/1.27  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 2.10/1.27  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.10/1.27  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 2.10/1.27  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.10/1.27  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.10/1.27  tff(k6_relset_1, type, k6_relset_1: ($i * $i * $i * $i) > $i).
% 2.10/1.27  tff('#skF_2', type, '#skF_2': $i).
% 2.10/1.27  tff('#skF_3', type, '#skF_3': $i).
% 2.10/1.27  tff('#skF_1', type, '#skF_1': $i).
% 2.10/1.27  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.10/1.27  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.10/1.27  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.10/1.27  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.10/1.27  tff('#skF_4', type, '#skF_4': $i).
% 2.10/1.27  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.10/1.27  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.10/1.27  
% 2.10/1.29  tff(f_75, negated_conjecture, ~(![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (r1_tarski(B, C) => r2_relset_1(A, B, k6_relset_1(A, B, C, D), D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_relset_1)).
% 2.10/1.29  tff(f_38, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.10/1.29  tff(f_36, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.10/1.29  tff(f_58, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 2.10/1.29  tff(f_54, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k2_relset_1(A, B, C), k1_zfmisc_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_relset_1)).
% 2.10/1.29  tff(f_29, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 2.10/1.29  tff(f_44, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k8_relat_1(A, B) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t125_relat_1)).
% 2.10/1.29  tff(f_50, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => (k8_relat_1(B, k8_relat_1(A, C)) = k8_relat_1(A, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t129_relat_1)).
% 2.10/1.29  tff(f_62, axiom, (![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k6_relset_1(A, B, C, D) = k8_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_relset_1)).
% 2.10/1.29  tff(f_68, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => r2_relset_1(A, B, C, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', reflexivity_r2_relset_1)).
% 2.10/1.29  tff(c_24, plain, (r1_tarski('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.10/1.29  tff(c_8, plain, (![A_6, B_7]: (v1_relat_1(k2_zfmisc_1(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.10/1.29  tff(c_26, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.10/1.29  tff(c_38, plain, (![B_33, A_34]: (v1_relat_1(B_33) | ~m1_subset_1(B_33, k1_zfmisc_1(A_34)) | ~v1_relat_1(A_34))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.10/1.29  tff(c_44, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_26, c_38])).
% 2.10/1.29  tff(c_48, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_8, c_44])).
% 2.10/1.29  tff(c_62, plain, (![A_39, B_40, C_41]: (k2_relset_1(A_39, B_40, C_41)=k2_relat_1(C_41) | ~m1_subset_1(C_41, k1_zfmisc_1(k2_zfmisc_1(A_39, B_40))))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.10/1.29  tff(c_71, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_26, c_62])).
% 2.10/1.29  tff(c_76, plain, (![A_42, B_43, C_44]: (m1_subset_1(k2_relset_1(A_42, B_43, C_44), k1_zfmisc_1(B_43)) | ~m1_subset_1(C_44, k1_zfmisc_1(k2_zfmisc_1(A_42, B_43))))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.10/1.29  tff(c_89, plain, (m1_subset_1(k2_relat_1('#skF_4'), k1_zfmisc_1('#skF_2')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_71, c_76])).
% 2.10/1.29  tff(c_94, plain, (m1_subset_1(k2_relat_1('#skF_4'), k1_zfmisc_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_89])).
% 2.10/1.29  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(A_1, B_2) | ~m1_subset_1(A_1, k1_zfmisc_1(B_2)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.10/1.29  tff(c_102, plain, (r1_tarski(k2_relat_1('#skF_4'), '#skF_2')), inference(resolution, [status(thm)], [c_94, c_2])).
% 2.10/1.29  tff(c_10, plain, (![A_8, B_9]: (k8_relat_1(A_8, B_9)=B_9 | ~r1_tarski(k2_relat_1(B_9), A_8) | ~v1_relat_1(B_9))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.10/1.29  tff(c_105, plain, (k8_relat_1('#skF_2', '#skF_4')='#skF_4' | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_102, c_10])).
% 2.10/1.29  tff(c_111, plain, (k8_relat_1('#skF_2', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_48, c_105])).
% 2.10/1.29  tff(c_152, plain, (![B_54, A_55, C_56]: (k8_relat_1(B_54, k8_relat_1(A_55, C_56))=k8_relat_1(A_55, C_56) | ~r1_tarski(A_55, B_54) | ~v1_relat_1(C_56))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.10/1.29  tff(c_167, plain, (![B_54]: (k8_relat_1(B_54, '#skF_4')=k8_relat_1('#skF_2', '#skF_4') | ~r1_tarski('#skF_2', B_54) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_111, c_152])).
% 2.10/1.29  tff(c_172, plain, (![B_57]: (k8_relat_1(B_57, '#skF_4')='#skF_4' | ~r1_tarski('#skF_2', B_57))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_111, c_167])).
% 2.10/1.29  tff(c_176, plain, (k8_relat_1('#skF_3', '#skF_4')='#skF_4'), inference(resolution, [status(thm)], [c_24, c_172])).
% 2.10/1.29  tff(c_187, plain, (![A_59, B_60, C_61, D_62]: (k6_relset_1(A_59, B_60, C_61, D_62)=k8_relat_1(C_61, D_62) | ~m1_subset_1(D_62, k1_zfmisc_1(k2_zfmisc_1(A_59, B_60))))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.10/1.29  tff(c_198, plain, (![C_61]: (k6_relset_1('#skF_1', '#skF_2', C_61, '#skF_4')=k8_relat_1(C_61, '#skF_4'))), inference(resolution, [status(thm)], [c_26, c_187])).
% 2.10/1.29  tff(c_22, plain, (~r2_relset_1('#skF_1', '#skF_2', k6_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.10/1.29  tff(c_199, plain, (~r2_relset_1('#skF_1', '#skF_2', k8_relat_1('#skF_3', '#skF_4'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_198, c_22])).
% 2.10/1.29  tff(c_200, plain, (~r2_relset_1('#skF_1', '#skF_2', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_176, c_199])).
% 2.10/1.29  tff(c_246, plain, (![A_74, B_75, C_76, D_77]: (r2_relset_1(A_74, B_75, C_76, C_76) | ~m1_subset_1(D_77, k1_zfmisc_1(k2_zfmisc_1(A_74, B_75))) | ~m1_subset_1(C_76, k1_zfmisc_1(k2_zfmisc_1(A_74, B_75))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.10/1.29  tff(c_258, plain, (![C_78]: (r2_relset_1('#skF_1', '#skF_2', C_78, C_78) | ~m1_subset_1(C_78, k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))))), inference(resolution, [status(thm)], [c_26, c_246])).
% 2.10/1.29  tff(c_266, plain, (r2_relset_1('#skF_1', '#skF_2', '#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_26, c_258])).
% 2.10/1.29  tff(c_272, plain, $false, inference(negUnitSimplification, [status(thm)], [c_200, c_266])).
% 2.10/1.29  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.10/1.29  
% 2.10/1.29  Inference rules
% 2.10/1.29  ----------------------
% 2.10/1.29  #Ref     : 0
% 2.10/1.29  #Sup     : 54
% 2.10/1.29  #Fact    : 0
% 2.10/1.29  #Define  : 0
% 2.10/1.29  #Split   : 2
% 2.10/1.29  #Chain   : 0
% 2.10/1.29  #Close   : 0
% 2.10/1.29  
% 2.10/1.29  Ordering : KBO
% 2.10/1.29  
% 2.10/1.29  Simplification rules
% 2.10/1.29  ----------------------
% 2.10/1.29  #Subsume      : 4
% 2.10/1.29  #Demod        : 19
% 2.10/1.29  #Tautology    : 16
% 2.10/1.29  #SimpNegUnit  : 1
% 2.10/1.29  #BackRed      : 1
% 2.10/1.29  
% 2.10/1.29  #Partial instantiations: 0
% 2.10/1.29  #Strategies tried      : 1
% 2.10/1.29  
% 2.10/1.29  Timing (in seconds)
% 2.10/1.29  ----------------------
% 2.10/1.29  Preprocessing        : 0.31
% 2.10/1.29  Parsing              : 0.17
% 2.10/1.29  CNF conversion       : 0.02
% 2.10/1.29  Main loop            : 0.22
% 2.10/1.29  Inferencing          : 0.09
% 2.10/1.29  Reduction            : 0.06
% 2.10/1.29  Demodulation         : 0.05
% 2.10/1.29  BG Simplification    : 0.01
% 2.10/1.29  Subsumption          : 0.03
% 2.10/1.29  Abstraction          : 0.02
% 2.10/1.29  MUC search           : 0.00
% 2.10/1.29  Cooper               : 0.00
% 2.10/1.29  Total                : 0.56
% 2.10/1.29  Index Insertion      : 0.00
% 2.10/1.29  Index Deletion       : 0.00
% 2.10/1.29  Index Matching       : 0.00
% 2.10/1.29  BG Taut test         : 0.00
%------------------------------------------------------------------------------

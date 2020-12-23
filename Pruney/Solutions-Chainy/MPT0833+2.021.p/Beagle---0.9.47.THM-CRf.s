%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:07:48 EST 2020

% Result     : Theorem 1.85s
% Output     : CNFRefutation 1.85s
% Verified   : 
% Statistics : Number of formulae       :   56 (  77 expanded)
%              Number of leaves         :   27 (  38 expanded)
%              Depth                    :   10
%              Number of atoms          :   78 ( 124 expanded)
%              Number of equality atoms :    8 (   8 expanded)
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

tff(f_46,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_75,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B)))
       => ( r1_tarski(B,C)
         => r2_relset_1(A,B,k6_relset_1(A,B,C,D),D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_relset_1)).

tff(f_38,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_58,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k2_relat_1(B),A)
       => k8_relat_1(A,B) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t125_relat_1)).

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

tff(c_10,plain,(
    ! [A_9,B_10] : v1_relat_1(k2_zfmisc_1(A_9,B_10)) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_26,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_28,plain,(
    ! [B_26,A_27] :
      ( v1_relat_1(B_26)
      | ~ m1_subset_1(B_26,k1_zfmisc_1(A_27))
      | ~ v1_relat_1(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_31,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_26,c_28])).

tff(c_34,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_31])).

tff(c_59,plain,(
    ! [C_39,B_40,A_41] :
      ( v5_relat_1(C_39,B_40)
      | ~ m1_subset_1(C_39,k1_zfmisc_1(k2_zfmisc_1(A_41,B_40))) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_63,plain,(
    v5_relat_1('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_26,c_59])).

tff(c_8,plain,(
    ! [B_8,A_7] :
      ( r1_tarski(k2_relat_1(B_8),A_7)
      | ~ v5_relat_1(B_8,A_7)
      | ~ v1_relat_1(B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_24,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_41,plain,(
    ! [A_32,C_33,B_34] :
      ( r1_tarski(A_32,C_33)
      | ~ r1_tarski(B_34,C_33)
      | ~ r1_tarski(A_32,B_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_48,plain,(
    ! [A_35] :
      ( r1_tarski(A_35,'#skF_3')
      | ~ r1_tarski(A_35,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_24,c_41])).

tff(c_64,plain,(
    ! [B_42] :
      ( r1_tarski(k2_relat_1(B_42),'#skF_3')
      | ~ v5_relat_1(B_42,'#skF_2')
      | ~ v1_relat_1(B_42) ) ),
    inference(resolution,[status(thm)],[c_8,c_48])).

tff(c_6,plain,(
    ! [B_8,A_7] :
      ( v5_relat_1(B_8,A_7)
      | ~ r1_tarski(k2_relat_1(B_8),A_7)
      | ~ v1_relat_1(B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_81,plain,(
    ! [B_45] :
      ( v5_relat_1(B_45,'#skF_3')
      | ~ v5_relat_1(B_45,'#skF_2')
      | ~ v1_relat_1(B_45) ) ),
    inference(resolution,[status(thm)],[c_64,c_6])).

tff(c_84,plain,
    ( v5_relat_1('#skF_4','#skF_3')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_63,c_81])).

tff(c_87,plain,(
    v5_relat_1('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_84])).

tff(c_72,plain,(
    ! [A_43,B_44] :
      ( k8_relat_1(A_43,B_44) = B_44
      | ~ r1_tarski(k2_relat_1(B_44),A_43)
      | ~ v1_relat_1(B_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_88,plain,(
    ! [A_46,B_47] :
      ( k8_relat_1(A_46,B_47) = B_47
      | ~ v5_relat_1(B_47,A_46)
      | ~ v1_relat_1(B_47) ) ),
    inference(resolution,[status(thm)],[c_8,c_72])).

tff(c_91,plain,
    ( k8_relat_1('#skF_3','#skF_4') = '#skF_4'
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_87,c_88])).

tff(c_97,plain,(
    k8_relat_1('#skF_3','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_91])).

tff(c_127,plain,(
    ! [A_54,B_55,C_56,D_57] :
      ( k6_relset_1(A_54,B_55,C_56,D_57) = k8_relat_1(C_56,D_57)
      | ~ m1_subset_1(D_57,k1_zfmisc_1(k2_zfmisc_1(A_54,B_55))) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_130,plain,(
    ! [C_56] : k6_relset_1('#skF_1','#skF_2',C_56,'#skF_4') = k8_relat_1(C_56,'#skF_4') ),
    inference(resolution,[status(thm)],[c_26,c_127])).

tff(c_22,plain,(
    ~ r2_relset_1('#skF_1','#skF_2',k6_relset_1('#skF_1','#skF_2','#skF_3','#skF_4'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_135,plain,(
    ~ r2_relset_1('#skF_1','#skF_2',k8_relat_1('#skF_3','#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_130,c_22])).

tff(c_136,plain,(
    ~ r2_relset_1('#skF_1','#skF_2','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_97,c_135])).

tff(c_131,plain,(
    ! [A_58,B_59,C_60,D_61] :
      ( r2_relset_1(A_58,B_59,C_60,C_60)
      | ~ m1_subset_1(D_61,k1_zfmisc_1(k2_zfmisc_1(A_58,B_59)))
      | ~ m1_subset_1(C_60,k1_zfmisc_1(k2_zfmisc_1(A_58,B_59))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_146,plain,(
    ! [C_63] :
      ( r2_relset_1('#skF_1','#skF_2',C_63,C_63)
      | ~ m1_subset_1(C_63,k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ) ),
    inference(resolution,[status(thm)],[c_26,c_131])).

tff(c_148,plain,(
    r2_relset_1('#skF_1','#skF_2','#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_26,c_146])).

tff(c_152,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_136,c_148])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:11:31 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.85/1.17  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.85/1.18  
% 1.85/1.18  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.85/1.18  %$ r2_relset_1 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k6_relset_1 > k8_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 1.85/1.18  
% 1.85/1.18  %Foreground sorts:
% 1.85/1.18  
% 1.85/1.18  
% 1.85/1.18  %Background operators:
% 1.85/1.18  
% 1.85/1.18  
% 1.85/1.18  %Foreground operators:
% 1.85/1.18  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 1.85/1.18  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.85/1.18  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 1.85/1.18  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.85/1.18  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.85/1.18  tff(k6_relset_1, type, k6_relset_1: ($i * $i * $i * $i) > $i).
% 1.85/1.18  tff('#skF_2', type, '#skF_2': $i).
% 1.85/1.18  tff('#skF_3', type, '#skF_3': $i).
% 1.85/1.18  tff('#skF_1', type, '#skF_1': $i).
% 1.85/1.18  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 1.85/1.18  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.85/1.18  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.85/1.18  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.85/1.18  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.85/1.18  tff('#skF_4', type, '#skF_4': $i).
% 1.85/1.18  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.85/1.18  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 1.85/1.18  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.85/1.18  
% 1.85/1.19  tff(f_46, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 1.85/1.19  tff(f_75, negated_conjecture, ~(![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (r1_tarski(B, C) => r2_relset_1(A, B, k6_relset_1(A, B, C, D), D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_relset_1)).
% 1.85/1.19  tff(f_38, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 1.85/1.19  tff(f_58, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 1.85/1.19  tff(f_44, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 1.85/1.19  tff(f_31, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 1.85/1.19  tff(f_52, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k8_relat_1(A, B) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t125_relat_1)).
% 1.85/1.19  tff(f_62, axiom, (![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k6_relset_1(A, B, C, D) = k8_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_relset_1)).
% 1.85/1.19  tff(f_68, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => r2_relset_1(A, B, C, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', reflexivity_r2_relset_1)).
% 1.85/1.19  tff(c_10, plain, (![A_9, B_10]: (v1_relat_1(k2_zfmisc_1(A_9, B_10)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.85/1.19  tff(c_26, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_75])).
% 1.85/1.19  tff(c_28, plain, (![B_26, A_27]: (v1_relat_1(B_26) | ~m1_subset_1(B_26, k1_zfmisc_1(A_27)) | ~v1_relat_1(A_27))), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.85/1.19  tff(c_31, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_26, c_28])).
% 1.85/1.19  tff(c_34, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_10, c_31])).
% 1.85/1.19  tff(c_59, plain, (![C_39, B_40, A_41]: (v5_relat_1(C_39, B_40) | ~m1_subset_1(C_39, k1_zfmisc_1(k2_zfmisc_1(A_41, B_40))))), inference(cnfTransformation, [status(thm)], [f_58])).
% 1.85/1.19  tff(c_63, plain, (v5_relat_1('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_26, c_59])).
% 1.85/1.19  tff(c_8, plain, (![B_8, A_7]: (r1_tarski(k2_relat_1(B_8), A_7) | ~v5_relat_1(B_8, A_7) | ~v1_relat_1(B_8))), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.85/1.19  tff(c_24, plain, (r1_tarski('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_75])).
% 1.85/1.19  tff(c_41, plain, (![A_32, C_33, B_34]: (r1_tarski(A_32, C_33) | ~r1_tarski(B_34, C_33) | ~r1_tarski(A_32, B_34))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.85/1.19  tff(c_48, plain, (![A_35]: (r1_tarski(A_35, '#skF_3') | ~r1_tarski(A_35, '#skF_2'))), inference(resolution, [status(thm)], [c_24, c_41])).
% 1.85/1.19  tff(c_64, plain, (![B_42]: (r1_tarski(k2_relat_1(B_42), '#skF_3') | ~v5_relat_1(B_42, '#skF_2') | ~v1_relat_1(B_42))), inference(resolution, [status(thm)], [c_8, c_48])).
% 1.85/1.19  tff(c_6, plain, (![B_8, A_7]: (v5_relat_1(B_8, A_7) | ~r1_tarski(k2_relat_1(B_8), A_7) | ~v1_relat_1(B_8))), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.85/1.19  tff(c_81, plain, (![B_45]: (v5_relat_1(B_45, '#skF_3') | ~v5_relat_1(B_45, '#skF_2') | ~v1_relat_1(B_45))), inference(resolution, [status(thm)], [c_64, c_6])).
% 1.85/1.19  tff(c_84, plain, (v5_relat_1('#skF_4', '#skF_3') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_63, c_81])).
% 1.85/1.19  tff(c_87, plain, (v5_relat_1('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_84])).
% 1.85/1.19  tff(c_72, plain, (![A_43, B_44]: (k8_relat_1(A_43, B_44)=B_44 | ~r1_tarski(k2_relat_1(B_44), A_43) | ~v1_relat_1(B_44))), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.85/1.19  tff(c_88, plain, (![A_46, B_47]: (k8_relat_1(A_46, B_47)=B_47 | ~v5_relat_1(B_47, A_46) | ~v1_relat_1(B_47))), inference(resolution, [status(thm)], [c_8, c_72])).
% 1.85/1.19  tff(c_91, plain, (k8_relat_1('#skF_3', '#skF_4')='#skF_4' | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_87, c_88])).
% 1.85/1.19  tff(c_97, plain, (k8_relat_1('#skF_3', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_34, c_91])).
% 1.85/1.19  tff(c_127, plain, (![A_54, B_55, C_56, D_57]: (k6_relset_1(A_54, B_55, C_56, D_57)=k8_relat_1(C_56, D_57) | ~m1_subset_1(D_57, k1_zfmisc_1(k2_zfmisc_1(A_54, B_55))))), inference(cnfTransformation, [status(thm)], [f_62])).
% 1.85/1.19  tff(c_130, plain, (![C_56]: (k6_relset_1('#skF_1', '#skF_2', C_56, '#skF_4')=k8_relat_1(C_56, '#skF_4'))), inference(resolution, [status(thm)], [c_26, c_127])).
% 1.85/1.19  tff(c_22, plain, (~r2_relset_1('#skF_1', '#skF_2', k6_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_75])).
% 1.85/1.19  tff(c_135, plain, (~r2_relset_1('#skF_1', '#skF_2', k8_relat_1('#skF_3', '#skF_4'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_130, c_22])).
% 1.85/1.19  tff(c_136, plain, (~r2_relset_1('#skF_1', '#skF_2', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_97, c_135])).
% 1.85/1.19  tff(c_131, plain, (![A_58, B_59, C_60, D_61]: (r2_relset_1(A_58, B_59, C_60, C_60) | ~m1_subset_1(D_61, k1_zfmisc_1(k2_zfmisc_1(A_58, B_59))) | ~m1_subset_1(C_60, k1_zfmisc_1(k2_zfmisc_1(A_58, B_59))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 1.85/1.19  tff(c_146, plain, (![C_63]: (r2_relset_1('#skF_1', '#skF_2', C_63, C_63) | ~m1_subset_1(C_63, k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))))), inference(resolution, [status(thm)], [c_26, c_131])).
% 1.85/1.19  tff(c_148, plain, (r2_relset_1('#skF_1', '#skF_2', '#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_26, c_146])).
% 1.85/1.19  tff(c_152, plain, $false, inference(negUnitSimplification, [status(thm)], [c_136, c_148])).
% 1.85/1.19  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.85/1.19  
% 1.85/1.19  Inference rules
% 1.85/1.19  ----------------------
% 1.85/1.19  #Ref     : 0
% 1.85/1.19  #Sup     : 26
% 1.85/1.19  #Fact    : 0
% 1.85/1.19  #Define  : 0
% 1.85/1.19  #Split   : 0
% 1.85/1.19  #Chain   : 0
% 1.85/1.19  #Close   : 0
% 1.85/1.19  
% 1.85/1.19  Ordering : KBO
% 1.85/1.19  
% 1.85/1.19  Simplification rules
% 1.85/1.19  ----------------------
% 1.85/1.19  #Subsume      : 0
% 1.85/1.19  #Demod        : 8
% 1.85/1.19  #Tautology    : 8
% 1.85/1.19  #SimpNegUnit  : 1
% 1.85/1.19  #BackRed      : 1
% 1.85/1.19  
% 1.85/1.19  #Partial instantiations: 0
% 1.85/1.19  #Strategies tried      : 1
% 1.85/1.19  
% 1.85/1.19  Timing (in seconds)
% 1.85/1.19  ----------------------
% 1.85/1.19  Preprocessing        : 0.28
% 1.85/1.19  Parsing              : 0.15
% 1.85/1.19  CNF conversion       : 0.02
% 1.85/1.19  Main loop            : 0.15
% 1.85/1.19  Inferencing          : 0.06
% 1.85/1.19  Reduction            : 0.04
% 1.85/1.19  Demodulation         : 0.03
% 1.85/1.19  BG Simplification    : 0.01
% 1.85/1.19  Subsumption          : 0.02
% 1.85/1.19  Abstraction          : 0.01
% 1.85/1.19  MUC search           : 0.00
% 1.85/1.19  Cooper               : 0.00
% 1.85/1.19  Total                : 0.46
% 1.85/1.19  Index Insertion      : 0.00
% 1.85/1.20  Index Deletion       : 0.00
% 1.85/1.20  Index Matching       : 0.00
% 1.85/1.20  BG Taut test         : 0.00
%------------------------------------------------------------------------------

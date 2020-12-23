%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:07:46 EST 2020

% Result     : Theorem 2.56s
% Output     : CNFRefutation 2.56s
% Verified   : 
% Statistics : Number of formulae       :   51 (  67 expanded)
%              Number of leaves         :   27 (  35 expanded)
%              Depth                    :    8
%              Number of atoms          :   71 ( 104 expanded)
%              Number of equality atoms :   10 (  10 expanded)
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

tff(f_99,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B)))
       => ( r1_tarski(B,C)
         => r2_relset_1(A,B,k6_relset_1(A,B,C,D),D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_relset_1)).

tff(f_92,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_59,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_42,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_80,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_74,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => ! [C] :
          ( ( v1_relat_1(C)
            & v5_relat_1(C,A) )
         => v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t218_relat_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k2_relat_1(B),A)
       => k8_relat_1(A,B) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t125_relat_1)).

tff(f_84,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k6_relset_1(A,B,C,D) = k8_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_relset_1)).

tff(c_40,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_232,plain,(
    ! [A_76,B_77,D_78] :
      ( r2_relset_1(A_76,B_77,D_78,D_78)
      | ~ m1_subset_1(D_78,k1_zfmisc_1(k2_zfmisc_1(A_76,B_77))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_239,plain,(
    r2_relset_1('#skF_1','#skF_2','#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_40,c_232])).

tff(c_38,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_20,plain,(
    ! [A_14,B_15] : v1_relat_1(k2_zfmisc_1(A_14,B_15)) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_54,plain,(
    ! [B_40,A_41] :
      ( v1_relat_1(B_40)
      | ~ m1_subset_1(B_40,k1_zfmisc_1(A_41))
      | ~ v1_relat_1(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_60,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_40,c_54])).

tff(c_64,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_60])).

tff(c_141,plain,(
    ! [C_59,B_60,A_61] :
      ( v5_relat_1(C_59,B_60)
      | ~ m1_subset_1(C_59,k1_zfmisc_1(k2_zfmisc_1(A_61,B_60))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_150,plain,(
    v5_relat_1('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_40,c_141])).

tff(c_241,plain,(
    ! [C_79,B_80,A_81] :
      ( v5_relat_1(C_79,B_80)
      | ~ v5_relat_1(C_79,A_81)
      | ~ v1_relat_1(C_79)
      | ~ r1_tarski(A_81,B_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_245,plain,(
    ! [B_80] :
      ( v5_relat_1('#skF_4',B_80)
      | ~ v1_relat_1('#skF_4')
      | ~ r1_tarski('#skF_2',B_80) ) ),
    inference(resolution,[status(thm)],[c_150,c_241])).

tff(c_255,plain,(
    ! [B_82] :
      ( v5_relat_1('#skF_4',B_82)
      | ~ r1_tarski('#skF_2',B_82) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_245])).

tff(c_18,plain,(
    ! [B_13,A_12] :
      ( r1_tarski(k2_relat_1(B_13),A_12)
      | ~ v5_relat_1(B_13,A_12)
      | ~ v1_relat_1(B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_151,plain,(
    ! [A_62,B_63] :
      ( k8_relat_1(A_62,B_63) = B_63
      | ~ r1_tarski(k2_relat_1(B_63),A_62)
      | ~ v1_relat_1(B_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_159,plain,(
    ! [A_12,B_13] :
      ( k8_relat_1(A_12,B_13) = B_13
      | ~ v5_relat_1(B_13,A_12)
      | ~ v1_relat_1(B_13) ) ),
    inference(resolution,[status(thm)],[c_18,c_151])).

tff(c_262,plain,(
    ! [B_82] :
      ( k8_relat_1(B_82,'#skF_4') = '#skF_4'
      | ~ v1_relat_1('#skF_4')
      | ~ r1_tarski('#skF_2',B_82) ) ),
    inference(resolution,[status(thm)],[c_255,c_159])).

tff(c_273,plain,(
    ! [B_85] :
      ( k8_relat_1(B_85,'#skF_4') = '#skF_4'
      | ~ r1_tarski('#skF_2',B_85) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_262])).

tff(c_283,plain,(
    k8_relat_1('#skF_3','#skF_4') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_38,c_273])).

tff(c_400,plain,(
    ! [A_96,B_97,C_98,D_99] :
      ( k6_relset_1(A_96,B_97,C_98,D_99) = k8_relat_1(C_98,D_99)
      | ~ m1_subset_1(D_99,k1_zfmisc_1(k2_zfmisc_1(A_96,B_97))) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_407,plain,(
    ! [C_98] : k6_relset_1('#skF_1','#skF_2',C_98,'#skF_4') = k8_relat_1(C_98,'#skF_4') ),
    inference(resolution,[status(thm)],[c_40,c_400])).

tff(c_36,plain,(
    ~ r2_relset_1('#skF_1','#skF_2',k6_relset_1('#skF_1','#skF_2','#skF_3','#skF_4'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_432,plain,(
    ~ r2_relset_1('#skF_1','#skF_2',k8_relat_1('#skF_3','#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_407,c_36])).

tff(c_435,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_239,c_283,c_432])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 14:44:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.56/1.34  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.56/1.35  
% 2.56/1.35  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.56/1.35  %$ r2_relset_1 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k6_relset_1 > k8_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.56/1.35  
% 2.56/1.35  %Foreground sorts:
% 2.56/1.35  
% 2.56/1.35  
% 2.56/1.35  %Background operators:
% 2.56/1.35  
% 2.56/1.35  
% 2.56/1.35  %Foreground operators:
% 2.56/1.35  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 2.56/1.35  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.56/1.35  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 2.56/1.35  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.56/1.35  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.56/1.35  tff(k6_relset_1, type, k6_relset_1: ($i * $i * $i * $i) > $i).
% 2.56/1.35  tff('#skF_2', type, '#skF_2': $i).
% 2.56/1.35  tff('#skF_3', type, '#skF_3': $i).
% 2.56/1.35  tff('#skF_1', type, '#skF_1': $i).
% 2.56/1.35  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.56/1.35  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.56/1.35  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.56/1.35  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.56/1.35  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.56/1.35  tff('#skF_4', type, '#skF_4': $i).
% 2.56/1.35  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.56/1.35  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.56/1.35  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.56/1.35  
% 2.56/1.36  tff(f_99, negated_conjecture, ~(![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (r1_tarski(B, C) => r2_relset_1(A, B, k6_relset_1(A, B, C, D), D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_relset_1)).
% 2.56/1.36  tff(f_92, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 2.56/1.36  tff(f_59, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.56/1.36  tff(f_42, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.56/1.36  tff(f_80, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.56/1.36  tff(f_74, axiom, (![A, B]: (r1_tarski(A, B) => (![C]: ((v1_relat_1(C) & v5_relat_1(C, A)) => v5_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t218_relat_1)).
% 2.56/1.36  tff(f_57, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 2.56/1.36  tff(f_65, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k8_relat_1(A, B) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t125_relat_1)).
% 2.56/1.36  tff(f_84, axiom, (![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k6_relset_1(A, B, C, D) = k8_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_relset_1)).
% 2.56/1.36  tff(c_40, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.56/1.36  tff(c_232, plain, (![A_76, B_77, D_78]: (r2_relset_1(A_76, B_77, D_78, D_78) | ~m1_subset_1(D_78, k1_zfmisc_1(k2_zfmisc_1(A_76, B_77))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.56/1.36  tff(c_239, plain, (r2_relset_1('#skF_1', '#skF_2', '#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_40, c_232])).
% 2.56/1.36  tff(c_38, plain, (r1_tarski('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.56/1.36  tff(c_20, plain, (![A_14, B_15]: (v1_relat_1(k2_zfmisc_1(A_14, B_15)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.56/1.36  tff(c_54, plain, (![B_40, A_41]: (v1_relat_1(B_40) | ~m1_subset_1(B_40, k1_zfmisc_1(A_41)) | ~v1_relat_1(A_41))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.56/1.36  tff(c_60, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_40, c_54])).
% 2.56/1.36  tff(c_64, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_20, c_60])).
% 2.56/1.36  tff(c_141, plain, (![C_59, B_60, A_61]: (v5_relat_1(C_59, B_60) | ~m1_subset_1(C_59, k1_zfmisc_1(k2_zfmisc_1(A_61, B_60))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.56/1.36  tff(c_150, plain, (v5_relat_1('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_40, c_141])).
% 2.56/1.36  tff(c_241, plain, (![C_79, B_80, A_81]: (v5_relat_1(C_79, B_80) | ~v5_relat_1(C_79, A_81) | ~v1_relat_1(C_79) | ~r1_tarski(A_81, B_80))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.56/1.36  tff(c_245, plain, (![B_80]: (v5_relat_1('#skF_4', B_80) | ~v1_relat_1('#skF_4') | ~r1_tarski('#skF_2', B_80))), inference(resolution, [status(thm)], [c_150, c_241])).
% 2.56/1.36  tff(c_255, plain, (![B_82]: (v5_relat_1('#skF_4', B_82) | ~r1_tarski('#skF_2', B_82))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_245])).
% 2.56/1.36  tff(c_18, plain, (![B_13, A_12]: (r1_tarski(k2_relat_1(B_13), A_12) | ~v5_relat_1(B_13, A_12) | ~v1_relat_1(B_13))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.56/1.36  tff(c_151, plain, (![A_62, B_63]: (k8_relat_1(A_62, B_63)=B_63 | ~r1_tarski(k2_relat_1(B_63), A_62) | ~v1_relat_1(B_63))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.56/1.36  tff(c_159, plain, (![A_12, B_13]: (k8_relat_1(A_12, B_13)=B_13 | ~v5_relat_1(B_13, A_12) | ~v1_relat_1(B_13))), inference(resolution, [status(thm)], [c_18, c_151])).
% 2.56/1.36  tff(c_262, plain, (![B_82]: (k8_relat_1(B_82, '#skF_4')='#skF_4' | ~v1_relat_1('#skF_4') | ~r1_tarski('#skF_2', B_82))), inference(resolution, [status(thm)], [c_255, c_159])).
% 2.56/1.36  tff(c_273, plain, (![B_85]: (k8_relat_1(B_85, '#skF_4')='#skF_4' | ~r1_tarski('#skF_2', B_85))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_262])).
% 2.56/1.36  tff(c_283, plain, (k8_relat_1('#skF_3', '#skF_4')='#skF_4'), inference(resolution, [status(thm)], [c_38, c_273])).
% 2.56/1.36  tff(c_400, plain, (![A_96, B_97, C_98, D_99]: (k6_relset_1(A_96, B_97, C_98, D_99)=k8_relat_1(C_98, D_99) | ~m1_subset_1(D_99, k1_zfmisc_1(k2_zfmisc_1(A_96, B_97))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.56/1.36  tff(c_407, plain, (![C_98]: (k6_relset_1('#skF_1', '#skF_2', C_98, '#skF_4')=k8_relat_1(C_98, '#skF_4'))), inference(resolution, [status(thm)], [c_40, c_400])).
% 2.56/1.36  tff(c_36, plain, (~r2_relset_1('#skF_1', '#skF_2', k6_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.56/1.36  tff(c_432, plain, (~r2_relset_1('#skF_1', '#skF_2', k8_relat_1('#skF_3', '#skF_4'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_407, c_36])).
% 2.56/1.36  tff(c_435, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_239, c_283, c_432])).
% 2.56/1.36  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.56/1.36  
% 2.56/1.36  Inference rules
% 2.56/1.36  ----------------------
% 2.56/1.36  #Ref     : 0
% 2.56/1.36  #Sup     : 79
% 2.56/1.36  #Fact    : 0
% 2.56/1.36  #Define  : 0
% 2.56/1.36  #Split   : 6
% 2.56/1.36  #Chain   : 0
% 2.56/1.36  #Close   : 0
% 2.56/1.36  
% 2.56/1.36  Ordering : KBO
% 2.56/1.36  
% 2.56/1.36  Simplification rules
% 2.56/1.36  ----------------------
% 2.56/1.36  #Subsume      : 8
% 2.56/1.36  #Demod        : 38
% 2.56/1.36  #Tautology    : 23
% 2.56/1.36  #SimpNegUnit  : 0
% 2.56/1.36  #BackRed      : 1
% 2.56/1.36  
% 2.56/1.36  #Partial instantiations: 0
% 2.56/1.36  #Strategies tried      : 1
% 2.56/1.36  
% 2.56/1.36  Timing (in seconds)
% 2.56/1.36  ----------------------
% 2.56/1.37  Preprocessing        : 0.32
% 2.56/1.37  Parsing              : 0.17
% 2.56/1.37  CNF conversion       : 0.02
% 2.56/1.37  Main loop            : 0.28
% 2.56/1.37  Inferencing          : 0.10
% 2.56/1.37  Reduction            : 0.09
% 2.56/1.37  Demodulation         : 0.06
% 2.56/1.37  BG Simplification    : 0.02
% 2.56/1.37  Subsumption          : 0.05
% 2.56/1.37  Abstraction          : 0.02
% 2.56/1.37  MUC search           : 0.00
% 2.56/1.37  Cooper               : 0.00
% 2.56/1.37  Total                : 0.63
% 2.56/1.37  Index Insertion      : 0.00
% 2.56/1.37  Index Deletion       : 0.00
% 2.56/1.37  Index Matching       : 0.00
% 2.56/1.37  BG Taut test         : 0.00
%------------------------------------------------------------------------------

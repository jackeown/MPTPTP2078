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
% DateTime   : Thu Dec  3 10:07:41 EST 2020

% Result     : Theorem 2.44s
% Output     : CNFRefutation 2.44s
% Verified   : 
% Statistics : Number of formulae       :   62 ( 150 expanded)
%              Number of leaves         :   28 (  62 expanded)
%              Depth                    :   13
%              Number of atoms          :   83 ( 248 expanded)
%              Number of equality atoms :    3 (   6 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k6_relset_1 > k8_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k8_relat_1,type,(
    k8_relat_1: ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_76,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(C,A)))
       => m1_subset_1(k6_relset_1(C,A,B,D),k1_zfmisc_1(k2_zfmisc_1(C,B))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_relset_1)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k2_relat_1(k8_relat_1(A,B)),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t116_relat_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k8_relat_1(A,B),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t117_relat_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_71,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( ( r1_tarski(k1_relat_1(C),A)
          & r1_tarski(k2_relat_1(C),B) )
       => m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_relset_1)).

tff(f_63,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k6_relset_1(A,B,C,D) = k8_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_relset_1)).

tff(c_28,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_41,plain,(
    ! [C_33,A_34,B_35] :
      ( v1_relat_1(C_33)
      | ~ m1_subset_1(C_33,k1_zfmisc_1(k2_zfmisc_1(A_34,B_35))) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_50,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_28,c_41])).

tff(c_12,plain,(
    ! [A_8,B_9] :
      ( r1_tarski(k2_relat_1(k8_relat_1(A_8,B_9)),A_8)
      | ~ v1_relat_1(B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_14,plain,(
    ! [A_10,B_11] :
      ( r1_tarski(k8_relat_1(A_10,B_11),B_11)
      | ~ v1_relat_1(B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_31,plain,(
    ! [A_29,B_30] :
      ( r1_tarski(A_29,B_30)
      | ~ m1_subset_1(A_29,k1_zfmisc_1(B_30)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_39,plain,(
    r1_tarski('#skF_4',k2_zfmisc_1('#skF_3','#skF_1')) ),
    inference(resolution,[status(thm)],[c_28,c_31])).

tff(c_144,plain,(
    ! [A_55,C_56,B_57] :
      ( r1_tarski(A_55,C_56)
      | ~ r1_tarski(B_57,C_56)
      | ~ r1_tarski(A_55,B_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_157,plain,(
    ! [A_58] :
      ( r1_tarski(A_58,k2_zfmisc_1('#skF_3','#skF_1'))
      | ~ r1_tarski(A_58,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_39,c_144])).

tff(c_6,plain,(
    ! [A_4,B_5] :
      ( m1_subset_1(A_4,k1_zfmisc_1(B_5))
      | ~ r1_tarski(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_98,plain,(
    ! [C_47,A_48,B_49] :
      ( v4_relat_1(C_47,A_48)
      | ~ m1_subset_1(C_47,k1_zfmisc_1(k2_zfmisc_1(A_48,B_49))) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_106,plain,(
    ! [A_4,A_48,B_49] :
      ( v4_relat_1(A_4,A_48)
      | ~ r1_tarski(A_4,k2_zfmisc_1(A_48,B_49)) ) ),
    inference(resolution,[status(thm)],[c_6,c_98])).

tff(c_174,plain,(
    ! [A_58] :
      ( v4_relat_1(A_58,'#skF_3')
      | ~ r1_tarski(A_58,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_157,c_106])).

tff(c_49,plain,(
    ! [A_4,A_34,B_35] :
      ( v1_relat_1(A_4)
      | ~ r1_tarski(A_4,k2_zfmisc_1(A_34,B_35)) ) ),
    inference(resolution,[status(thm)],[c_6,c_41])).

tff(c_178,plain,(
    ! [A_59] :
      ( v1_relat_1(A_59)
      | ~ r1_tarski(A_59,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_157,c_49])).

tff(c_190,plain,(
    ! [A_10] :
      ( v1_relat_1(k8_relat_1(A_10,'#skF_4'))
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_14,c_178])).

tff(c_195,plain,(
    ! [A_10] : v1_relat_1(k8_relat_1(A_10,'#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_190])).

tff(c_10,plain,(
    ! [B_7,A_6] :
      ( r1_tarski(k1_relat_1(B_7),A_6)
      | ~ v4_relat_1(B_7,A_6)
      | ~ v1_relat_1(B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_243,plain,(
    ! [C_82,A_83,B_84] :
      ( m1_subset_1(C_82,k1_zfmisc_1(k2_zfmisc_1(A_83,B_84)))
      | ~ r1_tarski(k2_relat_1(C_82),B_84)
      | ~ r1_tarski(k1_relat_1(C_82),A_83)
      | ~ v1_relat_1(C_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_199,plain,(
    ! [A_63,B_64,C_65,D_66] :
      ( k6_relset_1(A_63,B_64,C_65,D_66) = k8_relat_1(C_65,D_66)
      | ~ m1_subset_1(D_66,k1_zfmisc_1(k2_zfmisc_1(A_63,B_64))) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_206,plain,(
    ! [C_65] : k6_relset_1('#skF_3','#skF_1',C_65,'#skF_4') = k8_relat_1(C_65,'#skF_4') ),
    inference(resolution,[status(thm)],[c_28,c_199])).

tff(c_26,plain,(
    ~ m1_subset_1(k6_relset_1('#skF_3','#skF_1','#skF_2','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_209,plain,(
    ~ m1_subset_1(k8_relat_1('#skF_2','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_206,c_26])).

tff(c_246,plain,
    ( ~ r1_tarski(k2_relat_1(k8_relat_1('#skF_2','#skF_4')),'#skF_2')
    | ~ r1_tarski(k1_relat_1(k8_relat_1('#skF_2','#skF_4')),'#skF_3')
    | ~ v1_relat_1(k8_relat_1('#skF_2','#skF_4')) ),
    inference(resolution,[status(thm)],[c_243,c_209])).

tff(c_263,plain,
    ( ~ r1_tarski(k2_relat_1(k8_relat_1('#skF_2','#skF_4')),'#skF_2')
    | ~ r1_tarski(k1_relat_1(k8_relat_1('#skF_2','#skF_4')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_195,c_246])).

tff(c_421,plain,(
    ~ r1_tarski(k1_relat_1(k8_relat_1('#skF_2','#skF_4')),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_263])).

tff(c_424,plain,
    ( ~ v4_relat_1(k8_relat_1('#skF_2','#skF_4'),'#skF_3')
    | ~ v1_relat_1(k8_relat_1('#skF_2','#skF_4')) ),
    inference(resolution,[status(thm)],[c_10,c_421])).

tff(c_427,plain,(
    ~ v4_relat_1(k8_relat_1('#skF_2','#skF_4'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_195,c_424])).

tff(c_431,plain,(
    ~ r1_tarski(k8_relat_1('#skF_2','#skF_4'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_174,c_427])).

tff(c_434,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_14,c_431])).

tff(c_438,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_434])).

tff(c_439,plain,(
    ~ r1_tarski(k2_relat_1(k8_relat_1('#skF_2','#skF_4')),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_263])).

tff(c_443,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_12,c_439])).

tff(c_447,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_443])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:23:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.44/1.31  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.44/1.32  
% 2.44/1.32  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.44/1.32  %$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k6_relset_1 > k8_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.44/1.32  
% 2.44/1.32  %Foreground sorts:
% 2.44/1.32  
% 2.44/1.32  
% 2.44/1.32  %Background operators:
% 2.44/1.32  
% 2.44/1.32  
% 2.44/1.32  %Foreground operators:
% 2.44/1.32  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 2.44/1.32  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.44/1.32  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.44/1.32  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.44/1.32  tff(k6_relset_1, type, k6_relset_1: ($i * $i * $i * $i) > $i).
% 2.44/1.32  tff('#skF_2', type, '#skF_2': $i).
% 2.44/1.32  tff('#skF_3', type, '#skF_3': $i).
% 2.44/1.32  tff('#skF_1', type, '#skF_1': $i).
% 2.44/1.32  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.44/1.32  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.44/1.32  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.44/1.32  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.44/1.32  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.44/1.32  tff('#skF_4', type, '#skF_4': $i).
% 2.44/1.32  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.44/1.32  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.44/1.32  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.44/1.32  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.44/1.32  
% 2.44/1.33  tff(f_76, negated_conjecture, ~(![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(C, A))) => m1_subset_1(k6_relset_1(C, A, B, D), k1_zfmisc_1(k2_zfmisc_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_relset_1)).
% 2.44/1.33  tff(f_53, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.44/1.33  tff(f_45, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k2_relat_1(k8_relat_1(A, B)), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t116_relat_1)).
% 2.44/1.33  tff(f_49, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k8_relat_1(A, B), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t117_relat_1)).
% 2.44/1.33  tff(f_35, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 2.44/1.33  tff(f_31, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 2.44/1.33  tff(f_59, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.44/1.33  tff(f_41, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 2.44/1.33  tff(f_71, axiom, (![A, B, C]: (v1_relat_1(C) => ((r1_tarski(k1_relat_1(C), A) & r1_tarski(k2_relat_1(C), B)) => m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_relset_1)).
% 2.44/1.33  tff(f_63, axiom, (![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k6_relset_1(A, B, C, D) = k8_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_relset_1)).
% 2.44/1.33  tff(c_28, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.44/1.33  tff(c_41, plain, (![C_33, A_34, B_35]: (v1_relat_1(C_33) | ~m1_subset_1(C_33, k1_zfmisc_1(k2_zfmisc_1(A_34, B_35))))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.44/1.33  tff(c_50, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_28, c_41])).
% 2.44/1.33  tff(c_12, plain, (![A_8, B_9]: (r1_tarski(k2_relat_1(k8_relat_1(A_8, B_9)), A_8) | ~v1_relat_1(B_9))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.44/1.33  tff(c_14, plain, (![A_10, B_11]: (r1_tarski(k8_relat_1(A_10, B_11), B_11) | ~v1_relat_1(B_11))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.44/1.33  tff(c_31, plain, (![A_29, B_30]: (r1_tarski(A_29, B_30) | ~m1_subset_1(A_29, k1_zfmisc_1(B_30)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.44/1.33  tff(c_39, plain, (r1_tarski('#skF_4', k2_zfmisc_1('#skF_3', '#skF_1'))), inference(resolution, [status(thm)], [c_28, c_31])).
% 2.44/1.33  tff(c_144, plain, (![A_55, C_56, B_57]: (r1_tarski(A_55, C_56) | ~r1_tarski(B_57, C_56) | ~r1_tarski(A_55, B_57))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.44/1.33  tff(c_157, plain, (![A_58]: (r1_tarski(A_58, k2_zfmisc_1('#skF_3', '#skF_1')) | ~r1_tarski(A_58, '#skF_4'))), inference(resolution, [status(thm)], [c_39, c_144])).
% 2.44/1.33  tff(c_6, plain, (![A_4, B_5]: (m1_subset_1(A_4, k1_zfmisc_1(B_5)) | ~r1_tarski(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.44/1.33  tff(c_98, plain, (![C_47, A_48, B_49]: (v4_relat_1(C_47, A_48) | ~m1_subset_1(C_47, k1_zfmisc_1(k2_zfmisc_1(A_48, B_49))))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.44/1.33  tff(c_106, plain, (![A_4, A_48, B_49]: (v4_relat_1(A_4, A_48) | ~r1_tarski(A_4, k2_zfmisc_1(A_48, B_49)))), inference(resolution, [status(thm)], [c_6, c_98])).
% 2.44/1.33  tff(c_174, plain, (![A_58]: (v4_relat_1(A_58, '#skF_3') | ~r1_tarski(A_58, '#skF_4'))), inference(resolution, [status(thm)], [c_157, c_106])).
% 2.44/1.33  tff(c_49, plain, (![A_4, A_34, B_35]: (v1_relat_1(A_4) | ~r1_tarski(A_4, k2_zfmisc_1(A_34, B_35)))), inference(resolution, [status(thm)], [c_6, c_41])).
% 2.44/1.33  tff(c_178, plain, (![A_59]: (v1_relat_1(A_59) | ~r1_tarski(A_59, '#skF_4'))), inference(resolution, [status(thm)], [c_157, c_49])).
% 2.44/1.33  tff(c_190, plain, (![A_10]: (v1_relat_1(k8_relat_1(A_10, '#skF_4')) | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_14, c_178])).
% 2.44/1.33  tff(c_195, plain, (![A_10]: (v1_relat_1(k8_relat_1(A_10, '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_190])).
% 2.44/1.33  tff(c_10, plain, (![B_7, A_6]: (r1_tarski(k1_relat_1(B_7), A_6) | ~v4_relat_1(B_7, A_6) | ~v1_relat_1(B_7))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.44/1.33  tff(c_243, plain, (![C_82, A_83, B_84]: (m1_subset_1(C_82, k1_zfmisc_1(k2_zfmisc_1(A_83, B_84))) | ~r1_tarski(k2_relat_1(C_82), B_84) | ~r1_tarski(k1_relat_1(C_82), A_83) | ~v1_relat_1(C_82))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.44/1.33  tff(c_199, plain, (![A_63, B_64, C_65, D_66]: (k6_relset_1(A_63, B_64, C_65, D_66)=k8_relat_1(C_65, D_66) | ~m1_subset_1(D_66, k1_zfmisc_1(k2_zfmisc_1(A_63, B_64))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.44/1.33  tff(c_206, plain, (![C_65]: (k6_relset_1('#skF_3', '#skF_1', C_65, '#skF_4')=k8_relat_1(C_65, '#skF_4'))), inference(resolution, [status(thm)], [c_28, c_199])).
% 2.44/1.33  tff(c_26, plain, (~m1_subset_1(k6_relset_1('#skF_3', '#skF_1', '#skF_2', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.44/1.33  tff(c_209, plain, (~m1_subset_1(k8_relat_1('#skF_2', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_206, c_26])).
% 2.44/1.33  tff(c_246, plain, (~r1_tarski(k2_relat_1(k8_relat_1('#skF_2', '#skF_4')), '#skF_2') | ~r1_tarski(k1_relat_1(k8_relat_1('#skF_2', '#skF_4')), '#skF_3') | ~v1_relat_1(k8_relat_1('#skF_2', '#skF_4'))), inference(resolution, [status(thm)], [c_243, c_209])).
% 2.44/1.33  tff(c_263, plain, (~r1_tarski(k2_relat_1(k8_relat_1('#skF_2', '#skF_4')), '#skF_2') | ~r1_tarski(k1_relat_1(k8_relat_1('#skF_2', '#skF_4')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_195, c_246])).
% 2.44/1.33  tff(c_421, plain, (~r1_tarski(k1_relat_1(k8_relat_1('#skF_2', '#skF_4')), '#skF_3')), inference(splitLeft, [status(thm)], [c_263])).
% 2.44/1.33  tff(c_424, plain, (~v4_relat_1(k8_relat_1('#skF_2', '#skF_4'), '#skF_3') | ~v1_relat_1(k8_relat_1('#skF_2', '#skF_4'))), inference(resolution, [status(thm)], [c_10, c_421])).
% 2.44/1.33  tff(c_427, plain, (~v4_relat_1(k8_relat_1('#skF_2', '#skF_4'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_195, c_424])).
% 2.44/1.33  tff(c_431, plain, (~r1_tarski(k8_relat_1('#skF_2', '#skF_4'), '#skF_4')), inference(resolution, [status(thm)], [c_174, c_427])).
% 2.44/1.33  tff(c_434, plain, (~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_14, c_431])).
% 2.44/1.33  tff(c_438, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_50, c_434])).
% 2.44/1.33  tff(c_439, plain, (~r1_tarski(k2_relat_1(k8_relat_1('#skF_2', '#skF_4')), '#skF_2')), inference(splitRight, [status(thm)], [c_263])).
% 2.44/1.33  tff(c_443, plain, (~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_12, c_439])).
% 2.44/1.33  tff(c_447, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_50, c_443])).
% 2.44/1.33  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.44/1.33  
% 2.44/1.33  Inference rules
% 2.44/1.33  ----------------------
% 2.44/1.33  #Ref     : 0
% 2.44/1.33  #Sup     : 86
% 2.44/1.33  #Fact    : 0
% 2.44/1.33  #Define  : 0
% 2.44/1.33  #Split   : 1
% 2.44/1.33  #Chain   : 0
% 2.44/1.33  #Close   : 0
% 2.44/1.33  
% 2.44/1.33  Ordering : KBO
% 2.44/1.33  
% 2.44/1.33  Simplification rules
% 2.44/1.33  ----------------------
% 2.44/1.33  #Subsume      : 7
% 2.44/1.33  #Demod        : 12
% 2.44/1.33  #Tautology    : 9
% 2.44/1.33  #SimpNegUnit  : 0
% 2.44/1.33  #BackRed      : 2
% 2.44/1.33  
% 2.44/1.33  #Partial instantiations: 0
% 2.44/1.33  #Strategies tried      : 1
% 2.44/1.33  
% 2.44/1.34  Timing (in seconds)
% 2.44/1.34  ----------------------
% 2.44/1.34  Preprocessing        : 0.29
% 2.44/1.34  Parsing              : 0.16
% 2.44/1.34  CNF conversion       : 0.02
% 2.44/1.34  Main loop            : 0.27
% 2.44/1.34  Inferencing          : 0.11
% 2.44/1.34  Reduction            : 0.07
% 2.44/1.34  Demodulation         : 0.05
% 2.44/1.34  BG Simplification    : 0.01
% 2.44/1.34  Subsumption          : 0.05
% 2.44/1.34  Abstraction          : 0.01
% 2.44/1.34  MUC search           : 0.00
% 2.44/1.34  Cooper               : 0.00
% 2.44/1.34  Total                : 0.59
% 2.44/1.34  Index Insertion      : 0.00
% 2.44/1.34  Index Deletion       : 0.00
% 2.44/1.34  Index Matching       : 0.00
% 2.44/1.34  BG Taut test         : 0.00
%------------------------------------------------------------------------------

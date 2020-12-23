%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:07:44 EST 2020

% Result     : Theorem 2.03s
% Output     : CNFRefutation 2.03s
% Verified   : 
% Statistics : Number of formulae       :   61 ( 214 expanded)
%              Number of leaves         :   30 (  86 expanded)
%              Depth                    :   12
%              Number of atoms          :   80 ( 360 expanded)
%              Number of equality atoms :   12 (  39 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k6_relset_1 > k8_relat_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k8_relat_1,type,(
    k8_relat_1: ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

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

tff(f_38,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_79,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(C,A)))
       => m1_subset_1(k6_relset_1(C,A,B,D),k1_zfmisc_1(k2_zfmisc_1(C,B))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_relset_1)).

tff(f_32,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k2_relat_1(k8_relat_1(A,B)),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t116_relat_1)).

tff(f_62,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_46,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k7_relat_1(k8_relat_1(A,C),B) = k8_relat_1(A,k7_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t140_relat_1)).

tff(f_36,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => v1_relat_1(k8_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_relat_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k1_relat_1(k7_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_relat_1)).

tff(f_74,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( ( r1_tarski(k1_relat_1(C),A)
          & r1_tarski(k2_relat_1(C),B) )
       => m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_relset_1)).

tff(f_66,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k6_relset_1(A,B,C,D) = k8_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_relset_1)).

tff(c_6,plain,(
    ! [A_6,B_7] : v1_relat_1(k2_zfmisc_1(A_6,B_7)) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_26,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_29,plain,(
    ! [B_31,A_32] :
      ( v1_relat_1(B_31)
      | ~ m1_subset_1(B_31,k1_zfmisc_1(A_32))
      | ~ v1_relat_1(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_32,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_3','#skF_1')) ),
    inference(resolution,[status(thm)],[c_26,c_29])).

tff(c_35,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_32])).

tff(c_8,plain,(
    ! [A_8,B_9] :
      ( r1_tarski(k2_relat_1(k8_relat_1(A_8,B_9)),A_8)
      | ~ v1_relat_1(B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_44,plain,(
    ! [C_42,A_43,B_44] :
      ( v4_relat_1(C_42,A_43)
      | ~ m1_subset_1(C_42,k1_zfmisc_1(k2_zfmisc_1(A_43,B_44))) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_48,plain,(
    v4_relat_1('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_26,c_44])).

tff(c_12,plain,(
    ! [B_14,A_13] :
      ( k7_relat_1(B_14,A_13) = B_14
      | ~ v4_relat_1(B_14,A_13)
      | ~ v1_relat_1(B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_51,plain,
    ( k7_relat_1('#skF_4','#skF_3') = '#skF_4'
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_48,c_12])).

tff(c_54,plain,(
    k7_relat_1('#skF_4','#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_35,c_51])).

tff(c_64,plain,(
    ! [A_45,C_46,B_47] :
      ( k8_relat_1(A_45,k7_relat_1(C_46,B_47)) = k7_relat_1(k8_relat_1(A_45,C_46),B_47)
      | ~ v1_relat_1(C_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_79,plain,(
    ! [A_45] :
      ( k7_relat_1(k8_relat_1(A_45,'#skF_4'),'#skF_3') = k8_relat_1(A_45,'#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_54,c_64])).

tff(c_83,plain,(
    ! [A_45] : k7_relat_1(k8_relat_1(A_45,'#skF_4'),'#skF_3') = k8_relat_1(A_45,'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_35,c_79])).

tff(c_4,plain,(
    ! [A_4,B_5] :
      ( v1_relat_1(k8_relat_1(A_4,B_5))
      | ~ v1_relat_1(B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_100,plain,(
    ! [A_50,C_51,B_52] :
      ( v1_relat_1(k7_relat_1(k8_relat_1(A_50,C_51),B_52))
      | ~ v1_relat_1(k7_relat_1(C_51,B_52))
      | ~ v1_relat_1(C_51) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_64,c_4])).

tff(c_103,plain,(
    ! [A_45] :
      ( v1_relat_1(k8_relat_1(A_45,'#skF_4'))
      | ~ v1_relat_1(k7_relat_1('#skF_4','#skF_3'))
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_83,c_100])).

tff(c_108,plain,(
    ! [A_45] : v1_relat_1(k8_relat_1(A_45,'#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_35,c_35,c_54,c_103])).

tff(c_84,plain,(
    ! [A_48] : k7_relat_1(k8_relat_1(A_48,'#skF_4'),'#skF_3') = k8_relat_1(A_48,'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_35,c_79])).

tff(c_14,plain,(
    ! [B_16,A_15] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_16,A_15)),A_15)
      | ~ v1_relat_1(B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_93,plain,(
    ! [A_48] :
      ( r1_tarski(k1_relat_1(k8_relat_1(A_48,'#skF_4')),'#skF_3')
      | ~ v1_relat_1(k8_relat_1(A_48,'#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_84,c_14])).

tff(c_131,plain,(
    ! [A_48] : r1_tarski(k1_relat_1(k8_relat_1(A_48,'#skF_4')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_108,c_93])).

tff(c_22,plain,(
    ! [C_26,A_24,B_25] :
      ( m1_subset_1(C_26,k1_zfmisc_1(k2_zfmisc_1(A_24,B_25)))
      | ~ r1_tarski(k2_relat_1(C_26),B_25)
      | ~ r1_tarski(k1_relat_1(C_26),A_24)
      | ~ v1_relat_1(C_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_155,plain,(
    ! [A_61,B_62,C_63,D_64] :
      ( k6_relset_1(A_61,B_62,C_63,D_64) = k8_relat_1(C_63,D_64)
      | ~ m1_subset_1(D_64,k1_zfmisc_1(k2_zfmisc_1(A_61,B_62))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_158,plain,(
    ! [C_63] : k6_relset_1('#skF_3','#skF_1',C_63,'#skF_4') = k8_relat_1(C_63,'#skF_4') ),
    inference(resolution,[status(thm)],[c_26,c_155])).

tff(c_24,plain,(
    ~ m1_subset_1(k6_relset_1('#skF_3','#skF_1','#skF_2','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_181,plain,(
    ~ m1_subset_1(k8_relat_1('#skF_2','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_158,c_24])).

tff(c_193,plain,
    ( ~ r1_tarski(k2_relat_1(k8_relat_1('#skF_2','#skF_4')),'#skF_2')
    | ~ r1_tarski(k1_relat_1(k8_relat_1('#skF_2','#skF_4')),'#skF_3')
    | ~ v1_relat_1(k8_relat_1('#skF_2','#skF_4')) ),
    inference(resolution,[status(thm)],[c_22,c_181])).

tff(c_196,plain,(
    ~ r1_tarski(k2_relat_1(k8_relat_1('#skF_2','#skF_4')),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_108,c_131,c_193])).

tff(c_199,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_8,c_196])).

tff(c_203,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_35,c_199])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:22:59 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.03/1.25  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.03/1.26  
% 2.03/1.26  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.03/1.26  %$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k6_relset_1 > k8_relat_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.03/1.26  
% 2.03/1.26  %Foreground sorts:
% 2.03/1.26  
% 2.03/1.26  
% 2.03/1.26  %Background operators:
% 2.03/1.26  
% 2.03/1.26  
% 2.03/1.26  %Foreground operators:
% 2.03/1.26  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 2.03/1.26  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.03/1.26  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.03/1.26  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.03/1.26  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.03/1.26  tff(k6_relset_1, type, k6_relset_1: ($i * $i * $i * $i) > $i).
% 2.03/1.26  tff('#skF_2', type, '#skF_2': $i).
% 2.03/1.26  tff('#skF_3', type, '#skF_3': $i).
% 2.03/1.26  tff('#skF_1', type, '#skF_1': $i).
% 2.03/1.26  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.03/1.26  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.03/1.26  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.03/1.26  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.03/1.26  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.03/1.26  tff('#skF_4', type, '#skF_4': $i).
% 2.03/1.26  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.03/1.26  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.03/1.26  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.03/1.26  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.03/1.26  
% 2.03/1.28  tff(f_38, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.03/1.28  tff(f_79, negated_conjecture, ~(![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(C, A))) => m1_subset_1(k6_relset_1(C, A, B, D), k1_zfmisc_1(k2_zfmisc_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_relset_1)).
% 2.03/1.28  tff(f_32, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.03/1.28  tff(f_42, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k2_relat_1(k8_relat_1(A, B)), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t116_relat_1)).
% 2.03/1.28  tff(f_62, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.03/1.28  tff(f_52, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t209_relat_1)).
% 2.03/1.28  tff(f_46, axiom, (![A, B, C]: (v1_relat_1(C) => (k7_relat_1(k8_relat_1(A, C), B) = k8_relat_1(A, k7_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t140_relat_1)).
% 2.03/1.28  tff(f_36, axiom, (![A, B]: (v1_relat_1(B) => v1_relat_1(k8_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k8_relat_1)).
% 2.03/1.28  tff(f_56, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k7_relat_1(B, A)), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t87_relat_1)).
% 2.03/1.28  tff(f_74, axiom, (![A, B, C]: (v1_relat_1(C) => ((r1_tarski(k1_relat_1(C), A) & r1_tarski(k2_relat_1(C), B)) => m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_relset_1)).
% 2.03/1.28  tff(f_66, axiom, (![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k6_relset_1(A, B, C, D) = k8_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_relset_1)).
% 2.03/1.28  tff(c_6, plain, (![A_6, B_7]: (v1_relat_1(k2_zfmisc_1(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.03/1.28  tff(c_26, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.03/1.28  tff(c_29, plain, (![B_31, A_32]: (v1_relat_1(B_31) | ~m1_subset_1(B_31, k1_zfmisc_1(A_32)) | ~v1_relat_1(A_32))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.03/1.28  tff(c_32, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_3', '#skF_1'))), inference(resolution, [status(thm)], [c_26, c_29])).
% 2.03/1.28  tff(c_35, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_6, c_32])).
% 2.03/1.28  tff(c_8, plain, (![A_8, B_9]: (r1_tarski(k2_relat_1(k8_relat_1(A_8, B_9)), A_8) | ~v1_relat_1(B_9))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.03/1.28  tff(c_44, plain, (![C_42, A_43, B_44]: (v4_relat_1(C_42, A_43) | ~m1_subset_1(C_42, k1_zfmisc_1(k2_zfmisc_1(A_43, B_44))))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.03/1.28  tff(c_48, plain, (v4_relat_1('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_26, c_44])).
% 2.03/1.28  tff(c_12, plain, (![B_14, A_13]: (k7_relat_1(B_14, A_13)=B_14 | ~v4_relat_1(B_14, A_13) | ~v1_relat_1(B_14))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.03/1.28  tff(c_51, plain, (k7_relat_1('#skF_4', '#skF_3')='#skF_4' | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_48, c_12])).
% 2.03/1.28  tff(c_54, plain, (k7_relat_1('#skF_4', '#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_35, c_51])).
% 2.03/1.28  tff(c_64, plain, (![A_45, C_46, B_47]: (k8_relat_1(A_45, k7_relat_1(C_46, B_47))=k7_relat_1(k8_relat_1(A_45, C_46), B_47) | ~v1_relat_1(C_46))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.03/1.28  tff(c_79, plain, (![A_45]: (k7_relat_1(k8_relat_1(A_45, '#skF_4'), '#skF_3')=k8_relat_1(A_45, '#skF_4') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_54, c_64])).
% 2.03/1.28  tff(c_83, plain, (![A_45]: (k7_relat_1(k8_relat_1(A_45, '#skF_4'), '#skF_3')=k8_relat_1(A_45, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_35, c_79])).
% 2.03/1.28  tff(c_4, plain, (![A_4, B_5]: (v1_relat_1(k8_relat_1(A_4, B_5)) | ~v1_relat_1(B_5))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.03/1.28  tff(c_100, plain, (![A_50, C_51, B_52]: (v1_relat_1(k7_relat_1(k8_relat_1(A_50, C_51), B_52)) | ~v1_relat_1(k7_relat_1(C_51, B_52)) | ~v1_relat_1(C_51))), inference(superposition, [status(thm), theory('equality')], [c_64, c_4])).
% 2.03/1.28  tff(c_103, plain, (![A_45]: (v1_relat_1(k8_relat_1(A_45, '#skF_4')) | ~v1_relat_1(k7_relat_1('#skF_4', '#skF_3')) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_83, c_100])).
% 2.03/1.28  tff(c_108, plain, (![A_45]: (v1_relat_1(k8_relat_1(A_45, '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_35, c_35, c_54, c_103])).
% 2.03/1.28  tff(c_84, plain, (![A_48]: (k7_relat_1(k8_relat_1(A_48, '#skF_4'), '#skF_3')=k8_relat_1(A_48, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_35, c_79])).
% 2.03/1.28  tff(c_14, plain, (![B_16, A_15]: (r1_tarski(k1_relat_1(k7_relat_1(B_16, A_15)), A_15) | ~v1_relat_1(B_16))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.03/1.28  tff(c_93, plain, (![A_48]: (r1_tarski(k1_relat_1(k8_relat_1(A_48, '#skF_4')), '#skF_3') | ~v1_relat_1(k8_relat_1(A_48, '#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_84, c_14])).
% 2.03/1.28  tff(c_131, plain, (![A_48]: (r1_tarski(k1_relat_1(k8_relat_1(A_48, '#skF_4')), '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_108, c_93])).
% 2.03/1.28  tff(c_22, plain, (![C_26, A_24, B_25]: (m1_subset_1(C_26, k1_zfmisc_1(k2_zfmisc_1(A_24, B_25))) | ~r1_tarski(k2_relat_1(C_26), B_25) | ~r1_tarski(k1_relat_1(C_26), A_24) | ~v1_relat_1(C_26))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.03/1.28  tff(c_155, plain, (![A_61, B_62, C_63, D_64]: (k6_relset_1(A_61, B_62, C_63, D_64)=k8_relat_1(C_63, D_64) | ~m1_subset_1(D_64, k1_zfmisc_1(k2_zfmisc_1(A_61, B_62))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.03/1.28  tff(c_158, plain, (![C_63]: (k6_relset_1('#skF_3', '#skF_1', C_63, '#skF_4')=k8_relat_1(C_63, '#skF_4'))), inference(resolution, [status(thm)], [c_26, c_155])).
% 2.03/1.28  tff(c_24, plain, (~m1_subset_1(k6_relset_1('#skF_3', '#skF_1', '#skF_2', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.03/1.28  tff(c_181, plain, (~m1_subset_1(k8_relat_1('#skF_2', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_158, c_24])).
% 2.03/1.28  tff(c_193, plain, (~r1_tarski(k2_relat_1(k8_relat_1('#skF_2', '#skF_4')), '#skF_2') | ~r1_tarski(k1_relat_1(k8_relat_1('#skF_2', '#skF_4')), '#skF_3') | ~v1_relat_1(k8_relat_1('#skF_2', '#skF_4'))), inference(resolution, [status(thm)], [c_22, c_181])).
% 2.03/1.28  tff(c_196, plain, (~r1_tarski(k2_relat_1(k8_relat_1('#skF_2', '#skF_4')), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_108, c_131, c_193])).
% 2.03/1.28  tff(c_199, plain, (~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_8, c_196])).
% 2.03/1.28  tff(c_203, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_35, c_199])).
% 2.03/1.28  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.03/1.28  
% 2.03/1.28  Inference rules
% 2.03/1.28  ----------------------
% 2.03/1.28  #Ref     : 0
% 2.03/1.28  #Sup     : 38
% 2.03/1.28  #Fact    : 0
% 2.03/1.28  #Define  : 0
% 2.03/1.28  #Split   : 0
% 2.03/1.28  #Chain   : 0
% 2.03/1.28  #Close   : 0
% 2.03/1.28  
% 2.03/1.28  Ordering : KBO
% 2.03/1.28  
% 2.03/1.28  Simplification rules
% 2.03/1.28  ----------------------
% 2.03/1.28  #Subsume      : 1
% 2.03/1.28  #Demod        : 18
% 2.03/1.28  #Tautology    : 13
% 2.03/1.28  #SimpNegUnit  : 0
% 2.03/1.28  #BackRed      : 3
% 2.03/1.28  
% 2.03/1.28  #Partial instantiations: 0
% 2.03/1.28  #Strategies tried      : 1
% 2.03/1.28  
% 2.03/1.28  Timing (in seconds)
% 2.03/1.28  ----------------------
% 2.03/1.28  Preprocessing        : 0.29
% 2.03/1.28  Parsing              : 0.16
% 2.03/1.28  CNF conversion       : 0.02
% 2.03/1.28  Main loop            : 0.18
% 2.03/1.28  Inferencing          : 0.07
% 2.03/1.28  Reduction            : 0.06
% 2.03/1.28  Demodulation         : 0.04
% 2.03/1.28  BG Simplification    : 0.01
% 2.03/1.28  Subsumption          : 0.03
% 2.03/1.28  Abstraction          : 0.01
% 2.03/1.28  MUC search           : 0.00
% 2.03/1.28  Cooper               : 0.00
% 2.03/1.28  Total                : 0.50
% 2.03/1.28  Index Insertion      : 0.00
% 2.03/1.28  Index Deletion       : 0.00
% 2.03/1.28  Index Matching       : 0.00
% 2.03/1.28  BG Taut test         : 0.00
%------------------------------------------------------------------------------

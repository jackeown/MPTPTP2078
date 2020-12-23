%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:07:41 EST 2020

% Result     : Theorem 2.43s
% Output     : CNFRefutation 2.43s
% Verified   : 
% Statistics : Number of formulae       :   61 ( 133 expanded)
%              Number of leaves         :   30 (  57 expanded)
%              Depth                    :   13
%              Number of atoms          :   79 ( 208 expanded)
%              Number of equality atoms :    7 (  14 expanded)
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

tff(f_80,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(C,A)))
       => m1_subset_1(k6_relset_1(C,A,B,D),k1_zfmisc_1(k2_zfmisc_1(C,B))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_relset_1)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k2_relat_1(k8_relat_1(A,B)),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t116_relat_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => v1_relat_1(k8_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_relat_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k1_relat_1(k8_relat_1(A,B)),k1_relat_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l29_wellord1)).

tff(f_63,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k1_relat_1(k7_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_relat_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_75,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( ( r1_tarski(k1_relat_1(C),A)
          & r1_tarski(k2_relat_1(C),B) )
       => m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_relset_1)).

tff(f_67,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k6_relset_1(A,B,C,D) = k8_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_relset_1)).

tff(c_26,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_30,plain,(
    ! [C_33,A_34,B_35] :
      ( v1_relat_1(C_33)
      | ~ m1_subset_1(C_33,k1_zfmisc_1(k2_zfmisc_1(A_34,B_35))) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_34,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_26,c_30])).

tff(c_6,plain,(
    ! [A_6,B_7] :
      ( r1_tarski(k2_relat_1(k8_relat_1(A_6,B_7)),A_6)
      | ~ v1_relat_1(B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_4,plain,(
    ! [A_4,B_5] :
      ( v1_relat_1(k8_relat_1(A_4,B_5))
      | ~ v1_relat_1(B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_12,plain,(
    ! [A_12,B_13] :
      ( r1_tarski(k1_relat_1(k8_relat_1(A_12,B_13)),k1_relat_1(B_13))
      | ~ v1_relat_1(B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_35,plain,(
    ! [C_36,A_37,B_38] :
      ( v4_relat_1(C_36,A_37)
      | ~ m1_subset_1(C_36,k1_zfmisc_1(k2_zfmisc_1(A_37,B_38))) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_39,plain,(
    v4_relat_1('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_26,c_35])).

tff(c_40,plain,(
    ! [B_39,A_40] :
      ( k7_relat_1(B_39,A_40) = B_39
      | ~ v4_relat_1(B_39,A_40)
      | ~ v1_relat_1(B_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_43,plain,
    ( k7_relat_1('#skF_4','#skF_3') = '#skF_4'
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_39,c_40])).

tff(c_46,plain,(
    k7_relat_1('#skF_4','#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_43])).

tff(c_10,plain,(
    ! [B_11,A_10] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_11,A_10)),A_10)
      | ~ v1_relat_1(B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_50,plain,
    ( r1_tarski(k1_relat_1('#skF_4'),'#skF_3')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_10])).

tff(c_54,plain,(
    r1_tarski(k1_relat_1('#skF_4'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_50])).

tff(c_61,plain,(
    ! [A_44,C_45,B_46] :
      ( r1_tarski(A_44,C_45)
      | ~ r1_tarski(B_46,C_45)
      | ~ r1_tarski(A_44,B_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_75,plain,(
    ! [A_49] :
      ( r1_tarski(A_49,'#skF_3')
      | ~ r1_tarski(A_49,k1_relat_1('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_54,c_61])).

tff(c_79,plain,(
    ! [A_12] :
      ( r1_tarski(k1_relat_1(k8_relat_1(A_12,'#skF_4')),'#skF_3')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_12,c_75])).

tff(c_90,plain,(
    ! [A_12] : r1_tarski(k1_relat_1(k8_relat_1(A_12,'#skF_4')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_79])).

tff(c_349,plain,(
    ! [C_88,A_89,B_90] :
      ( m1_subset_1(C_88,k1_zfmisc_1(k2_zfmisc_1(A_89,B_90)))
      | ~ r1_tarski(k2_relat_1(C_88),B_90)
      | ~ r1_tarski(k1_relat_1(C_88),A_89)
      | ~ v1_relat_1(C_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_161,plain,(
    ! [A_65,B_66,C_67,D_68] :
      ( k6_relset_1(A_65,B_66,C_67,D_68) = k8_relat_1(C_67,D_68)
      | ~ m1_subset_1(D_68,k1_zfmisc_1(k2_zfmisc_1(A_65,B_66))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_164,plain,(
    ! [C_67] : k6_relset_1('#skF_3','#skF_1',C_67,'#skF_4') = k8_relat_1(C_67,'#skF_4') ),
    inference(resolution,[status(thm)],[c_26,c_161])).

tff(c_24,plain,(
    ~ m1_subset_1(k6_relset_1('#skF_3','#skF_1','#skF_2','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_165,plain,(
    ~ m1_subset_1(k8_relat_1('#skF_2','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_164,c_24])).

tff(c_352,plain,
    ( ~ r1_tarski(k2_relat_1(k8_relat_1('#skF_2','#skF_4')),'#skF_2')
    | ~ r1_tarski(k1_relat_1(k8_relat_1('#skF_2','#skF_4')),'#skF_3')
    | ~ v1_relat_1(k8_relat_1('#skF_2','#skF_4')) ),
    inference(resolution,[status(thm)],[c_349,c_165])).

tff(c_366,plain,
    ( ~ r1_tarski(k2_relat_1(k8_relat_1('#skF_2','#skF_4')),'#skF_2')
    | ~ v1_relat_1(k8_relat_1('#skF_2','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_352])).

tff(c_371,plain,(
    ~ v1_relat_1(k8_relat_1('#skF_2','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_366])).

tff(c_374,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_4,c_371])).

tff(c_378,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_374])).

tff(c_379,plain,(
    ~ r1_tarski(k2_relat_1(k8_relat_1('#skF_2','#skF_4')),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_366])).

tff(c_383,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_6,c_379])).

tff(c_387,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_383])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:02:52 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.43/1.34  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.43/1.35  
% 2.43/1.35  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.43/1.35  %$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k6_relset_1 > k8_relat_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.43/1.35  
% 2.43/1.35  %Foreground sorts:
% 2.43/1.35  
% 2.43/1.35  
% 2.43/1.35  %Background operators:
% 2.43/1.35  
% 2.43/1.35  
% 2.43/1.35  %Foreground operators:
% 2.43/1.35  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 2.43/1.35  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.43/1.35  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.43/1.35  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.43/1.35  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.43/1.35  tff(k6_relset_1, type, k6_relset_1: ($i * $i * $i * $i) > $i).
% 2.43/1.35  tff('#skF_2', type, '#skF_2': $i).
% 2.43/1.35  tff('#skF_3', type, '#skF_3': $i).
% 2.43/1.35  tff('#skF_1', type, '#skF_1': $i).
% 2.43/1.35  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.43/1.35  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.43/1.35  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.43/1.35  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.43/1.35  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.43/1.35  tff('#skF_4', type, '#skF_4': $i).
% 2.43/1.35  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.43/1.35  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.43/1.35  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.43/1.35  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.43/1.35  
% 2.43/1.36  tff(f_80, negated_conjecture, ~(![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(C, A))) => m1_subset_1(k6_relset_1(C, A, B, D), k1_zfmisc_1(k2_zfmisc_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_relset_1)).
% 2.43/1.36  tff(f_57, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.43/1.36  tff(f_39, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k2_relat_1(k8_relat_1(A, B)), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t116_relat_1)).
% 2.43/1.36  tff(f_35, axiom, (![A, B]: (v1_relat_1(B) => v1_relat_1(k8_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k8_relat_1)).
% 2.43/1.36  tff(f_53, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k8_relat_1(A, B)), k1_relat_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l29_wellord1)).
% 2.43/1.36  tff(f_63, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.43/1.36  tff(f_45, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t209_relat_1)).
% 2.43/1.36  tff(f_49, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k7_relat_1(B, A)), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t87_relat_1)).
% 2.43/1.36  tff(f_31, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 2.43/1.36  tff(f_75, axiom, (![A, B, C]: (v1_relat_1(C) => ((r1_tarski(k1_relat_1(C), A) & r1_tarski(k2_relat_1(C), B)) => m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_relset_1)).
% 2.43/1.36  tff(f_67, axiom, (![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k6_relset_1(A, B, C, D) = k8_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_relset_1)).
% 2.43/1.36  tff(c_26, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.43/1.36  tff(c_30, plain, (![C_33, A_34, B_35]: (v1_relat_1(C_33) | ~m1_subset_1(C_33, k1_zfmisc_1(k2_zfmisc_1(A_34, B_35))))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.43/1.36  tff(c_34, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_26, c_30])).
% 2.43/1.36  tff(c_6, plain, (![A_6, B_7]: (r1_tarski(k2_relat_1(k8_relat_1(A_6, B_7)), A_6) | ~v1_relat_1(B_7))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.43/1.36  tff(c_4, plain, (![A_4, B_5]: (v1_relat_1(k8_relat_1(A_4, B_5)) | ~v1_relat_1(B_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.43/1.36  tff(c_12, plain, (![A_12, B_13]: (r1_tarski(k1_relat_1(k8_relat_1(A_12, B_13)), k1_relat_1(B_13)) | ~v1_relat_1(B_13))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.43/1.36  tff(c_35, plain, (![C_36, A_37, B_38]: (v4_relat_1(C_36, A_37) | ~m1_subset_1(C_36, k1_zfmisc_1(k2_zfmisc_1(A_37, B_38))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.43/1.36  tff(c_39, plain, (v4_relat_1('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_26, c_35])).
% 2.43/1.36  tff(c_40, plain, (![B_39, A_40]: (k7_relat_1(B_39, A_40)=B_39 | ~v4_relat_1(B_39, A_40) | ~v1_relat_1(B_39))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.43/1.36  tff(c_43, plain, (k7_relat_1('#skF_4', '#skF_3')='#skF_4' | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_39, c_40])).
% 2.43/1.36  tff(c_46, plain, (k7_relat_1('#skF_4', '#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_34, c_43])).
% 2.43/1.36  tff(c_10, plain, (![B_11, A_10]: (r1_tarski(k1_relat_1(k7_relat_1(B_11, A_10)), A_10) | ~v1_relat_1(B_11))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.43/1.36  tff(c_50, plain, (r1_tarski(k1_relat_1('#skF_4'), '#skF_3') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_46, c_10])).
% 2.43/1.36  tff(c_54, plain, (r1_tarski(k1_relat_1('#skF_4'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_50])).
% 2.43/1.37  tff(c_61, plain, (![A_44, C_45, B_46]: (r1_tarski(A_44, C_45) | ~r1_tarski(B_46, C_45) | ~r1_tarski(A_44, B_46))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.43/1.37  tff(c_75, plain, (![A_49]: (r1_tarski(A_49, '#skF_3') | ~r1_tarski(A_49, k1_relat_1('#skF_4')))), inference(resolution, [status(thm)], [c_54, c_61])).
% 2.43/1.37  tff(c_79, plain, (![A_12]: (r1_tarski(k1_relat_1(k8_relat_1(A_12, '#skF_4')), '#skF_3') | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_12, c_75])).
% 2.43/1.37  tff(c_90, plain, (![A_12]: (r1_tarski(k1_relat_1(k8_relat_1(A_12, '#skF_4')), '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_79])).
% 2.43/1.37  tff(c_349, plain, (![C_88, A_89, B_90]: (m1_subset_1(C_88, k1_zfmisc_1(k2_zfmisc_1(A_89, B_90))) | ~r1_tarski(k2_relat_1(C_88), B_90) | ~r1_tarski(k1_relat_1(C_88), A_89) | ~v1_relat_1(C_88))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.43/1.37  tff(c_161, plain, (![A_65, B_66, C_67, D_68]: (k6_relset_1(A_65, B_66, C_67, D_68)=k8_relat_1(C_67, D_68) | ~m1_subset_1(D_68, k1_zfmisc_1(k2_zfmisc_1(A_65, B_66))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.43/1.37  tff(c_164, plain, (![C_67]: (k6_relset_1('#skF_3', '#skF_1', C_67, '#skF_4')=k8_relat_1(C_67, '#skF_4'))), inference(resolution, [status(thm)], [c_26, c_161])).
% 2.43/1.37  tff(c_24, plain, (~m1_subset_1(k6_relset_1('#skF_3', '#skF_1', '#skF_2', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.43/1.37  tff(c_165, plain, (~m1_subset_1(k8_relat_1('#skF_2', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_164, c_24])).
% 2.43/1.37  tff(c_352, plain, (~r1_tarski(k2_relat_1(k8_relat_1('#skF_2', '#skF_4')), '#skF_2') | ~r1_tarski(k1_relat_1(k8_relat_1('#skF_2', '#skF_4')), '#skF_3') | ~v1_relat_1(k8_relat_1('#skF_2', '#skF_4'))), inference(resolution, [status(thm)], [c_349, c_165])).
% 2.43/1.37  tff(c_366, plain, (~r1_tarski(k2_relat_1(k8_relat_1('#skF_2', '#skF_4')), '#skF_2') | ~v1_relat_1(k8_relat_1('#skF_2', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_90, c_352])).
% 2.43/1.37  tff(c_371, plain, (~v1_relat_1(k8_relat_1('#skF_2', '#skF_4'))), inference(splitLeft, [status(thm)], [c_366])).
% 2.43/1.37  tff(c_374, plain, (~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_4, c_371])).
% 2.43/1.37  tff(c_378, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_374])).
% 2.43/1.37  tff(c_379, plain, (~r1_tarski(k2_relat_1(k8_relat_1('#skF_2', '#skF_4')), '#skF_2')), inference(splitRight, [status(thm)], [c_366])).
% 2.43/1.37  tff(c_383, plain, (~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_6, c_379])).
% 2.43/1.37  tff(c_387, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_383])).
% 2.43/1.37  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.43/1.37  
% 2.43/1.37  Inference rules
% 2.43/1.37  ----------------------
% 2.43/1.37  #Ref     : 0
% 2.43/1.37  #Sup     : 73
% 2.43/1.37  #Fact    : 0
% 2.43/1.37  #Define  : 0
% 2.43/1.37  #Split   : 1
% 2.43/1.37  #Chain   : 0
% 2.43/1.37  #Close   : 0
% 2.43/1.37  
% 2.43/1.37  Ordering : KBO
% 2.43/1.37  
% 2.43/1.37  Simplification rules
% 2.43/1.37  ----------------------
% 2.43/1.37  #Subsume      : 3
% 2.43/1.37  #Demod        : 10
% 2.43/1.37  #Tautology    : 5
% 2.43/1.37  #SimpNegUnit  : 0
% 2.43/1.37  #BackRed      : 1
% 2.43/1.37  
% 2.43/1.37  #Partial instantiations: 0
% 2.43/1.37  #Strategies tried      : 1
% 2.43/1.37  
% 2.43/1.37  Timing (in seconds)
% 2.43/1.37  ----------------------
% 2.43/1.37  Preprocessing        : 0.33
% 2.43/1.37  Parsing              : 0.18
% 2.43/1.37  CNF conversion       : 0.02
% 2.43/1.37  Main loop            : 0.25
% 2.43/1.37  Inferencing          : 0.10
% 2.43/1.37  Reduction            : 0.06
% 2.43/1.37  Demodulation         : 0.05
% 2.43/1.37  BG Simplification    : 0.01
% 2.43/1.37  Subsumption          : 0.06
% 2.43/1.37  Abstraction          : 0.01
% 2.43/1.37  MUC search           : 0.00
% 2.43/1.37  Cooper               : 0.00
% 2.43/1.37  Total                : 0.61
% 2.43/1.37  Index Insertion      : 0.00
% 2.43/1.37  Index Deletion       : 0.00
% 2.43/1.37  Index Matching       : 0.00
% 2.43/1.37  BG Taut test         : 0.00
%------------------------------------------------------------------------------

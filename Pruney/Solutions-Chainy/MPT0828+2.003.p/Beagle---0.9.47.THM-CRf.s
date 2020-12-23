%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:07:17 EST 2020

% Result     : Theorem 2.62s
% Output     : CNFRefutation 2.73s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 112 expanded)
%              Number of leaves         :   29 (  50 expanded)
%              Depth                    :    9
%              Number of atoms          :   97 ( 206 expanded)
%              Number of equality atoms :   18 (  38 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

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

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_83,negated_conjecture,(
    ~ ! [A,B,C] :
        ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
       => ( r1_tarski(k6_relat_1(B),C)
         => ( B = k1_relset_1(B,A,C)
            & r1_tarski(B,k2_relset_1(B,A,C)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_relset_1)).

tff(f_60,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_56,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_52,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_48,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(A,B)
           => ( r1_tarski(k1_relat_1(A),k1_relat_1(B))
              & r1_tarski(k2_relat_1(A),k2_relat_1(B)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_relat_1)).

tff(f_74,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_66,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_70,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(c_38,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_366,plain,(
    ! [C_73,A_74,B_75] :
      ( v1_relat_1(C_73)
      | ~ m1_subset_1(C_73,k1_zfmisc_1(k2_zfmisc_1(A_74,B_75))) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_370,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_38,c_366])).

tff(c_36,plain,(
    r1_tarski(k6_relat_1('#skF_2'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_20,plain,(
    ! [A_9] : v1_relat_1(k6_relat_1(A_9)) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_18,plain,(
    ! [A_8] : k2_relat_1(k6_relat_1(A_8)) = A_8 ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_594,plain,(
    ! [A_110,B_111] :
      ( r1_tarski(k2_relat_1(A_110),k2_relat_1(B_111))
      | ~ r1_tarski(A_110,B_111)
      | ~ v1_relat_1(B_111)
      | ~ v1_relat_1(A_110) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_599,plain,(
    ! [A_8,B_111] :
      ( r1_tarski(A_8,k2_relat_1(B_111))
      | ~ r1_tarski(k6_relat_1(A_8),B_111)
      | ~ v1_relat_1(B_111)
      | ~ v1_relat_1(k6_relat_1(A_8)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_594])).

tff(c_626,plain,(
    ! [A_114,B_115] :
      ( r1_tarski(A_114,k2_relat_1(B_115))
      | ~ r1_tarski(k6_relat_1(A_114),B_115)
      | ~ v1_relat_1(B_115) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_599])).

tff(c_629,plain,
    ( r1_tarski('#skF_2',k2_relat_1('#skF_3'))
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_36,c_626])).

tff(c_636,plain,(
    r1_tarski('#skF_2',k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_370,c_629])).

tff(c_689,plain,(
    ! [A_120,B_121,C_122] :
      ( k2_relset_1(A_120,B_121,C_122) = k2_relat_1(C_122)
      | ~ m1_subset_1(C_122,k1_zfmisc_1(k2_zfmisc_1(A_120,B_121))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_693,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_38,c_689])).

tff(c_34,plain,
    ( ~ r1_tarski('#skF_2',k2_relset_1('#skF_2','#skF_1','#skF_3'))
    | k1_relset_1('#skF_2','#skF_1','#skF_3') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_72,plain,(
    k1_relset_1('#skF_2','#skF_1','#skF_3') != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_34])).

tff(c_73,plain,(
    ! [C_29,A_30,B_31] :
      ( v1_relat_1(C_29)
      | ~ m1_subset_1(C_29,k1_zfmisc_1(k2_zfmisc_1(A_30,B_31))) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_77,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_38,c_73])).

tff(c_108,plain,(
    ! [C_41,A_42,B_43] :
      ( v4_relat_1(C_41,A_42)
      | ~ m1_subset_1(C_41,k1_zfmisc_1(k2_zfmisc_1(A_42,B_43))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_112,plain,(
    v4_relat_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_38,c_108])).

tff(c_10,plain,(
    ! [B_4,A_3] :
      ( r1_tarski(k1_relat_1(B_4),A_3)
      | ~ v4_relat_1(B_4,A_3)
      | ~ v1_relat_1(B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_16,plain,(
    ! [A_8] : k1_relat_1(k6_relat_1(A_8)) = A_8 ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_137,plain,(
    ! [A_48,B_49] :
      ( r1_tarski(k1_relat_1(A_48),k1_relat_1(B_49))
      | ~ r1_tarski(A_48,B_49)
      | ~ v1_relat_1(B_49)
      | ~ v1_relat_1(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_145,plain,(
    ! [A_8,B_49] :
      ( r1_tarski(A_8,k1_relat_1(B_49))
      | ~ r1_tarski(k6_relat_1(A_8),B_49)
      | ~ v1_relat_1(B_49)
      | ~ v1_relat_1(k6_relat_1(A_8)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_137])).

tff(c_169,plain,(
    ! [A_52,B_53] :
      ( r1_tarski(A_52,k1_relat_1(B_53))
      | ~ r1_tarski(k6_relat_1(A_52),B_53)
      | ~ v1_relat_1(B_53) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_145])).

tff(c_172,plain,
    ( r1_tarski('#skF_2',k1_relat_1('#skF_3'))
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_36,c_169])).

tff(c_179,plain,(
    r1_tarski('#skF_2',k1_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_77,c_172])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_185,plain,
    ( k1_relat_1('#skF_3') = '#skF_2'
    | ~ r1_tarski(k1_relat_1('#skF_3'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_179,c_2])).

tff(c_186,plain,(
    ~ r1_tarski(k1_relat_1('#skF_3'),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_185])).

tff(c_189,plain,
    ( ~ v4_relat_1('#skF_3','#skF_2')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_10,c_186])).

tff(c_193,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_77,c_112,c_189])).

tff(c_194,plain,(
    k1_relat_1('#skF_3') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_185])).

tff(c_352,plain,(
    ! [A_70,B_71,C_72] :
      ( k1_relset_1(A_70,B_71,C_72) = k1_relat_1(C_72)
      | ~ m1_subset_1(C_72,k1_zfmisc_1(k2_zfmisc_1(A_70,B_71))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_355,plain,(
    k1_relset_1('#skF_2','#skF_1','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_38,c_352])).

tff(c_357,plain,(
    k1_relset_1('#skF_2','#skF_1','#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_194,c_355])).

tff(c_359,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_357])).

tff(c_360,plain,(
    ~ r1_tarski('#skF_2',k2_relset_1('#skF_2','#skF_1','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_694,plain,(
    ~ r1_tarski('#skF_2',k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_693,c_360])).

tff(c_697,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_636,c_694])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:40:53 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.62/1.34  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.62/1.35  
% 2.62/1.35  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.62/1.35  %$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 2.62/1.35  
% 2.62/1.35  %Foreground sorts:
% 2.62/1.35  
% 2.62/1.35  
% 2.62/1.35  %Background operators:
% 2.62/1.35  
% 2.62/1.35  
% 2.62/1.35  %Foreground operators:
% 2.62/1.35  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.62/1.35  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.62/1.35  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.62/1.35  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.62/1.35  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.62/1.35  tff('#skF_2', type, '#skF_2': $i).
% 2.62/1.35  tff('#skF_3', type, '#skF_3': $i).
% 2.62/1.35  tff('#skF_1', type, '#skF_1': $i).
% 2.62/1.35  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.62/1.35  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.62/1.35  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.62/1.35  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.62/1.35  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.62/1.35  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.62/1.35  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.62/1.35  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.62/1.35  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.62/1.35  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.62/1.35  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.62/1.35  
% 2.73/1.37  tff(f_83, negated_conjecture, ~(![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => (r1_tarski(k6_relat_1(B), C) => ((B = k1_relset_1(B, A, C)) & r1_tarski(B, k2_relset_1(B, A, C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_relset_1)).
% 2.73/1.37  tff(f_60, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.73/1.37  tff(f_56, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc3_funct_1)).
% 2.73/1.37  tff(f_52, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 2.73/1.37  tff(f_48, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(A, B) => (r1_tarski(k1_relat_1(A), k1_relat_1(B)) & r1_tarski(k2_relat_1(A), k2_relat_1(B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_relat_1)).
% 2.73/1.37  tff(f_74, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 2.73/1.37  tff(f_66, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.73/1.37  tff(f_37, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 2.73/1.37  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.73/1.37  tff(f_70, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.73/1.37  tff(c_38, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.73/1.37  tff(c_366, plain, (![C_73, A_74, B_75]: (v1_relat_1(C_73) | ~m1_subset_1(C_73, k1_zfmisc_1(k2_zfmisc_1(A_74, B_75))))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.73/1.37  tff(c_370, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_38, c_366])).
% 2.73/1.37  tff(c_36, plain, (r1_tarski(k6_relat_1('#skF_2'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.73/1.37  tff(c_20, plain, (![A_9]: (v1_relat_1(k6_relat_1(A_9)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.73/1.37  tff(c_18, plain, (![A_8]: (k2_relat_1(k6_relat_1(A_8))=A_8)), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.73/1.37  tff(c_594, plain, (![A_110, B_111]: (r1_tarski(k2_relat_1(A_110), k2_relat_1(B_111)) | ~r1_tarski(A_110, B_111) | ~v1_relat_1(B_111) | ~v1_relat_1(A_110))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.73/1.37  tff(c_599, plain, (![A_8, B_111]: (r1_tarski(A_8, k2_relat_1(B_111)) | ~r1_tarski(k6_relat_1(A_8), B_111) | ~v1_relat_1(B_111) | ~v1_relat_1(k6_relat_1(A_8)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_594])).
% 2.73/1.37  tff(c_626, plain, (![A_114, B_115]: (r1_tarski(A_114, k2_relat_1(B_115)) | ~r1_tarski(k6_relat_1(A_114), B_115) | ~v1_relat_1(B_115))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_599])).
% 2.73/1.37  tff(c_629, plain, (r1_tarski('#skF_2', k2_relat_1('#skF_3')) | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_36, c_626])).
% 2.73/1.37  tff(c_636, plain, (r1_tarski('#skF_2', k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_370, c_629])).
% 2.73/1.37  tff(c_689, plain, (![A_120, B_121, C_122]: (k2_relset_1(A_120, B_121, C_122)=k2_relat_1(C_122) | ~m1_subset_1(C_122, k1_zfmisc_1(k2_zfmisc_1(A_120, B_121))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.73/1.37  tff(c_693, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_38, c_689])).
% 2.73/1.37  tff(c_34, plain, (~r1_tarski('#skF_2', k2_relset_1('#skF_2', '#skF_1', '#skF_3')) | k1_relset_1('#skF_2', '#skF_1', '#skF_3')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.73/1.37  tff(c_72, plain, (k1_relset_1('#skF_2', '#skF_1', '#skF_3')!='#skF_2'), inference(splitLeft, [status(thm)], [c_34])).
% 2.73/1.37  tff(c_73, plain, (![C_29, A_30, B_31]: (v1_relat_1(C_29) | ~m1_subset_1(C_29, k1_zfmisc_1(k2_zfmisc_1(A_30, B_31))))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.73/1.37  tff(c_77, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_38, c_73])).
% 2.73/1.37  tff(c_108, plain, (![C_41, A_42, B_43]: (v4_relat_1(C_41, A_42) | ~m1_subset_1(C_41, k1_zfmisc_1(k2_zfmisc_1(A_42, B_43))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.73/1.37  tff(c_112, plain, (v4_relat_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_38, c_108])).
% 2.73/1.37  tff(c_10, plain, (![B_4, A_3]: (r1_tarski(k1_relat_1(B_4), A_3) | ~v4_relat_1(B_4, A_3) | ~v1_relat_1(B_4))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.73/1.37  tff(c_16, plain, (![A_8]: (k1_relat_1(k6_relat_1(A_8))=A_8)), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.73/1.37  tff(c_137, plain, (![A_48, B_49]: (r1_tarski(k1_relat_1(A_48), k1_relat_1(B_49)) | ~r1_tarski(A_48, B_49) | ~v1_relat_1(B_49) | ~v1_relat_1(A_48))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.73/1.37  tff(c_145, plain, (![A_8, B_49]: (r1_tarski(A_8, k1_relat_1(B_49)) | ~r1_tarski(k6_relat_1(A_8), B_49) | ~v1_relat_1(B_49) | ~v1_relat_1(k6_relat_1(A_8)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_137])).
% 2.73/1.37  tff(c_169, plain, (![A_52, B_53]: (r1_tarski(A_52, k1_relat_1(B_53)) | ~r1_tarski(k6_relat_1(A_52), B_53) | ~v1_relat_1(B_53))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_145])).
% 2.73/1.37  tff(c_172, plain, (r1_tarski('#skF_2', k1_relat_1('#skF_3')) | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_36, c_169])).
% 2.73/1.37  tff(c_179, plain, (r1_tarski('#skF_2', k1_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_77, c_172])).
% 2.73/1.37  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.73/1.37  tff(c_185, plain, (k1_relat_1('#skF_3')='#skF_2' | ~r1_tarski(k1_relat_1('#skF_3'), '#skF_2')), inference(resolution, [status(thm)], [c_179, c_2])).
% 2.73/1.37  tff(c_186, plain, (~r1_tarski(k1_relat_1('#skF_3'), '#skF_2')), inference(splitLeft, [status(thm)], [c_185])).
% 2.73/1.37  tff(c_189, plain, (~v4_relat_1('#skF_3', '#skF_2') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_10, c_186])).
% 2.73/1.37  tff(c_193, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_77, c_112, c_189])).
% 2.73/1.37  tff(c_194, plain, (k1_relat_1('#skF_3')='#skF_2'), inference(splitRight, [status(thm)], [c_185])).
% 2.73/1.37  tff(c_352, plain, (![A_70, B_71, C_72]: (k1_relset_1(A_70, B_71, C_72)=k1_relat_1(C_72) | ~m1_subset_1(C_72, k1_zfmisc_1(k2_zfmisc_1(A_70, B_71))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.73/1.37  tff(c_355, plain, (k1_relset_1('#skF_2', '#skF_1', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_38, c_352])).
% 2.73/1.37  tff(c_357, plain, (k1_relset_1('#skF_2', '#skF_1', '#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_194, c_355])).
% 2.73/1.37  tff(c_359, plain, $false, inference(negUnitSimplification, [status(thm)], [c_72, c_357])).
% 2.73/1.37  tff(c_360, plain, (~r1_tarski('#skF_2', k2_relset_1('#skF_2', '#skF_1', '#skF_3'))), inference(splitRight, [status(thm)], [c_34])).
% 2.73/1.37  tff(c_694, plain, (~r1_tarski('#skF_2', k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_693, c_360])).
% 2.73/1.37  tff(c_697, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_636, c_694])).
% 2.73/1.37  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.73/1.37  
% 2.73/1.37  Inference rules
% 2.73/1.37  ----------------------
% 2.73/1.37  #Ref     : 0
% 2.73/1.37  #Sup     : 125
% 2.73/1.37  #Fact    : 0
% 2.73/1.37  #Define  : 0
% 2.73/1.37  #Split   : 4
% 2.73/1.37  #Chain   : 0
% 2.73/1.37  #Close   : 0
% 2.73/1.37  
% 2.73/1.37  Ordering : KBO
% 2.73/1.37  
% 2.73/1.37  Simplification rules
% 2.73/1.37  ----------------------
% 2.73/1.37  #Subsume      : 10
% 2.73/1.37  #Demod        : 110
% 2.73/1.37  #Tautology    : 48
% 2.73/1.37  #SimpNegUnit  : 1
% 2.73/1.37  #BackRed      : 2
% 2.73/1.37  
% 2.73/1.37  #Partial instantiations: 0
% 2.73/1.37  #Strategies tried      : 1
% 2.73/1.37  
% 2.73/1.37  Timing (in seconds)
% 2.73/1.37  ----------------------
% 2.73/1.37  Preprocessing        : 0.30
% 2.73/1.37  Parsing              : 0.16
% 2.73/1.37  CNF conversion       : 0.02
% 2.73/1.37  Main loop            : 0.30
% 2.73/1.37  Inferencing          : 0.12
% 2.73/1.37  Reduction            : 0.09
% 2.73/1.37  Demodulation         : 0.07
% 2.73/1.37  BG Simplification    : 0.01
% 2.73/1.37  Subsumption          : 0.06
% 2.73/1.37  Abstraction          : 0.02
% 2.73/1.37  MUC search           : 0.00
% 2.73/1.37  Cooper               : 0.00
% 2.73/1.37  Total                : 0.63
% 2.73/1.37  Index Insertion      : 0.00
% 2.73/1.37  Index Deletion       : 0.00
% 2.73/1.37  Index Matching       : 0.00
% 2.73/1.37  BG Taut test         : 0.00
%------------------------------------------------------------------------------

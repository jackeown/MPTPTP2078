%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:07:25 EST 2020

% Result     : Theorem 2.60s
% Output     : CNFRefutation 2.60s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 130 expanded)
%              Number of leaves         :   30 (  56 expanded)
%              Depth                    :    9
%              Number of atoms          :   98 ( 229 expanded)
%              Number of equality atoms :   24 (  67 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

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

tff(f_85,negated_conjecture,(
    ~ ! [A,B,C] :
        ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
       => ( r1_tarski(k6_relat_1(B),C)
         => ( r1_tarski(B,k1_relset_1(A,B,C))
            & B = k2_relset_1(A,B,C) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_relset_1)).

tff(f_68,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_76,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( r1_tarski(k6_relat_1(C),D)
       => ( r1_tarski(C,k1_relset_1(A,B,D))
          & r1_tarski(C,k2_relset_1(A,B,D)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_relset_1)).

tff(f_46,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_42,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_32,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_64,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_40,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k5_relat_1(k6_relat_1(A),B) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_relat_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k2_relat_1(B),A)
       => k5_relat_1(B,k6_relat_1(A)) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_relat_1)).

tff(c_34,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_467,plain,(
    ! [A_103,B_104,C_105] :
      ( k2_relset_1(A_103,B_104,C_105) = k2_relat_1(C_105)
      | ~ m1_subset_1(C_105,k1_zfmisc_1(k2_zfmisc_1(A_103,B_104))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_471,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_467])).

tff(c_30,plain,
    ( k2_relset_1('#skF_1','#skF_2','#skF_3') != '#skF_2'
    | ~ r1_tarski('#skF_2',k1_relset_1('#skF_1','#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_67,plain,(
    ~ r1_tarski('#skF_2',k1_relset_1('#skF_1','#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_30])).

tff(c_32,plain,(
    r1_tarski(k6_relat_1('#skF_2'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_320,plain,(
    ! [C_73,A_74,B_75,D_76] :
      ( r1_tarski(C_73,k1_relset_1(A_74,B_75,D_76))
      | ~ r1_tarski(k6_relat_1(C_73),D_76)
      | ~ m1_subset_1(D_76,k1_zfmisc_1(k2_zfmisc_1(A_74,B_75))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_347,plain,(
    ! [A_78,B_79] :
      ( r1_tarski('#skF_2',k1_relset_1(A_78,B_79,'#skF_3'))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(A_78,B_79))) ) ),
    inference(resolution,[status(thm)],[c_32,c_320])).

tff(c_350,plain,(
    r1_tarski('#skF_2',k1_relset_1('#skF_1','#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_34,c_347])).

tff(c_354,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_67,c_350])).

tff(c_355,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_472,plain,(
    k2_relat_1('#skF_3') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_471,c_355])).

tff(c_12,plain,(
    ! [A_9] : k1_relat_1(k6_relat_1(A_9)) = A_9 ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_10,plain,(
    ! [A_7,B_8] : v1_relat_1(k2_zfmisc_1(A_7,B_8)) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_55,plain,(
    ! [B_29,A_30] :
      ( v1_relat_1(B_29)
      | ~ m1_subset_1(B_29,k1_zfmisc_1(A_30))
      | ~ v1_relat_1(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_58,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_34,c_55])).

tff(c_61,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_58])).

tff(c_364,plain,(
    ! [C_84,B_85,A_86] :
      ( v5_relat_1(C_84,B_85)
      | ~ m1_subset_1(C_84,k1_zfmisc_1(k2_zfmisc_1(A_86,B_85))) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_368,plain,(
    v5_relat_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_34,c_364])).

tff(c_6,plain,(
    ! [B_5,A_4] :
      ( r1_tarski(k2_relat_1(B_5),A_4)
      | ~ v5_relat_1(B_5,A_4)
      | ~ v1_relat_1(B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_484,plain,(
    ! [C_108,A_109,B_110,D_111] :
      ( r1_tarski(C_108,k2_relset_1(A_109,B_110,D_111))
      | ~ r1_tarski(k6_relat_1(C_108),D_111)
      | ~ m1_subset_1(D_111,k1_zfmisc_1(k2_zfmisc_1(A_109,B_110))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_488,plain,(
    ! [A_112,B_113] :
      ( r1_tarski('#skF_2',k2_relset_1(A_112,B_113,'#skF_3'))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(A_112,B_113))) ) ),
    inference(resolution,[status(thm)],[c_32,c_484])).

tff(c_491,plain,(
    r1_tarski('#skF_2',k2_relset_1('#skF_1','#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_34,c_488])).

tff(c_493,plain,(
    r1_tarski('#skF_2',k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_471,c_491])).

tff(c_8,plain,(
    ! [A_6] : v1_relat_1(k6_relat_1(A_6)) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_425,plain,(
    ! [A_97,B_98] :
      ( k5_relat_1(k6_relat_1(A_97),B_98) = B_98
      | ~ r1_tarski(k1_relat_1(B_98),A_97)
      | ~ v1_relat_1(B_98) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_428,plain,(
    ! [A_97,A_9] :
      ( k5_relat_1(k6_relat_1(A_97),k6_relat_1(A_9)) = k6_relat_1(A_9)
      | ~ r1_tarski(A_9,A_97)
      | ~ v1_relat_1(k6_relat_1(A_9)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_425])).

tff(c_431,plain,(
    ! [A_99,A_100] :
      ( k5_relat_1(k6_relat_1(A_99),k6_relat_1(A_100)) = k6_relat_1(A_100)
      | ~ r1_tarski(A_100,A_99) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_428])).

tff(c_14,plain,(
    ! [A_9] : k2_relat_1(k6_relat_1(A_9)) = A_9 ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_384,plain,(
    ! [B_91,A_92] :
      ( k5_relat_1(B_91,k6_relat_1(A_92)) = B_91
      | ~ r1_tarski(k2_relat_1(B_91),A_92)
      | ~ v1_relat_1(B_91) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_390,plain,(
    ! [A_9,A_92] :
      ( k5_relat_1(k6_relat_1(A_9),k6_relat_1(A_92)) = k6_relat_1(A_9)
      | ~ r1_tarski(A_9,A_92)
      | ~ v1_relat_1(k6_relat_1(A_9)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_384])).

tff(c_393,plain,(
    ! [A_9,A_92] :
      ( k5_relat_1(k6_relat_1(A_9),k6_relat_1(A_92)) = k6_relat_1(A_9)
      | ~ r1_tarski(A_9,A_92) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_390])).

tff(c_437,plain,(
    ! [A_99,A_100] :
      ( k6_relat_1(A_99) = k6_relat_1(A_100)
      | ~ r1_tarski(A_99,A_100)
      | ~ r1_tarski(A_100,A_99) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_431,c_393])).

tff(c_496,plain,
    ( k6_relat_1(k2_relat_1('#skF_3')) = k6_relat_1('#skF_2')
    | ~ r1_tarski(k2_relat_1('#skF_3'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_493,c_437])).

tff(c_497,plain,(
    ~ r1_tarski(k2_relat_1('#skF_3'),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_496])).

tff(c_500,plain,
    ( ~ v5_relat_1('#skF_3','#skF_2')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_6,c_497])).

tff(c_504,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_61,c_368,c_500])).

tff(c_505,plain,(
    k6_relat_1(k2_relat_1('#skF_3')) = k6_relat_1('#skF_2') ),
    inference(splitRight,[status(thm)],[c_496])).

tff(c_553,plain,(
    k1_relat_1(k6_relat_1('#skF_2')) = k2_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_505,c_12])).

tff(c_564,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_553])).

tff(c_566,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_472,c_564])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n021.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 12:58:49 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.60/1.38  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.60/1.39  
% 2.60/1.39  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.60/1.39  %$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 2.60/1.39  
% 2.60/1.39  %Foreground sorts:
% 2.60/1.39  
% 2.60/1.39  
% 2.60/1.39  %Background operators:
% 2.60/1.39  
% 2.60/1.39  
% 2.60/1.39  %Foreground operators:
% 2.60/1.39  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.60/1.39  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.60/1.39  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.60/1.39  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.60/1.39  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.60/1.39  tff('#skF_2', type, '#skF_2': $i).
% 2.60/1.39  tff('#skF_3', type, '#skF_3': $i).
% 2.60/1.39  tff('#skF_1', type, '#skF_1': $i).
% 2.60/1.39  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.60/1.39  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.60/1.39  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.60/1.39  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.60/1.39  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.60/1.39  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.60/1.39  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.60/1.39  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.60/1.39  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.60/1.39  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.60/1.39  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.60/1.39  
% 2.60/1.41  tff(f_85, negated_conjecture, ~(![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (r1_tarski(k6_relat_1(B), C) => (r1_tarski(B, k1_relset_1(A, B, C)) & (B = k2_relset_1(A, B, C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t32_relset_1)).
% 2.60/1.41  tff(f_68, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 2.60/1.41  tff(f_76, axiom, (![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (r1_tarski(k6_relat_1(C), D) => (r1_tarski(C, k1_relset_1(A, B, D)) & r1_tarski(C, k2_relset_1(A, B, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t30_relset_1)).
% 2.60/1.41  tff(f_46, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 2.60/1.41  tff(f_42, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.60/1.41  tff(f_32, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.60/1.41  tff(f_64, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.60/1.41  tff(f_38, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 2.60/1.41  tff(f_40, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 2.60/1.41  tff(f_52, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k5_relat_1(k6_relat_1(A), B) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t77_relat_1)).
% 2.60/1.41  tff(f_58, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k5_relat_1(B, k6_relat_1(A)) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_relat_1)).
% 2.60/1.41  tff(c_34, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.60/1.41  tff(c_467, plain, (![A_103, B_104, C_105]: (k2_relset_1(A_103, B_104, C_105)=k2_relat_1(C_105) | ~m1_subset_1(C_105, k1_zfmisc_1(k2_zfmisc_1(A_103, B_104))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.60/1.41  tff(c_471, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_34, c_467])).
% 2.60/1.41  tff(c_30, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2' | ~r1_tarski('#skF_2', k1_relset_1('#skF_1', '#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.60/1.41  tff(c_67, plain, (~r1_tarski('#skF_2', k1_relset_1('#skF_1', '#skF_2', '#skF_3'))), inference(splitLeft, [status(thm)], [c_30])).
% 2.60/1.41  tff(c_32, plain, (r1_tarski(k6_relat_1('#skF_2'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.60/1.41  tff(c_320, plain, (![C_73, A_74, B_75, D_76]: (r1_tarski(C_73, k1_relset_1(A_74, B_75, D_76)) | ~r1_tarski(k6_relat_1(C_73), D_76) | ~m1_subset_1(D_76, k1_zfmisc_1(k2_zfmisc_1(A_74, B_75))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.60/1.41  tff(c_347, plain, (![A_78, B_79]: (r1_tarski('#skF_2', k1_relset_1(A_78, B_79, '#skF_3')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(A_78, B_79))))), inference(resolution, [status(thm)], [c_32, c_320])).
% 2.60/1.41  tff(c_350, plain, (r1_tarski('#skF_2', k1_relset_1('#skF_1', '#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_34, c_347])).
% 2.60/1.41  tff(c_354, plain, $false, inference(negUnitSimplification, [status(thm)], [c_67, c_350])).
% 2.60/1.41  tff(c_355, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2'), inference(splitRight, [status(thm)], [c_30])).
% 2.60/1.41  tff(c_472, plain, (k2_relat_1('#skF_3')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_471, c_355])).
% 2.60/1.41  tff(c_12, plain, (![A_9]: (k1_relat_1(k6_relat_1(A_9))=A_9)), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.60/1.41  tff(c_10, plain, (![A_7, B_8]: (v1_relat_1(k2_zfmisc_1(A_7, B_8)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.60/1.41  tff(c_55, plain, (![B_29, A_30]: (v1_relat_1(B_29) | ~m1_subset_1(B_29, k1_zfmisc_1(A_30)) | ~v1_relat_1(A_30))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.60/1.41  tff(c_58, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_34, c_55])).
% 2.60/1.41  tff(c_61, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_10, c_58])).
% 2.60/1.41  tff(c_364, plain, (![C_84, B_85, A_86]: (v5_relat_1(C_84, B_85) | ~m1_subset_1(C_84, k1_zfmisc_1(k2_zfmisc_1(A_86, B_85))))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.60/1.41  tff(c_368, plain, (v5_relat_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_34, c_364])).
% 2.60/1.41  tff(c_6, plain, (![B_5, A_4]: (r1_tarski(k2_relat_1(B_5), A_4) | ~v5_relat_1(B_5, A_4) | ~v1_relat_1(B_5))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.60/1.41  tff(c_484, plain, (![C_108, A_109, B_110, D_111]: (r1_tarski(C_108, k2_relset_1(A_109, B_110, D_111)) | ~r1_tarski(k6_relat_1(C_108), D_111) | ~m1_subset_1(D_111, k1_zfmisc_1(k2_zfmisc_1(A_109, B_110))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.60/1.41  tff(c_488, plain, (![A_112, B_113]: (r1_tarski('#skF_2', k2_relset_1(A_112, B_113, '#skF_3')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(A_112, B_113))))), inference(resolution, [status(thm)], [c_32, c_484])).
% 2.60/1.41  tff(c_491, plain, (r1_tarski('#skF_2', k2_relset_1('#skF_1', '#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_34, c_488])).
% 2.60/1.41  tff(c_493, plain, (r1_tarski('#skF_2', k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_471, c_491])).
% 2.60/1.41  tff(c_8, plain, (![A_6]: (v1_relat_1(k6_relat_1(A_6)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.60/1.41  tff(c_425, plain, (![A_97, B_98]: (k5_relat_1(k6_relat_1(A_97), B_98)=B_98 | ~r1_tarski(k1_relat_1(B_98), A_97) | ~v1_relat_1(B_98))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.60/1.41  tff(c_428, plain, (![A_97, A_9]: (k5_relat_1(k6_relat_1(A_97), k6_relat_1(A_9))=k6_relat_1(A_9) | ~r1_tarski(A_9, A_97) | ~v1_relat_1(k6_relat_1(A_9)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_425])).
% 2.60/1.41  tff(c_431, plain, (![A_99, A_100]: (k5_relat_1(k6_relat_1(A_99), k6_relat_1(A_100))=k6_relat_1(A_100) | ~r1_tarski(A_100, A_99))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_428])).
% 2.60/1.41  tff(c_14, plain, (![A_9]: (k2_relat_1(k6_relat_1(A_9))=A_9)), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.60/1.41  tff(c_384, plain, (![B_91, A_92]: (k5_relat_1(B_91, k6_relat_1(A_92))=B_91 | ~r1_tarski(k2_relat_1(B_91), A_92) | ~v1_relat_1(B_91))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.60/1.41  tff(c_390, plain, (![A_9, A_92]: (k5_relat_1(k6_relat_1(A_9), k6_relat_1(A_92))=k6_relat_1(A_9) | ~r1_tarski(A_9, A_92) | ~v1_relat_1(k6_relat_1(A_9)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_384])).
% 2.60/1.41  tff(c_393, plain, (![A_9, A_92]: (k5_relat_1(k6_relat_1(A_9), k6_relat_1(A_92))=k6_relat_1(A_9) | ~r1_tarski(A_9, A_92))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_390])).
% 2.60/1.41  tff(c_437, plain, (![A_99, A_100]: (k6_relat_1(A_99)=k6_relat_1(A_100) | ~r1_tarski(A_99, A_100) | ~r1_tarski(A_100, A_99))), inference(superposition, [status(thm), theory('equality')], [c_431, c_393])).
% 2.60/1.41  tff(c_496, plain, (k6_relat_1(k2_relat_1('#skF_3'))=k6_relat_1('#skF_2') | ~r1_tarski(k2_relat_1('#skF_3'), '#skF_2')), inference(resolution, [status(thm)], [c_493, c_437])).
% 2.60/1.41  tff(c_497, plain, (~r1_tarski(k2_relat_1('#skF_3'), '#skF_2')), inference(splitLeft, [status(thm)], [c_496])).
% 2.60/1.41  tff(c_500, plain, (~v5_relat_1('#skF_3', '#skF_2') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_6, c_497])).
% 2.60/1.41  tff(c_504, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_61, c_368, c_500])).
% 2.60/1.41  tff(c_505, plain, (k6_relat_1(k2_relat_1('#skF_3'))=k6_relat_1('#skF_2')), inference(splitRight, [status(thm)], [c_496])).
% 2.60/1.41  tff(c_553, plain, (k1_relat_1(k6_relat_1('#skF_2'))=k2_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_505, c_12])).
% 2.60/1.41  tff(c_564, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_12, c_553])).
% 2.60/1.41  tff(c_566, plain, $false, inference(negUnitSimplification, [status(thm)], [c_472, c_564])).
% 2.60/1.41  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.60/1.41  
% 2.60/1.41  Inference rules
% 2.60/1.41  ----------------------
% 2.60/1.41  #Ref     : 0
% 2.60/1.41  #Sup     : 118
% 2.60/1.41  #Fact    : 0
% 2.60/1.41  #Define  : 0
% 2.60/1.41  #Split   : 6
% 2.60/1.41  #Chain   : 0
% 2.60/1.41  #Close   : 0
% 2.60/1.41  
% 2.60/1.41  Ordering : KBO
% 2.60/1.41  
% 2.60/1.41  Simplification rules
% 2.60/1.41  ----------------------
% 2.60/1.41  #Subsume      : 7
% 2.60/1.41  #Demod        : 59
% 2.60/1.41  #Tautology    : 48
% 2.60/1.41  #SimpNegUnit  : 2
% 2.60/1.41  #BackRed      : 5
% 2.60/1.41  
% 2.60/1.41  #Partial instantiations: 0
% 2.60/1.41  #Strategies tried      : 1
% 2.60/1.41  
% 2.60/1.41  Timing (in seconds)
% 2.60/1.41  ----------------------
% 2.60/1.41  Preprocessing        : 0.32
% 2.60/1.41  Parsing              : 0.18
% 2.60/1.41  CNF conversion       : 0.02
% 2.60/1.41  Main loop            : 0.30
% 2.60/1.41  Inferencing          : 0.12
% 2.60/1.41  Reduction            : 0.09
% 2.60/1.41  Demodulation         : 0.06
% 2.60/1.41  BG Simplification    : 0.02
% 2.60/1.41  Subsumption          : 0.05
% 2.60/1.41  Abstraction          : 0.02
% 2.60/1.41  MUC search           : 0.00
% 2.60/1.41  Cooper               : 0.00
% 2.60/1.41  Total                : 0.65
% 2.60/1.41  Index Insertion      : 0.00
% 2.60/1.41  Index Deletion       : 0.00
% 2.60/1.41  Index Matching       : 0.00
% 2.60/1.41  BG Taut test         : 0.00
%------------------------------------------------------------------------------

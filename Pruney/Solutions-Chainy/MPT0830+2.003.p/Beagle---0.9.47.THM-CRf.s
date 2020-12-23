%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:07:26 EST 2020

% Result     : Theorem 2.42s
% Output     : CNFRefutation 2.71s
% Verified   : 
% Statistics : Number of formulae       :   63 ( 114 expanded)
%              Number of leaves         :   29 (  49 expanded)
%              Depth                    :    9
%              Number of atoms          :   89 ( 188 expanded)
%              Number of equality atoms :    3 (  12 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k5_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k5_relset_1,type,(
    k5_relset_1: ( $i * $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

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

tff(f_83,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,C)))
       => m1_subset_1(k5_relset_1(A,C,D,B),k1_zfmisc_1(k2_zfmisc_1(B,C))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_relset_1)).

tff(f_54,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k1_relat_1(k7_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_relat_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k7_relat_1(B,A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_relat_1)).

tff(f_78,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,C)))
     => ( r1_tarski(A,D)
       => m1_subset_1(A,k1_zfmisc_1(k2_zfmisc_1(B,C))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_relset_1)).

tff(f_60,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_36,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_72,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( ( r1_tarski(k1_relat_1(C),A)
          & r1_tarski(k2_relat_1(C),B) )
       => m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_relset_1)).

tff(f_64,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k5_relset_1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k5_relset_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(c_30,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_42,plain,(
    ! [C_35,A_36,B_37] :
      ( v1_relat_1(C_35)
      | ~ m1_subset_1(C_35,k1_zfmisc_1(k2_zfmisc_1(A_36,B_37))) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_51,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_30,c_42])).

tff(c_12,plain,(
    ! [B_9,A_8] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_9,A_8)),A_8)
      | ~ v1_relat_1(B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_14,plain,(
    ! [B_11,A_10] :
      ( r1_tarski(k7_relat_1(B_11,A_10),B_11)
      | ~ v1_relat_1(B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_201,plain,(
    ! [A_78,B_79,C_80,D_81] :
      ( m1_subset_1(A_78,k1_zfmisc_1(k2_zfmisc_1(B_79,C_80)))
      | ~ r1_tarski(A_78,D_81)
      | ~ m1_subset_1(D_81,k1_zfmisc_1(k2_zfmisc_1(B_79,C_80))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_333,plain,(
    ! [B_125,A_126,B_127,C_128] :
      ( m1_subset_1(k7_relat_1(B_125,A_126),k1_zfmisc_1(k2_zfmisc_1(B_127,C_128)))
      | ~ m1_subset_1(B_125,k1_zfmisc_1(k2_zfmisc_1(B_127,C_128)))
      | ~ v1_relat_1(B_125) ) ),
    inference(resolution,[status(thm)],[c_14,c_201])).

tff(c_18,plain,(
    ! [C_17,B_16,A_15] :
      ( v5_relat_1(C_17,B_16)
      | ~ m1_subset_1(C_17,k1_zfmisc_1(k2_zfmisc_1(A_15,B_16))) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_492,plain,(
    ! [B_155,A_156,C_157,B_158] :
      ( v5_relat_1(k7_relat_1(B_155,A_156),C_157)
      | ~ m1_subset_1(B_155,k1_zfmisc_1(k2_zfmisc_1(B_158,C_157)))
      | ~ v1_relat_1(B_155) ) ),
    inference(resolution,[status(thm)],[c_333,c_18])).

tff(c_503,plain,(
    ! [A_156] :
      ( v5_relat_1(k7_relat_1('#skF_4',A_156),'#skF_3')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_30,c_492])).

tff(c_510,plain,(
    ! [A_156] : v5_relat_1(k7_relat_1('#skF_4',A_156),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_51,c_503])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( m1_subset_1(A_1,k1_zfmisc_1(B_2))
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_63,plain,(
    ! [B_41,A_42] :
      ( v1_relat_1(B_41)
      | ~ m1_subset_1(B_41,k1_zfmisc_1(A_42))
      | ~ v1_relat_1(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_77,plain,(
    ! [A_43,B_44] :
      ( v1_relat_1(A_43)
      | ~ v1_relat_1(B_44)
      | ~ r1_tarski(A_43,B_44) ) ),
    inference(resolution,[status(thm)],[c_4,c_63])).

tff(c_86,plain,(
    ! [B_11,A_10] :
      ( v1_relat_1(k7_relat_1(B_11,A_10))
      | ~ v1_relat_1(B_11) ) ),
    inference(resolution,[status(thm)],[c_14,c_77])).

tff(c_222,plain,(
    ! [C_87,A_88,B_89] :
      ( m1_subset_1(C_87,k1_zfmisc_1(k2_zfmisc_1(A_88,B_89)))
      | ~ r1_tarski(k2_relat_1(C_87),B_89)
      | ~ r1_tarski(k1_relat_1(C_87),A_88)
      | ~ v1_relat_1(C_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_178,plain,(
    ! [A_73,B_74,C_75,D_76] :
      ( k5_relset_1(A_73,B_74,C_75,D_76) = k7_relat_1(C_75,D_76)
      | ~ m1_subset_1(C_75,k1_zfmisc_1(k2_zfmisc_1(A_73,B_74))) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_185,plain,(
    ! [D_76] : k5_relset_1('#skF_1','#skF_3','#skF_4',D_76) = k7_relat_1('#skF_4',D_76) ),
    inference(resolution,[status(thm)],[c_30,c_178])).

tff(c_28,plain,(
    ~ m1_subset_1(k5_relset_1('#skF_1','#skF_3','#skF_4','#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_187,plain,(
    ~ m1_subset_1(k7_relat_1('#skF_4','#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_185,c_28])).

tff(c_243,plain,
    ( ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_4','#skF_2')),'#skF_3')
    | ~ r1_tarski(k1_relat_1(k7_relat_1('#skF_4','#skF_2')),'#skF_2')
    | ~ v1_relat_1(k7_relat_1('#skF_4','#skF_2')) ),
    inference(resolution,[status(thm)],[c_222,c_187])).

tff(c_363,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_4','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_243])).

tff(c_366,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_86,c_363])).

tff(c_370,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_51,c_366])).

tff(c_372,plain,(
    v1_relat_1(k7_relat_1('#skF_4','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_243])).

tff(c_10,plain,(
    ! [B_7,A_6] :
      ( r1_tarski(k2_relat_1(B_7),A_6)
      | ~ v5_relat_1(B_7,A_6)
      | ~ v1_relat_1(B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_371,plain,
    ( ~ r1_tarski(k1_relat_1(k7_relat_1('#skF_4','#skF_2')),'#skF_2')
    | ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_4','#skF_2')),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_243])).

tff(c_408,plain,(
    ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_4','#skF_2')),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_371])).

tff(c_411,plain,
    ( ~ v5_relat_1(k7_relat_1('#skF_4','#skF_2'),'#skF_3')
    | ~ v1_relat_1(k7_relat_1('#skF_4','#skF_2')) ),
    inference(resolution,[status(thm)],[c_10,c_408])).

tff(c_414,plain,(
    ~ v5_relat_1(k7_relat_1('#skF_4','#skF_2'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_372,c_411])).

tff(c_513,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_510,c_414])).

tff(c_514,plain,(
    ~ r1_tarski(k1_relat_1(k7_relat_1('#skF_4','#skF_2')),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_371])).

tff(c_518,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_12,c_514])).

tff(c_522,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_51,c_518])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:34:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.42/1.35  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.42/1.36  
% 2.42/1.36  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.42/1.36  %$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k5_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.42/1.36  
% 2.42/1.36  %Foreground sorts:
% 2.42/1.36  
% 2.42/1.36  
% 2.42/1.36  %Background operators:
% 2.42/1.36  
% 2.42/1.36  
% 2.42/1.36  %Foreground operators:
% 2.42/1.36  tff(k5_relset_1, type, k5_relset_1: ($i * $i * $i * $i) > $i).
% 2.42/1.36  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.42/1.36  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.42/1.36  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.42/1.36  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.42/1.36  tff('#skF_2', type, '#skF_2': $i).
% 2.42/1.36  tff('#skF_3', type, '#skF_3': $i).
% 2.42/1.36  tff('#skF_1', type, '#skF_1': $i).
% 2.42/1.36  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.42/1.36  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.42/1.36  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.42/1.36  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.42/1.36  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.42/1.36  tff('#skF_4', type, '#skF_4': $i).
% 2.42/1.36  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.42/1.36  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.42/1.36  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.42/1.36  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.42/1.36  
% 2.71/1.38  tff(f_83, negated_conjecture, ~(![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, C))) => m1_subset_1(k5_relset_1(A, C, D, B), k1_zfmisc_1(k2_zfmisc_1(B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t33_relset_1)).
% 2.71/1.38  tff(f_54, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.71/1.38  tff(f_46, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k7_relat_1(B, A)), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t87_relat_1)).
% 2.71/1.38  tff(f_50, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k7_relat_1(B, A), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t88_relat_1)).
% 2.71/1.38  tff(f_78, axiom, (![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C))) => (r1_tarski(A, D) => m1_subset_1(A, k1_zfmisc_1(k2_zfmisc_1(B, C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_relset_1)).
% 2.71/1.38  tff(f_60, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.71/1.38  tff(f_29, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 2.71/1.38  tff(f_36, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.71/1.38  tff(f_72, axiom, (![A, B, C]: (v1_relat_1(C) => ((r1_tarski(k1_relat_1(C), A) & r1_tarski(k2_relat_1(C), B)) => m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_relset_1)).
% 2.71/1.38  tff(f_64, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k5_relset_1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k5_relset_1)).
% 2.71/1.38  tff(f_42, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 2.71/1.38  tff(c_30, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.71/1.38  tff(c_42, plain, (![C_35, A_36, B_37]: (v1_relat_1(C_35) | ~m1_subset_1(C_35, k1_zfmisc_1(k2_zfmisc_1(A_36, B_37))))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.71/1.38  tff(c_51, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_30, c_42])).
% 2.71/1.38  tff(c_12, plain, (![B_9, A_8]: (r1_tarski(k1_relat_1(k7_relat_1(B_9, A_8)), A_8) | ~v1_relat_1(B_9))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.71/1.38  tff(c_14, plain, (![B_11, A_10]: (r1_tarski(k7_relat_1(B_11, A_10), B_11) | ~v1_relat_1(B_11))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.71/1.38  tff(c_201, plain, (![A_78, B_79, C_80, D_81]: (m1_subset_1(A_78, k1_zfmisc_1(k2_zfmisc_1(B_79, C_80))) | ~r1_tarski(A_78, D_81) | ~m1_subset_1(D_81, k1_zfmisc_1(k2_zfmisc_1(B_79, C_80))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.71/1.38  tff(c_333, plain, (![B_125, A_126, B_127, C_128]: (m1_subset_1(k7_relat_1(B_125, A_126), k1_zfmisc_1(k2_zfmisc_1(B_127, C_128))) | ~m1_subset_1(B_125, k1_zfmisc_1(k2_zfmisc_1(B_127, C_128))) | ~v1_relat_1(B_125))), inference(resolution, [status(thm)], [c_14, c_201])).
% 2.71/1.38  tff(c_18, plain, (![C_17, B_16, A_15]: (v5_relat_1(C_17, B_16) | ~m1_subset_1(C_17, k1_zfmisc_1(k2_zfmisc_1(A_15, B_16))))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.71/1.38  tff(c_492, plain, (![B_155, A_156, C_157, B_158]: (v5_relat_1(k7_relat_1(B_155, A_156), C_157) | ~m1_subset_1(B_155, k1_zfmisc_1(k2_zfmisc_1(B_158, C_157))) | ~v1_relat_1(B_155))), inference(resolution, [status(thm)], [c_333, c_18])).
% 2.71/1.38  tff(c_503, plain, (![A_156]: (v5_relat_1(k7_relat_1('#skF_4', A_156), '#skF_3') | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_30, c_492])).
% 2.71/1.38  tff(c_510, plain, (![A_156]: (v5_relat_1(k7_relat_1('#skF_4', A_156), '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_51, c_503])).
% 2.71/1.38  tff(c_4, plain, (![A_1, B_2]: (m1_subset_1(A_1, k1_zfmisc_1(B_2)) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.71/1.38  tff(c_63, plain, (![B_41, A_42]: (v1_relat_1(B_41) | ~m1_subset_1(B_41, k1_zfmisc_1(A_42)) | ~v1_relat_1(A_42))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.71/1.38  tff(c_77, plain, (![A_43, B_44]: (v1_relat_1(A_43) | ~v1_relat_1(B_44) | ~r1_tarski(A_43, B_44))), inference(resolution, [status(thm)], [c_4, c_63])).
% 2.71/1.38  tff(c_86, plain, (![B_11, A_10]: (v1_relat_1(k7_relat_1(B_11, A_10)) | ~v1_relat_1(B_11))), inference(resolution, [status(thm)], [c_14, c_77])).
% 2.71/1.38  tff(c_222, plain, (![C_87, A_88, B_89]: (m1_subset_1(C_87, k1_zfmisc_1(k2_zfmisc_1(A_88, B_89))) | ~r1_tarski(k2_relat_1(C_87), B_89) | ~r1_tarski(k1_relat_1(C_87), A_88) | ~v1_relat_1(C_87))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.71/1.38  tff(c_178, plain, (![A_73, B_74, C_75, D_76]: (k5_relset_1(A_73, B_74, C_75, D_76)=k7_relat_1(C_75, D_76) | ~m1_subset_1(C_75, k1_zfmisc_1(k2_zfmisc_1(A_73, B_74))))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.71/1.38  tff(c_185, plain, (![D_76]: (k5_relset_1('#skF_1', '#skF_3', '#skF_4', D_76)=k7_relat_1('#skF_4', D_76))), inference(resolution, [status(thm)], [c_30, c_178])).
% 2.71/1.38  tff(c_28, plain, (~m1_subset_1(k5_relset_1('#skF_1', '#skF_3', '#skF_4', '#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.71/1.38  tff(c_187, plain, (~m1_subset_1(k7_relat_1('#skF_4', '#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_185, c_28])).
% 2.71/1.38  tff(c_243, plain, (~r1_tarski(k2_relat_1(k7_relat_1('#skF_4', '#skF_2')), '#skF_3') | ~r1_tarski(k1_relat_1(k7_relat_1('#skF_4', '#skF_2')), '#skF_2') | ~v1_relat_1(k7_relat_1('#skF_4', '#skF_2'))), inference(resolution, [status(thm)], [c_222, c_187])).
% 2.71/1.38  tff(c_363, plain, (~v1_relat_1(k7_relat_1('#skF_4', '#skF_2'))), inference(splitLeft, [status(thm)], [c_243])).
% 2.71/1.38  tff(c_366, plain, (~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_86, c_363])).
% 2.71/1.38  tff(c_370, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_51, c_366])).
% 2.71/1.38  tff(c_372, plain, (v1_relat_1(k7_relat_1('#skF_4', '#skF_2'))), inference(splitRight, [status(thm)], [c_243])).
% 2.71/1.38  tff(c_10, plain, (![B_7, A_6]: (r1_tarski(k2_relat_1(B_7), A_6) | ~v5_relat_1(B_7, A_6) | ~v1_relat_1(B_7))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.71/1.38  tff(c_371, plain, (~r1_tarski(k1_relat_1(k7_relat_1('#skF_4', '#skF_2')), '#skF_2') | ~r1_tarski(k2_relat_1(k7_relat_1('#skF_4', '#skF_2')), '#skF_3')), inference(splitRight, [status(thm)], [c_243])).
% 2.71/1.38  tff(c_408, plain, (~r1_tarski(k2_relat_1(k7_relat_1('#skF_4', '#skF_2')), '#skF_3')), inference(splitLeft, [status(thm)], [c_371])).
% 2.71/1.38  tff(c_411, plain, (~v5_relat_1(k7_relat_1('#skF_4', '#skF_2'), '#skF_3') | ~v1_relat_1(k7_relat_1('#skF_4', '#skF_2'))), inference(resolution, [status(thm)], [c_10, c_408])).
% 2.71/1.38  tff(c_414, plain, (~v5_relat_1(k7_relat_1('#skF_4', '#skF_2'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_372, c_411])).
% 2.71/1.38  tff(c_513, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_510, c_414])).
% 2.71/1.38  tff(c_514, plain, (~r1_tarski(k1_relat_1(k7_relat_1('#skF_4', '#skF_2')), '#skF_2')), inference(splitRight, [status(thm)], [c_371])).
% 2.71/1.38  tff(c_518, plain, (~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_12, c_514])).
% 2.71/1.38  tff(c_522, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_51, c_518])).
% 2.71/1.38  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.71/1.38  
% 2.71/1.38  Inference rules
% 2.71/1.38  ----------------------
% 2.71/1.38  #Ref     : 0
% 2.71/1.38  #Sup     : 105
% 2.71/1.38  #Fact    : 0
% 2.71/1.38  #Define  : 0
% 2.71/1.38  #Split   : 5
% 2.71/1.38  #Chain   : 0
% 2.71/1.38  #Close   : 0
% 2.71/1.38  
% 2.71/1.38  Ordering : KBO
% 2.71/1.38  
% 2.71/1.38  Simplification rules
% 2.71/1.38  ----------------------
% 2.71/1.38  #Subsume      : 7
% 2.71/1.38  #Demod        : 19
% 2.71/1.38  #Tautology    : 13
% 2.71/1.38  #SimpNegUnit  : 0
% 2.71/1.38  #BackRed      : 3
% 2.71/1.38  
% 2.71/1.38  #Partial instantiations: 0
% 2.71/1.38  #Strategies tried      : 1
% 2.71/1.38  
% 2.71/1.38  Timing (in seconds)
% 2.71/1.38  ----------------------
% 2.71/1.38  Preprocessing        : 0.31
% 2.71/1.38  Parsing              : 0.17
% 2.71/1.38  CNF conversion       : 0.02
% 2.71/1.38  Main loop            : 0.31
% 2.71/1.38  Inferencing          : 0.12
% 2.71/1.38  Reduction            : 0.08
% 2.71/1.38  Demodulation         : 0.05
% 2.71/1.38  BG Simplification    : 0.02
% 2.71/1.38  Subsumption          : 0.06
% 2.71/1.38  Abstraction          : 0.02
% 2.71/1.38  MUC search           : 0.00
% 2.71/1.38  Cooper               : 0.00
% 2.71/1.38  Total                : 0.65
% 2.71/1.38  Index Insertion      : 0.00
% 2.71/1.38  Index Deletion       : 0.00
% 2.71/1.38  Index Matching       : 0.00
% 2.71/1.38  BG Taut test         : 0.00
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:07:55 EST 2020

% Result     : Theorem 2.54s
% Output     : CNFRefutation 2.83s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 129 expanded)
%              Number of leaves         :   40 (  59 expanded)
%              Depth                    :   10
%              Number of atoms          :  110 ( 193 expanded)
%              Number of equality atoms :   45 (  72 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k8_relset_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k8_relset_1,type,(
    k8_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

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

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

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

tff(f_40,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_100,negated_conjecture,(
    ~ ! [A,B,C] :
        ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
       => ( k7_relset_1(A,B,C,A) = k2_relset_1(A,B,C)
          & k8_relset_1(A,B,C,B) = k1_relset_1(A,B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_relset_1)).

tff(f_36,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_85,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_77,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k2_relset_1(A,B,C),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_relset_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_67,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k2_relat_1(B),A)
       => k5_relat_1(B,k6_relat_1(A)) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_relat_1)).

tff(f_38,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_61,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_51,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k1_relat_1(k5_relat_1(A,B)) = k10_relat_1(A,k1_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t182_relat_1)).

tff(f_93,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(f_81,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_73,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_89,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(c_10,plain,(
    ! [A_7,B_8] : v1_relat_1(k2_zfmisc_1(A_7,B_8)) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_40,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_71,plain,(
    ! [B_48,A_49] :
      ( v1_relat_1(B_48)
      | ~ m1_subset_1(B_48,k1_zfmisc_1(A_49))
      | ~ v1_relat_1(A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_77,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_40,c_71])).

tff(c_81,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_77])).

tff(c_494,plain,(
    ! [A_128,B_129,C_130] :
      ( k2_relset_1(A_128,B_129,C_130) = k2_relat_1(C_130)
      | ~ m1_subset_1(C_130,k1_zfmisc_1(k2_zfmisc_1(A_128,B_129))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_503,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_40,c_494])).

tff(c_606,plain,(
    ! [A_145,B_146,C_147] :
      ( m1_subset_1(k2_relset_1(A_145,B_146,C_147),k1_zfmisc_1(B_146))
      | ~ m1_subset_1(C_147,k1_zfmisc_1(k2_zfmisc_1(A_145,B_146))) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_631,plain,
    ( m1_subset_1(k2_relat_1('#skF_3'),k1_zfmisc_1('#skF_2'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_503,c_606])).

tff(c_639,plain,(
    m1_subset_1(k2_relat_1('#skF_3'),k1_zfmisc_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_631])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( r1_tarski(A_1,B_2)
      | ~ m1_subset_1(A_1,k1_zfmisc_1(B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_647,plain,(
    r1_tarski(k2_relat_1('#skF_3'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_639,c_2])).

tff(c_22,plain,(
    ! [B_18,A_17] :
      ( k5_relat_1(B_18,k6_relat_1(A_17)) = B_18
      | ~ r1_tarski(k2_relat_1(B_18),A_17)
      | ~ v1_relat_1(B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_650,plain,
    ( k5_relat_1('#skF_3',k6_relat_1('#skF_2')) = '#skF_3'
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_647,c_22])).

tff(c_656,plain,(
    k5_relat_1('#skF_3',k6_relat_1('#skF_2')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_650])).

tff(c_8,plain,(
    ! [A_6] : v1_relat_1(k6_relat_1(A_6)) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_18,plain,(
    ! [A_16] : k1_relat_1(k6_relat_1(A_16)) = A_16 ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_513,plain,(
    ! [A_131,B_132] :
      ( k10_relat_1(A_131,k1_relat_1(B_132)) = k1_relat_1(k5_relat_1(A_131,B_132))
      | ~ v1_relat_1(B_132)
      | ~ v1_relat_1(A_131) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_522,plain,(
    ! [A_131,A_16] :
      ( k1_relat_1(k5_relat_1(A_131,k6_relat_1(A_16))) = k10_relat_1(A_131,A_16)
      | ~ v1_relat_1(k6_relat_1(A_16))
      | ~ v1_relat_1(A_131) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_513])).

tff(c_526,plain,(
    ! [A_131,A_16] :
      ( k1_relat_1(k5_relat_1(A_131,k6_relat_1(A_16))) = k10_relat_1(A_131,A_16)
      | ~ v1_relat_1(A_131) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_522])).

tff(c_662,plain,
    ( k10_relat_1('#skF_3','#skF_2') = k1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_656,c_526])).

tff(c_666,plain,(
    k10_relat_1('#skF_3','#skF_2') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_662])).

tff(c_715,plain,(
    ! [A_154,B_155,C_156,D_157] :
      ( k8_relset_1(A_154,B_155,C_156,D_157) = k10_relat_1(C_156,D_157)
      | ~ m1_subset_1(C_156,k1_zfmisc_1(k2_zfmisc_1(A_154,B_155))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_726,plain,(
    ! [D_157] : k8_relset_1('#skF_1','#skF_2','#skF_3',D_157) = k10_relat_1('#skF_3',D_157) ),
    inference(resolution,[status(thm)],[c_40,c_715])).

tff(c_479,plain,(
    ! [A_125,B_126,C_127] :
      ( k1_relset_1(A_125,B_126,C_127) = k1_relat_1(C_127)
      | ~ m1_subset_1(C_127,k1_zfmisc_1(k2_zfmisc_1(A_125,B_126))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_488,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_40,c_479])).

tff(c_110,plain,(
    ! [C_59,A_60,B_61] :
      ( v4_relat_1(C_59,A_60)
      | ~ m1_subset_1(C_59,k1_zfmisc_1(k2_zfmisc_1(A_60,B_61))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_119,plain,(
    v4_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_40,c_110])).

tff(c_16,plain,(
    ! [B_15,A_14] :
      ( k7_relat_1(B_15,A_14) = B_15
      | ~ v4_relat_1(B_15,A_14)
      | ~ v1_relat_1(B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_122,plain,
    ( k7_relat_1('#skF_3','#skF_1') = '#skF_3'
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_119,c_16])).

tff(c_125,plain,(
    k7_relat_1('#skF_3','#skF_1') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_122])).

tff(c_12,plain,(
    ! [B_10,A_9] :
      ( k2_relat_1(k7_relat_1(B_10,A_9)) = k9_relat_1(B_10,A_9)
      | ~ v1_relat_1(B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_129,plain,
    ( k9_relat_1('#skF_3','#skF_1') = k2_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_125,c_12])).

tff(c_133,plain,(
    k9_relat_1('#skF_3','#skF_1') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_129])).

tff(c_371,plain,(
    ! [A_99,B_100,C_101,D_102] :
      ( k7_relset_1(A_99,B_100,C_101,D_102) = k9_relat_1(C_101,D_102)
      | ~ m1_subset_1(C_101,k1_zfmisc_1(k2_zfmisc_1(A_99,B_100))) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_382,plain,(
    ! [D_102] : k7_relset_1('#skF_1','#skF_2','#skF_3',D_102) = k9_relat_1('#skF_3',D_102) ),
    inference(resolution,[status(thm)],[c_40,c_371])).

tff(c_203,plain,(
    ! [A_80,B_81,C_82] :
      ( k2_relset_1(A_80,B_81,C_82) = k2_relat_1(C_82)
      | ~ m1_subset_1(C_82,k1_zfmisc_1(k2_zfmisc_1(A_80,B_81))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_212,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_40,c_203])).

tff(c_38,plain,
    ( k8_relset_1('#skF_1','#skF_2','#skF_3','#skF_2') != k1_relset_1('#skF_1','#skF_2','#skF_3')
    | k7_relset_1('#skF_1','#skF_2','#skF_3','#skF_1') != k2_relset_1('#skF_1','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_82,plain,(
    k7_relset_1('#skF_1','#skF_2','#skF_3','#skF_1') != k2_relset_1('#skF_1','#skF_2','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_38])).

tff(c_213,plain,(
    k7_relset_1('#skF_1','#skF_2','#skF_3','#skF_1') != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_212,c_82])).

tff(c_383,plain,(
    k9_relat_1('#skF_3','#skF_1') != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_382,c_213])).

tff(c_386,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_133,c_383])).

tff(c_387,plain,(
    k8_relset_1('#skF_1','#skF_2','#skF_3','#skF_2') != k1_relset_1('#skF_1','#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_489,plain,(
    k8_relset_1('#skF_1','#skF_2','#skF_3','#skF_2') != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_488,c_387])).

tff(c_727,plain,(
    k10_relat_1('#skF_3','#skF_2') != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_726,c_489])).

tff(c_730,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_666,c_727])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n025.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:06:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.54/1.45  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.82/1.46  
% 2.82/1.46  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.83/1.46  %$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k8_relset_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 2.83/1.46  
% 2.83/1.46  %Foreground sorts:
% 2.83/1.46  
% 2.83/1.46  
% 2.83/1.46  %Background operators:
% 2.83/1.46  
% 2.83/1.46  
% 2.83/1.46  %Foreground operators:
% 2.83/1.46  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.83/1.46  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.83/1.46  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.83/1.46  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 2.83/1.46  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.83/1.46  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.83/1.46  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.83/1.46  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 2.83/1.46  tff('#skF_2', type, '#skF_2': $i).
% 2.83/1.46  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.83/1.46  tff('#skF_3', type, '#skF_3': $i).
% 2.83/1.46  tff('#skF_1', type, '#skF_1': $i).
% 2.83/1.46  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.83/1.46  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.83/1.46  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.83/1.46  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.83/1.46  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.83/1.46  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.83/1.46  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.83/1.46  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.83/1.46  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.83/1.46  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.83/1.46  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.83/1.46  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.83/1.46  
% 2.83/1.48  tff(f_40, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.83/1.48  tff(f_100, negated_conjecture, ~(![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((k7_relset_1(A, B, C, A) = k2_relset_1(A, B, C)) & (k8_relset_1(A, B, C, B) = k1_relset_1(A, B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_relset_1)).
% 2.83/1.48  tff(f_36, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.83/1.48  tff(f_85, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 2.83/1.48  tff(f_77, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k2_relset_1(A, B, C), k1_zfmisc_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_relset_1)).
% 2.83/1.48  tff(f_29, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 2.83/1.48  tff(f_67, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k5_relat_1(B, k6_relat_1(A)) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_relat_1)).
% 2.83/1.48  tff(f_38, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 2.83/1.48  tff(f_61, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 2.83/1.48  tff(f_51, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k1_relat_1(k5_relat_1(A, B)) = k10_relat_1(A, k1_relat_1(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t182_relat_1)).
% 2.83/1.48  tff(f_93, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 2.83/1.48  tff(f_81, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.83/1.48  tff(f_73, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.83/1.48  tff(f_57, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t209_relat_1)).
% 2.83/1.48  tff(f_44, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 2.83/1.48  tff(f_89, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 2.83/1.48  tff(c_10, plain, (![A_7, B_8]: (v1_relat_1(k2_zfmisc_1(A_7, B_8)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.83/1.48  tff(c_40, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.83/1.48  tff(c_71, plain, (![B_48, A_49]: (v1_relat_1(B_48) | ~m1_subset_1(B_48, k1_zfmisc_1(A_49)) | ~v1_relat_1(A_49))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.83/1.48  tff(c_77, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_40, c_71])).
% 2.83/1.48  tff(c_81, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_10, c_77])).
% 2.83/1.48  tff(c_494, plain, (![A_128, B_129, C_130]: (k2_relset_1(A_128, B_129, C_130)=k2_relat_1(C_130) | ~m1_subset_1(C_130, k1_zfmisc_1(k2_zfmisc_1(A_128, B_129))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.83/1.48  tff(c_503, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_40, c_494])).
% 2.83/1.48  tff(c_606, plain, (![A_145, B_146, C_147]: (m1_subset_1(k2_relset_1(A_145, B_146, C_147), k1_zfmisc_1(B_146)) | ~m1_subset_1(C_147, k1_zfmisc_1(k2_zfmisc_1(A_145, B_146))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.83/1.48  tff(c_631, plain, (m1_subset_1(k2_relat_1('#skF_3'), k1_zfmisc_1('#skF_2')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_503, c_606])).
% 2.83/1.48  tff(c_639, plain, (m1_subset_1(k2_relat_1('#skF_3'), k1_zfmisc_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_631])).
% 2.83/1.48  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(A_1, B_2) | ~m1_subset_1(A_1, k1_zfmisc_1(B_2)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.83/1.48  tff(c_647, plain, (r1_tarski(k2_relat_1('#skF_3'), '#skF_2')), inference(resolution, [status(thm)], [c_639, c_2])).
% 2.83/1.48  tff(c_22, plain, (![B_18, A_17]: (k5_relat_1(B_18, k6_relat_1(A_17))=B_18 | ~r1_tarski(k2_relat_1(B_18), A_17) | ~v1_relat_1(B_18))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.83/1.48  tff(c_650, plain, (k5_relat_1('#skF_3', k6_relat_1('#skF_2'))='#skF_3' | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_647, c_22])).
% 2.83/1.48  tff(c_656, plain, (k5_relat_1('#skF_3', k6_relat_1('#skF_2'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_81, c_650])).
% 2.83/1.48  tff(c_8, plain, (![A_6]: (v1_relat_1(k6_relat_1(A_6)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.83/1.48  tff(c_18, plain, (![A_16]: (k1_relat_1(k6_relat_1(A_16))=A_16)), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.83/1.48  tff(c_513, plain, (![A_131, B_132]: (k10_relat_1(A_131, k1_relat_1(B_132))=k1_relat_1(k5_relat_1(A_131, B_132)) | ~v1_relat_1(B_132) | ~v1_relat_1(A_131))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.83/1.48  tff(c_522, plain, (![A_131, A_16]: (k1_relat_1(k5_relat_1(A_131, k6_relat_1(A_16)))=k10_relat_1(A_131, A_16) | ~v1_relat_1(k6_relat_1(A_16)) | ~v1_relat_1(A_131))), inference(superposition, [status(thm), theory('equality')], [c_18, c_513])).
% 2.83/1.48  tff(c_526, plain, (![A_131, A_16]: (k1_relat_1(k5_relat_1(A_131, k6_relat_1(A_16)))=k10_relat_1(A_131, A_16) | ~v1_relat_1(A_131))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_522])).
% 2.83/1.48  tff(c_662, plain, (k10_relat_1('#skF_3', '#skF_2')=k1_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_656, c_526])).
% 2.83/1.48  tff(c_666, plain, (k10_relat_1('#skF_3', '#skF_2')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_81, c_662])).
% 2.83/1.48  tff(c_715, plain, (![A_154, B_155, C_156, D_157]: (k8_relset_1(A_154, B_155, C_156, D_157)=k10_relat_1(C_156, D_157) | ~m1_subset_1(C_156, k1_zfmisc_1(k2_zfmisc_1(A_154, B_155))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.83/1.48  tff(c_726, plain, (![D_157]: (k8_relset_1('#skF_1', '#skF_2', '#skF_3', D_157)=k10_relat_1('#skF_3', D_157))), inference(resolution, [status(thm)], [c_40, c_715])).
% 2.83/1.48  tff(c_479, plain, (![A_125, B_126, C_127]: (k1_relset_1(A_125, B_126, C_127)=k1_relat_1(C_127) | ~m1_subset_1(C_127, k1_zfmisc_1(k2_zfmisc_1(A_125, B_126))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.83/1.48  tff(c_488, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_40, c_479])).
% 2.83/1.48  tff(c_110, plain, (![C_59, A_60, B_61]: (v4_relat_1(C_59, A_60) | ~m1_subset_1(C_59, k1_zfmisc_1(k2_zfmisc_1(A_60, B_61))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.83/1.48  tff(c_119, plain, (v4_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_40, c_110])).
% 2.83/1.48  tff(c_16, plain, (![B_15, A_14]: (k7_relat_1(B_15, A_14)=B_15 | ~v4_relat_1(B_15, A_14) | ~v1_relat_1(B_15))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.83/1.48  tff(c_122, plain, (k7_relat_1('#skF_3', '#skF_1')='#skF_3' | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_119, c_16])).
% 2.83/1.48  tff(c_125, plain, (k7_relat_1('#skF_3', '#skF_1')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_81, c_122])).
% 2.83/1.48  tff(c_12, plain, (![B_10, A_9]: (k2_relat_1(k7_relat_1(B_10, A_9))=k9_relat_1(B_10, A_9) | ~v1_relat_1(B_10))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.83/1.48  tff(c_129, plain, (k9_relat_1('#skF_3', '#skF_1')=k2_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_125, c_12])).
% 2.83/1.48  tff(c_133, plain, (k9_relat_1('#skF_3', '#skF_1')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_81, c_129])).
% 2.83/1.48  tff(c_371, plain, (![A_99, B_100, C_101, D_102]: (k7_relset_1(A_99, B_100, C_101, D_102)=k9_relat_1(C_101, D_102) | ~m1_subset_1(C_101, k1_zfmisc_1(k2_zfmisc_1(A_99, B_100))))), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.83/1.48  tff(c_382, plain, (![D_102]: (k7_relset_1('#skF_1', '#skF_2', '#skF_3', D_102)=k9_relat_1('#skF_3', D_102))), inference(resolution, [status(thm)], [c_40, c_371])).
% 2.83/1.48  tff(c_203, plain, (![A_80, B_81, C_82]: (k2_relset_1(A_80, B_81, C_82)=k2_relat_1(C_82) | ~m1_subset_1(C_82, k1_zfmisc_1(k2_zfmisc_1(A_80, B_81))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.83/1.48  tff(c_212, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_40, c_203])).
% 2.83/1.48  tff(c_38, plain, (k8_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_2')!=k1_relset_1('#skF_1', '#skF_2', '#skF_3') | k7_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_1')!=k2_relset_1('#skF_1', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.83/1.48  tff(c_82, plain, (k7_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_1')!=k2_relset_1('#skF_1', '#skF_2', '#skF_3')), inference(splitLeft, [status(thm)], [c_38])).
% 2.83/1.48  tff(c_213, plain, (k7_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_1')!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_212, c_82])).
% 2.83/1.48  tff(c_383, plain, (k9_relat_1('#skF_3', '#skF_1')!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_382, c_213])).
% 2.83/1.48  tff(c_386, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_133, c_383])).
% 2.83/1.48  tff(c_387, plain, (k8_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_2')!=k1_relset_1('#skF_1', '#skF_2', '#skF_3')), inference(splitRight, [status(thm)], [c_38])).
% 2.83/1.48  tff(c_489, plain, (k8_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_2')!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_488, c_387])).
% 2.83/1.48  tff(c_727, plain, (k10_relat_1('#skF_3', '#skF_2')!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_726, c_489])).
% 2.83/1.48  tff(c_730, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_666, c_727])).
% 2.83/1.48  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.83/1.48  
% 2.83/1.48  Inference rules
% 2.83/1.48  ----------------------
% 2.83/1.48  #Ref     : 0
% 2.83/1.48  #Sup     : 154
% 2.83/1.48  #Fact    : 0
% 2.83/1.48  #Define  : 0
% 2.83/1.48  #Split   : 3
% 2.83/1.48  #Chain   : 0
% 2.83/1.48  #Close   : 0
% 2.83/1.48  
% 2.83/1.48  Ordering : KBO
% 2.83/1.48  
% 2.83/1.48  Simplification rules
% 2.83/1.48  ----------------------
% 2.83/1.48  #Subsume      : 4
% 2.83/1.48  #Demod        : 59
% 2.83/1.48  #Tautology    : 70
% 2.83/1.48  #SimpNegUnit  : 0
% 2.83/1.48  #BackRed      : 5
% 2.83/1.48  
% 2.83/1.48  #Partial instantiations: 0
% 2.83/1.48  #Strategies tried      : 1
% 2.83/1.48  
% 2.83/1.48  Timing (in seconds)
% 2.83/1.48  ----------------------
% 2.83/1.48  Preprocessing        : 0.32
% 2.83/1.48  Parsing              : 0.18
% 2.83/1.48  CNF conversion       : 0.02
% 2.83/1.48  Main loop            : 0.31
% 2.83/1.48  Inferencing          : 0.13
% 2.83/1.48  Reduction            : 0.09
% 2.83/1.48  Demodulation         : 0.06
% 2.83/1.48  BG Simplification    : 0.02
% 2.83/1.48  Subsumption          : 0.04
% 2.83/1.48  Abstraction          : 0.02
% 2.83/1.48  MUC search           : 0.00
% 2.83/1.48  Cooper               : 0.00
% 2.83/1.48  Total                : 0.67
% 2.83/1.48  Index Insertion      : 0.00
% 2.83/1.48  Index Deletion       : 0.00
% 2.83/1.48  Index Matching       : 0.00
% 2.83/1.48  BG Taut test         : 0.00
%------------------------------------------------------------------------------
